package vexiiriscv

import spinal.core._
import spinal.core.fiber.Fiber
import spinal.lib.{AnalysisUtils, LatencyAnalysis}
import spinal.lib.bus.misc.SizeMapping
import spinal.lib.bus.tilelink.{M2sTransfers, SizeRange}
import spinal.lib.misc.{InterruptNode, PathTracer}
import spinal.lib.system.tag.{MemoryEndpoint, PMA, PmaRegion, PmaRegionImpl, VirtualEndpoint}
import vexiiriscv.compat.MultiPortWritesSymplifier
import vexiiriscv.decode.{Decode, DecodePipelinePlugin}
import vexiiriscv.execute.{CsrRamPlugin, ExecuteLanePlugin, SrcPlugin}
import vexiiriscv.execute.lsu._
import vexiiriscv.fetch._
import vexiiriscv.misc.PrivilegedPlugin
import vexiiriscv.prediction.BtbPlugin
import vexiiriscv.regfile.RegFilePlugin
import vexiiriscv.soc.TilelinkVexiiRiscvFiber

import spinal.core.internals.{ExpressionContainer, PhaseAllocateNames, PhaseContext, MemTopology, PhaseNetlist}
import spinal.core.internals._

import scala.collection.mutable.ArrayBuffer

object BunSpinalConfig extends spinal.core.SpinalConfig(
  defaultConfigForClockDomains = ClockDomainConfig(
    resetKind = spinal.core.SYNC
  )
){
  //Insert a compilation phase which will add a  (* ram_style = "block" *) on all synchronous rams.
  phasesInserters += {(array) => array.insert(array.indexWhere(_.isInstanceOf[PhaseAllocateNames]) + 1, new BunSoCForceRamBlockPhase)}
}

object blackboxSyncOnly extends MemBlackboxingPolicy {
  override def translationInterest(topology: MemTopology): Boolean = {
    if(topology.readsAsync.exists(_.readUnderWrite != writeFirst))
      return false
    return true
  }

  override def onUnblackboxable(topology: MemTopology, who: Any, message: String): Unit = {}
}

// Generates VexiiRiscv verilog using command line arguments
object GenBun extends App {
  val param = new ParamSimple()
  val sc = BunSpinalConfig.addStandardMemBlackboxing(blackboxSyncOnly)
  val regions = ArrayBuffer[PmaRegion]()
  val analysis = new AnalysisUtils
  var reportModel = false

  assert(new scopt.OptionParser[Unit]("VexiiRiscv") {
    help("help").text("prints this usage text")
    opt[Unit]("report-model") action { (v, c) => reportModel = true }
    param.addOptions(this)
    analysis.addOption(this)
    ParamSimple.addOptionRegion(this, regions)
  }.parse(args, ()).nonEmpty)

  if(regions.isEmpty) regions ++= ParamSimple.defaultPma

  sc.memBlackBoxers += new PhaseNetlist {
    override def impl(pc: PhaseContext): Unit = {
      val topPatch = pc.topLevel rework new AreaRoot {
        val CMBIST, CMATPG = in Bool()
        val sramtrm = in UInt (3 bits)
      }
      pc.walkComponents {
        case c: Ram_1w_1rs => {
          c.rework {
            topPatch.CMBIST.pull(propagateName = true)
            topPatch.CMATPG.pull(propagateName = true)
            topPatch.sramtrm.pull(propagateName = true)
          }
          c.addGeneric("ramname", s"RAM_DP_${c.wordCount}_${c.wordWidth}")
        }
        case _ =>
      }
    }
  }

  // configure CPU performance features
  param.decoders = 2
  param.lanes = 2
  param.withBtb = true
  param.withGShare = true
  param.withRas = true
  param.allowBypassFrom = 0
  param.divRadix = 4
  param.withLateAlu = true
  param.withAlignerBuffer = true
  param.withDispatcherBuffer = true

  // configure Dcache
  param.lsuMemDataWidthMin = 64
  param.lsuL1Sets = 64
  param.lsuL1Ways = 4
  param.lsuL1RefillCount = 8
  param.lsuL1WritebackCount = 8
  param.lsuStoreBufferSlots = 4
  param.lsuStoreBufferOps = 32
  param.withLsuBypass = true
  param.lsuSoftwarePrefetch = true
  param.lsuHardwarePrefetch = "rpt"

  // configure MMU
  param.privParam.withSupervisor = true
  param.privParam.withUser = true
  param.withMmu = true

  // 0-cycle regfile: what does this do to Fmax?
  param.regFileSync = false

  // configure Icache
  param.fetchMemDataWidthMin = 64
  param.fetchL1Sets = 64
  param.fetchL1Ways = 4
  param.fetchL1RefillCount = 4

  // configure RV architecture features
  param.withMul = true
  param.withDiv = true
  param.withRva = true
  param.withRvc = true
  param.withRvZb = true
  param.withRvcbm = true
  param.xlen = 32

  // enable caches
  param.lsuL1Enable = true
  param.fetchL1Enable = true

  val report = sc.generateSystemVerilog {
    val plugins = param.plugins()
    ParamSimple.setPma(plugins, regions)
    VexiiRiscv(plugins)
  }

  analysis.report(report)

  if(reportModel){
    misc.Reporter.model(report.toplevel)
  }
}

class BunSoCForceRamBlockPhase() extends spinal.core.internals.Phase{
  override def impl(pc: PhaseContext): Unit = {
    pc.walkBaseNodes{
      case mem: Mem[_] => {
        var asyncRead = false
        mem.dlcForeach[MemPortStatement]{
          case _ : MemReadAsync => asyncRead = true
          case _ =>
        }
        if(!asyncRead) mem.addAttribute("ram_style", "block")
      }
      case _ =>
    }
  }
  override def hasNetlistImpact: Boolean = false
}
