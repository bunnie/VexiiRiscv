// generation notes: --with-rvZb removed

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
    if(topology.readsAsync.exists(_.readUnderWrite != writeFirst) || (topology.mem.wordCount * topology.mem.width) < 512)
      return false
    return true
  }

  override def onUnblackboxable(topology: MemTopology, who: Any, message: String): Unit = {}
}

object GenLitex extends App {
  val param = new ParamSimple()
  val sc = BunSpinalConfig // .addStandardMemBlackboxing(blackboxSyncOnly)
  val regions = ArrayBuffer[PmaRegion]()
  val analysis = new AnalysisUtils
  var reportModel = false

  assert(new scopt.OptionParser[Unit]("VexiiRiscvLitex") {
    help("help").text("prints this usage text")
    opt[Unit]("report-model") action { (v, c) => reportModel = true }
    param.addOptions(this)
    analysis.addOption(this)
    ParamSimple.addOptionRegion(this, regions)
  }.parse(args, ()).nonEmpty)

  if (regions.isEmpty) regions ++= ParamSimple.defaultPma

  val report = sc.generateSystemVerilog {
    val plugins = param.plugins()
    ParamSimple.setPma(plugins, regions)
    VexiiRiscv(plugins)
  }

  analysis.report(report)

  if (reportModel) {
    misc.Reporter.model(report.toplevel)
  }
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
      pc.walkComponents {
        case c: Ram_1w_1rs => {
          val awidth = c.rdAddressWidth
          val bwidth = c.wrAddressWidth
          val adata_width = c.rdDataWidth
          val bdata_width = c.wrDataWidth
          val topPatch = pc.topLevel rework new Area {
            // println(f"rd ${c.rdDataWidth}, wd ${c.wrDataWidth}, ra ${c.rdAddressWidth}, wa ${c.wrAddressWidth}")
            setName(c.getPath("_"))
            val stov, emasa, tena, tcena, tenb, tcenb, sea, dftrambyp, seb, ret1n = in Bool()
            val emaa = in UInt (3 bits)
            val emab = in UInt (3 bits)
            val taa = in UInt (awidth bits)
            val wenb = in UInt (bdata_width bits)
            val twenb = in UInt (bdata_width bits)
            val tab = in UInt (bwidth bits)
            val tdb = in UInt (bdata_width bits)
            val sia = in UInt (2 bits)
            val sib = in UInt (2 bits)
          }
          c.rework {
            topPatch.stov.pull(propagateName = true).unsetName().setName("stov")
            topPatch.emasa.pull(propagateName = true).unsetName().setName("emasa")
            topPatch.tena.pull(propagateName = true).unsetName().setName("tena")
            topPatch.tcena.pull(propagateName = true).unsetName().setName("tcena")
            topPatch.tenb.pull(propagateName = true).unsetName().setName("tenb")
            topPatch.tcenb.pull(propagateName = true).unsetName().setName("tcenb")
            topPatch.sea.pull(propagateName = true).unsetName().setName("sea")
            topPatch.dftrambyp.pull(propagateName = true).unsetName().setName("dftrambyp")
            topPatch.seb.pull(propagateName = true).unsetName().setName("seb")
            topPatch.ret1n.pull(propagateName = true).unsetName().setName("ret1n")
            topPatch.emaa.pull(propagateName = true).unsetName().setName("emaa")
            topPatch.emab.pull(propagateName = true).unsetName().setName("emab")
            topPatch.taa.pull(propagateName = true).unsetName().setName("taa")
            topPatch.wenb.pull(propagateName = true).unsetName().setName("wenb")
            topPatch.twenb.pull(propagateName = true).unsetName().setName("twenb")
            topPatch.tab.pull(propagateName = true).unsetName().setName("tab")
            topPatch.tdb.pull(propagateName = true).unsetName().setName("tdb")
            topPatch.sia.pull(propagateName = true).unsetName().setName("sia")
            topPatch.sib.pull(propagateName = true).unsetName().setName("sib")
          }
          val blackboxed_outputs = c rework new AreaRoot {
            val cenya, cenyb = out Bool()
            val soa = out UInt (2 bits)
            val sob = out UInt (2 bits)
            val wenyb = out UInt (adata_width bits)
            val aya = out UInt (awidth bits)
            val ayb = out UInt (bwidth bits)
          }
          pc.topLevel rework new Area {
            setName(c.getPath("_"))
            val cenya, cenyb = out Bool()
            val soa = out UInt (2 bits)
            val sob = out UInt (2 bits)
            val wenyb = out UInt (adata_width bits)
            val aya = out UInt (awidth bits)
            val ayb = out UInt (bwidth bits)

            cenya := blackboxed_outputs.cenya.pull(propagateName = true)
            cenyb := blackboxed_outputs.cenyb.pull(propagateName = true)
            soa := blackboxed_outputs.soa.pull(propagateName = true)
            sob := blackboxed_outputs.sob.pull(propagateName = true)
            wenyb := blackboxed_outputs.wenyb.pull(propagateName = true)
            aya := blackboxed_outputs.aya.pull(propagateName = true)
            ayb := blackboxed_outputs.ayb.pull(propagateName = true)
          }
          c.addGeneric("ramname", s"RAM_DP_${c.wordCount}_${c.wordWidth}")
        }
        case _ =>
      }
    }
  }

/*
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
*/
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


// Generates VexiiRiscv verilog using command line arguments
object GenBunTl extends App {
  val param = new ParamSimple()
  val sc = BunSpinalConfig.addStandardMemBlackboxing(blackboxSyncOnly)
  val regions = ArrayBuffer[PmaRegion]()
  var tlSinkWidth = 0

  assert(new scopt.OptionParser[Unit]("VexiiRiscv") {
    help("help").text("prints this usage text")
    opt[Int]("tl-sink-width") action { (v, c) => tlSinkWidth = v }
    param.addOptions(this)
    ParamSimple.addOptionRegion(this, regions)
  }.parse(args, ()).nonEmpty)

  if(regions.isEmpty) regions ++= ParamSimple.defaultPma

  sc.memBlackBoxers += new PhaseNetlist {
    override def impl(pc: PhaseContext): Unit = {
      pc.walkComponents {
        case c: Ram_1w_1rs => {
          val awidth = c.rdAddressWidth
          val bwidth = c.wrAddressWidth
          val adata_width = c.rdDataWidth
          val bdata_width = c.wrDataWidth
          val topPatch = pc.topLevel rework new Area {
            // println(f"rd ${c.rdDataWidth}, wd ${c.wrDataWidth}, ra ${c.rdAddressWidth}, wa ${c.wrAddressWidth}")
            setName(c.getPath("_"))
            val stov, emasa, tena, tcena, tenb, tcenb, sea, dftrambyp, seb, ret1n = in Bool()
            val emaa = in UInt (3 bits)
            val emab = in UInt (3 bits)
            val taa = in UInt (awidth bits)
            val wenb = in UInt (bdata_width bits)
            val twenb = in UInt (bdata_width bits)
            val tab = in UInt (bwidth bits)
            val tdb = in UInt (bdata_width bits)
            val sia = in UInt (2 bits)
            val sib = in UInt (2 bits)
          }
          c.rework {
            topPatch.stov.pull(propagateName = true).unsetName().setName("stov")
            topPatch.emasa.pull(propagateName = true).unsetName().setName("emasa")
            topPatch.tena.pull(propagateName = true).unsetName().setName("tena")
            topPatch.tcena.pull(propagateName = true).unsetName().setName("tcena")
            topPatch.tenb.pull(propagateName = true).unsetName().setName("tenb")
            topPatch.tcenb.pull(propagateName = true).unsetName().setName("tcenb")
            topPatch.sea.pull(propagateName = true).unsetName().setName("sea")
            topPatch.dftrambyp.pull(propagateName = true).unsetName().setName("dftrambyp")
            topPatch.seb.pull(propagateName = true).unsetName().setName("seb")
            topPatch.ret1n.pull(propagateName = true).unsetName().setName("ret1n")
            topPatch.emaa.pull(propagateName = true).unsetName().setName("emaa")
            topPatch.emab.pull(propagateName = true).unsetName().setName("emab")
            topPatch.taa.pull(propagateName = true).unsetName().setName("taa")
            topPatch.wenb.pull(propagateName = true).unsetName().setName("wenb")
            topPatch.twenb.pull(propagateName = true).unsetName().setName("twenb")
            topPatch.tab.pull(propagateName = true).unsetName().setName("tab")
            topPatch.tdb.pull(propagateName = true).unsetName().setName("tdb")
            topPatch.sia.pull(propagateName = true).unsetName().setName("sia")
            topPatch.sib.pull(propagateName = true).unsetName().setName("sib")
          }
          val blackboxed_outputs = c rework new AreaRoot {
            val cenya, cenyb = out Bool()
            val soa = out UInt (2 bits)
            val sob = out UInt (2 bits)
            val wenyb = out UInt (adata_width bits)
            val aya = out UInt (awidth bits)
            val ayb = out UInt (bwidth bits)
          }
          pc.topLevel rework new Area {
            setName(c.getPath("_"))
            val cenya, cenyb = out Bool()
            val soa = out UInt (2 bits)
            val sob = out UInt (2 bits)
            val wenyb = out UInt (adata_width bits)
            val aya = out UInt (awidth bits)
            val ayb = out UInt (bwidth bits)

            cenya := blackboxed_outputs.cenya.pull(propagateName = true)
            cenyb := blackboxed_outputs.cenyb.pull(propagateName = true)
            soa := blackboxed_outputs.soa.pull(propagateName = true)
            sob := blackboxed_outputs.sob.pull(propagateName = true)
            wenyb := blackboxed_outputs.wenyb.pull(propagateName = true)
            aya := blackboxed_outputs.aya.pull(propagateName = true)
            ayb := blackboxed_outputs.ayb.pull(propagateName = true)
          }
          c.addGeneric("ramname", s"RAM_DP_${c.wordCount}_${c.wordWidth}")
        }
        case _ =>
      }
    }
  }

/*
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

  // above is superceded with command line args:
  --with-fetch-l1 --with-lsu-l1 --lsu-l1-coherency --fetch-l1-hardware-prefetch=nl
  --fetch-l1-refill-count=2 --lsu-software-prefetch --lsu-hardware-prefetch rpt
  --performance-counters 9 --regfile-async --lsu-l1-store-buffer-ops=32
  --lsu-l1-refill-count 4 --lsu-l1-writeback-count 4 --lsu-l1-store-buffer-slots=4
  --with-mul --with-div --allow-bypass-from=0 --with-lsu-bypass --with-supervisor
  --fetch-l1-ways=4 --fetch-l1-mem-data-width-min=64 --lsu-l1-ways=4 --lsu-l1-mem-data-width-min=64
  --xlen=32 --with-rvc --with-rva --with-btb --with-ras --with-gshare --with-late-alu
  --decoders=2 --lanes=2 --with-dispatcher-buffer --with-hart-id-input
  --reset-vector=0x10000 --with-whiteboxer-outputs
  --region base=3000,size=1000,main=0,exe=1 --region base=2010000,size=1000,main=0,exe=1
  --region base=1000,size=1000,main=0,exe=1 --region base=10020000,size=1000,main=0,exe=1
  --region base=2000000,size=10000,main=0,exe=1 --region base=C000000,size=4000000,main=0,exe=1
  --region base=0,size=1000,main=0,exe=1 --region base=10000,size=10000,main=0,exe=1
  --region base=100000,size=1000,main=0,exe=1 --region base=110000,size=1000,main=0,exe=1
  --region base=80000000,size=10000000,main=1,exe=1 --region base=8000000,size=10000,main=1,exe=1
  --with-boot-mem-init --tl-sink-width=4 --with-rvZb

*/
  val report = sc.generateSystemVerilog {
    val plugins = param.plugins()
    import spinal.lib.bus.tilelink._
    import spinal.lib.bus.tilelink.fabric._
    new Component {
      setDefinitionName("VexiiRiscvTilelink")
      val cpu = new TilelinkVexiiRiscvFiber(plugins)
      val mem = new SlaveBus(
        M2sSupport(
          transfers = M2sTransfers.all,
          dataWidth = param.memDataWidth,
          addressWidth = param.physicalWidth
        ),
        S2mParameters(
          List(
            S2mAgent(
              name = null,
              sinkId = SizeMapping(0, 1 << tlSinkWidth),
              emits = S2mTransfers(probe = SizeRange(0x40))
            )
          )
        )
      )

      // Custom memory mapping
      val tags = mem.node.spinalTags.filter(!_.isInstanceOf[MemoryEndpoint])
      mem.node.spinalTags.clear()
      mem.node.spinalTags ++= tags
      val virtualRegions = for (region <- regions) yield new VirtualEndpoint(mem.node, region.mapping) {
        if (region.isMain) self.addTag(PMA.MAIN)
        if (region.isExecutable) self.addTag(PMA.EXECUTABLE)
      }

      mem.node << cpu.iBus
      mem.node << cpu.dBus
      if (cpu.lsuL1Bus != null) mem.node << cpu.lsuL1Bus

      // Bind interrupts
      val mti, msi, mei = InterruptNode.master()
      cpu.priv.get.mti << mti;
      in(mti.flag)
      cpu.priv.get.msi << msi;
      in(msi.flag)
      cpu.priv.get.mei << mei;
      in(mei.flag)

      val sei = (cpu.priv.get.sei != null) generate InterruptNode.master()
      if (sei != null) cpu.priv.get.sei << sei;
      in(sei.flag)

      val patcher = Fiber patch new AreaRoot {
        val hartId = param.withHartIdInput generate plugins.collectFirst {
          case p: PrivilegedPlugin => p.api.harts(0).hartId.toIo
        }

        val memA = mem.node.bus.a
        out(memA.compliantMask()).setName(memA.mask.getName())
        memA.mask.setName(memA.mask.getName() + "_non_compliant")
        memA.mask.setAsDirectionLess()
      }
    }
  }

  for (m <- report.toplevel.mem.node.m2s.parameters.masters) {
    println(m.name)
    for (source <- m.mapping) {
      println(s"- ${source.id} ${source.emits}")
    }
  }
}