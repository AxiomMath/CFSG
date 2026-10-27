module

public import Certificates.Data.Kernel.M24G.Syl
public import Certificates.Kernel.M24G.SylData
public import Certificates.Kernel.M24G.SextData
public import Certificates.Kernel.M24G.TSData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.SylC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G

set_option maxHeartbeats 0 in
theorem s0Fix_ok : sylS0FixOn Native.s0Tabs = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem triple_ok : replayOK Native.keyTriple sylTripleSteps (0, 8, 16) 1100 SylD.tL SylD.tPar
    SylD.tGen (posTree Native.keyTriple SylD.tL) = true := by
  decide +kernel

theorem tripleLen_ok : SylD.tL.length = 1024 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem tripleValid_ok : SylD.tL.all Native.validTriple = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem tuple_ok : replayOK Native.keyOSP sylOSPSteps Native.tup0 200 SylD.uL SylD.uPar SylD.uGen
    (posTree Native.keyOSP SylD.uL) = true := by
  decide +kernel

theorem tupleLen_ok : SylD.uL.length = 63 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem tupleValid_ok : SylD.uL.all Native.validOSP = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem fixed_ok : sylFixedOn sylS0BT = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cls_ok : sylClsF SL = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem trioDet_ok : sylTrioDetF TS = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem v0_ok : sylV0F SL TS = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem span_ok : sylSpanOn (sylClsMask SL) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem space_ok : replayOK Native.keySp sylSpSteps Native.vpList 2928 SylD.vL SylD.vPar SylD.vGen
    (posTree Native.keySp SylD.vL) = true := by
  decide +kernel

theorem spaceLen_ok : SylD.vL.length = 3796 := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem spaceValid_ok : SylD.vL.all Native.validSp = true := by
  decide +kernel

end CFSG.KC.M24G.SylC
