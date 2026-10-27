module

public import Certificates.Data.Kernel.M24G.Duad
public import Certificates.Kernel.M24G.DuadData
public import Certificates.Kernel.M24G.SextData

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G.DuadC

open CFSG.KC.M24G CFSG.Quasithin.H13.AS91.M24G
open scoped CFSG.KC.M24G.FixOctEq

set_option maxHeartbeats 0 in
theorem pair_ok : replayOK (Native.duadPairKey (Native.duadT0 ())) duadPpStepsF
    (Native.duadF770 ()) 900 DuadD.pL DuadD.pPar DuadD.pGen
    (posTree (Native.duadPairKey (Native.duadT0 ())) DuadD.pL) = true := by
  decide +kernel

theorem pairLen_ok : 770 ≤ DuadD.pL.length := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem a_ok : replayOK duadKeyF (duadStepsF Native.duadP1Gens) Native.fixOctIdTab (128 + 5)
    DuadD.aL DuadD.aPar DuadD.aGen (posTree duadKeyF DuadD.aL) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem b_ok : replayOK duadKeyF (duadStepsF Native.duadP2Gens) Native.fixOctIdTab (128 + 5)
    DuadD.bL DuadD.bPar DuadD.bGen (posTree duadKeyF DuadD.bL) = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem c_ok : replayOK duadKeyF (duadStepsF Native.duadQ3Gens) Native.fixOctIdTab (9 + 5)
    DuadD.cL DuadD.cPar DuadD.cGen (posTree duadKeyF DuadD.cL) = true := by
  decide +kernel

theorem aLen_ok : DuadD.aL.length = 128 := by
  decide +kernel

theorem bLen_ok : DuadD.bL.length = 128 := by
  decide +kernel

theorem cLen_ok : DuadD.cL.length = 9 := by
  decide +kernel

theorem gens_ok : duadGensOK Native.duadP1Gens = true ∧ duadGensOK Native.duadP2Gens = true ∧
    duadGensOK Native.duadQ3Gens = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem aInv_ok : duadInvOK (posTree duadKeyF DuadD.aL) DuadD.aL = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bInv_ok : duadInvOK (posTree duadKeyF DuadD.bL) DuadD.bL = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cInv_ok : duadInvOK (posTree duadKeyF DuadD.cL) DuadD.cL = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem aEa_ok : duadEaF DuadD.aL = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem bEa_ok : duadEaF DuadD.bL = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem cover_ok : duadCoverF SL = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem s2_ok : Native.duadS2Check () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem sat_ok : Native.duadSatCheck () = true := by
  decide +kernel

end CFSG.KC.M24G.DuadC
