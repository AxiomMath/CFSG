module

public import Certificates.Data.Kernel.LocalQT.SylE
public import Certificates.Data.Kernel.LocalQT.SylL
public import CFSG.Certificates.Kernel.LocalQTWordSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TCheckInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24CheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LieType.CurtisTits.Recognition
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TChain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TUniq
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4137

open CFSG.KC.LQT.Syl CFSG.KC.LQT.W CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Mathieu
  CFSG.Blueprint

@[expose] def GC : List Nat :=
  [817395973838868159142633316802379971, 938078705133617800621527216201835139]

theorem hG : [m24a, m24b].map (fun x : ↥NativeSporadic.M24 => codeP (x : Equiv.Perm (Fin 24))) =
    GC := by decide +kernel

theorem k1 : eabK 24 6 (rlGK 24 GC m24RGens m24E1Bw) = true := by quickRfl
theorem k2 : eabK 24 6 (rlGK 24 GC m24RGens m24E2Bw) = true := by quickRfl
theorem kH : lenIs (heavyK 24 (rlGK 24 GC m24RGens m24RWords)
    (lstK 24 6 (rlGK 24 GC m24RGens m24E1Bw) ++ lstK 24 6 (rlGK 24 GC m24RGens m24E2Bw)) 62)
    0 = true := by quickRfl

theorem pA : (AdjData m24E1B (m24Cj m24E1G2) m24E1A2 ∧ AdjData m24E1B (m24Cj m24E1G3) m24E1A3) ∧
    (AdjData m24E2B (m24Cj m24E2G2) m24E2A2 ∧ AdjData m24E2B (m24Cj m24E2G3) m24E2A3) := by
  decide +kernel
theorem pS1 : (slpEval (normH NativeSporadic.M24)
      (m24Gens18 m24E1B (m24Cj m24E1G2) (m24Cj m24E1G3)) m24E1Slp).getD m24E1Tg.1 1 = m24a ∧
    (slpEval (normH NativeSporadic.M24)
      (m24Gens18 m24E1B (m24Cj m24E1G2) (m24Cj m24E1G3)) m24E1Slp).getD m24E1Tg.2 1 = m24b := by
  decide +kernel
theorem pS2 : (slpEval (normH NativeSporadic.M24)
      (m24Gens18 m24E2B (m24Cj m24E2G2) (m24Cj m24E2G3)) m24E2Slp).getD m24E2Tg.1 1 = m24a ∧
    (slpEval (normH NativeSporadic.M24)
      (m24Gens18 m24E2B (m24Cj m24E2G2) (m24Cj m24E2G3)) m24E2Slp).getD m24E2Tg.2 1 = m24b := by
  decide +kernel

end CFSG.KD.LQT.C4137

end
