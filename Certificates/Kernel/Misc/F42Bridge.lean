module

public import Certificates.Kernel.Misc.F42
import Mathlib.Tactic.NormNum
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PK.MiscBase
import Certificates.Data.Kernel.Misc.T46

public section

namespace CFSG.KD.Misc.F42

open CFSG.KC.Misc CFSG.KC.Misc.F42 CFSG.LieType.Multipliers.F42 CFSG.Blueprint.Chevalley

set_option maxRecDepth 200000 in
theorem wfIChk : CFSG.KC.LQT.P.allN (508 + 2) (fun k => wfS (nthV I k)) = true := by quickRfl

theorem facts : (List.range 48).all (liftOK lifts) = true ∧ pairsOK lifts = true ∧
    (List.range 48).all (wordOK lifts) = true ∧ negOK lifts 0 35 = true := by
  have h := f42_sound (nP := 32) bA bB bS bRefs bRoots fmt ints start nIeq lenF insAll
    (by norm_num) liftsChk roots liftAll pairAll wordAll neg (CFSG.KS.PK.allN_lqt_iff.1 wfIChk)
  rw [lifts_eq, pairsOK_eq, negOK_eq]
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  have e : wordOK (liftsOf payloadA payloadB slpText liftRefs) =
      wordOKG f4ArtifactRoots commPairs (liftsOf payloadA payloadB slpText liftRefs) :=
    funext fun k => wordOK_eq _ k
  rw [e]
  exact h.2.2.1

end CFSG.KD.Misc.F42

end
