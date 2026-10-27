module

public import Certificates.Kernel.HN1408.Words
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab65ACheck
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3Model

theorem l65 : lettersOK tab65AWord = true := by decide +kernel
theorem l65W : lettersOK tab65AW = true := by decide +kernel
theorem l65R : lettersOK tab65AW.reverse = true := by decide +kernel

theorem k65i : invEqK 1408 11 (mask 11) (1408 * 11) (WK tab65AW) (WK tab65AW.reverse) = true := by
  quickRfl

theorem k65c : Nat.beq (pc (pc (WK tab65AW) (WK wordB)) (WK tab65AW.reverse)) (WK tab65AWord) =
    true := by
  quickRfl

end CFSG.KD.HN1408

end
