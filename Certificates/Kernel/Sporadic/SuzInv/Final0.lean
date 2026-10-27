module

public import Certificates.Kernel.Sporadic.SuzInv.Glue
public import Certificates.Kernel.Sporadic.SuzInv.Full0
public import Certificates.Kernel.Sporadic.SuzInv.Inner0
import all CFSG.Sporadic.SuzOddCore.InvArrays
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.SuzOddCore CFSG.Certificates.Native

theorem derivsF0 : invFullDerivs 0 = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 12 19 derivF0 := by
  decide

theorem derivsI0 : invInnerDerivs 0 =
    CFSG.Sporadic.Schreier.Co3.Native.wordsArr 22 28 derivI0 := by
  decide

theorem facts0 : rawChainOK 1782 (invFullGenArrs 0) (invFullStrongArrs 0)
      (invFullBases.getD 0 []).toArray (invFullDerivs 0) 4 = true ∧
    (rawOrbitSizes 1782 (invFullStrongArrs 0) (invFullBases.getD 0 []).toArray).prod = 322560 ∧
    rawChainOK 1782 (invInnerGenArrs 0) (invInnerStrongArrs 0)
      (invInnerBases.getD 0 []).toArray (invInnerDerivs 0) 4 = true ∧
    (rawOrbitSizes 1782 (invInnerStrongArrs 0) (invInnerBases.getD 0 []).toArray).prod =
      161280 := by
  refine ⟨chain_of bindsF0 gensF0.1 (by norm_num) gensF0.2 genF0 ?_, ?_,
    chain_of bindsI0 gensI0.1 (by norm_num) gensI0.2 genI0 ?_, ?_⟩
  · rw [derivsF0]
    exact rawChainK_sound (NS := 223) (CH := 8) bindsF0 SuzInvF0.head SuzInvF0.hl (by norm_num)
      SuzInvF0.hs
  · rw [rawOrbitSizesK_sound bindsF0 permF0 SuzInvF0.hl]
    decide
  · rw [derivsI0]
    exact rawChainK_sound (NS := 223) (CH := 8) bindsI0 SuzInvI0.head SuzInvI0.hl (by norm_num)
      SuzInvI0.hs
  · rw [rawOrbitSizesK_sound bindsI0 permI0 SuzInvI0.hl]
    decide

end CertificateChecks.KernelSpor.SuzInv

end
