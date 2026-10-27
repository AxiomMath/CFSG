module

public import Certificates.Kernel.Sporadic.SuzInv.Glue
public import Certificates.Kernel.Sporadic.SuzInv.Full1
public import Certificates.Kernel.Sporadic.SuzInv.Inner1
import all CFSG.Sporadic.SuzOddCore.InvArrays
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.SuzOddCore CFSG.Certificates.Native

theorem derivsF1 : invFullDerivs 1 = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 6 11 derivF1 := by
  decide

theorem derivsI1 : invInnerDerivs 1 =
    CFSG.Sporadic.Schreier.Co3.Native.wordsArr 10 16 derivI1 := by
  decide

theorem facts1 : rawChainOK 1782 (invFullGenArrs 1) (invFullStrongArrs 1)
      (invFullBases.getD 1 []).toArray (invFullDerivs 1) 4 = true ∧
    (rawOrbitSizes 1782 (invFullStrongArrs 1) (invFullBases.getD 1 []).toArray).prod = 6635520 ∧
    rawChainOK 1782 (invInnerGenArrs 1) (invInnerStrongArrs 1)
      (invInnerBases.getD 1 []).toArray (invInnerDerivs 1) 4 = true ∧
    (rawOrbitSizes 1782 (invInnerStrongArrs 1) (invInnerBases.getD 1 []).toArray).prod =
      3317760 := by
  refine ⟨chain_of bindsF1 gensF1.1 (by norm_num) gensF1.2 genF1 ?_, ?_,
    chain_of bindsI1 gensI1.1 (by norm_num) gensI1.2 genI1 ?_, ?_⟩
  · rw [derivsF1]
    exact rawChainK_sound (NS := 223) (CH := 8) bindsF1 SuzInvF1.head SuzInvF1.hl (by norm_num)
      SuzInvF1.hs
  · rw [rawOrbitSizesK_sound bindsF1 permF1 SuzInvF1.hl]
    decide
  · rw [derivsI1]
    exact rawChainK_sound (NS := 223) (CH := 8) bindsI1 SuzInvI1.head SuzInvI1.hl (by norm_num)
      SuzInvI1.hs
  · rw [rawOrbitSizesK_sound bindsI1 permI1 SuzInvI1.hl]
    decide

end CertificateChecks.KernelSpor.SuzInv

end
