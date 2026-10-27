module

public import Certificates.Kernel.Sporadic.SuzInv.Glue
public import Certificates.Kernel.Sporadic.SuzInv.Full3
public import Certificates.Kernel.Sporadic.SuzInv.Inner3
import CFSG.Sporadic.SuzOddCore.InvArrays
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.SuzOddCore CFSG.Certificates.Native

theorem derivsF3 : invFullDerivs 3 = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 6 13 derivF3 := by
  decide

theorem derivsI3 : invInnerDerivs 3 =
    CFSG.Sporadic.Schreier.Co3.Native.wordsArr 5 11 derivI3 := by
  decide

theorem facts3 : rawChainOK 1782 (invFullGenArrs 3) (invFullStrongArrs 3)
      (invFullBases.getD 3 []).toArray (invFullDerivs 3) 4 = true ∧
    (rawOrbitSizes 1782 (invFullStrongArrs 3) (invFullBases.getD 3 []).toArray).prod = 2419200 ∧
    rawChainOK 1782 (invInnerGenArrs 3) (invInnerStrongArrs 3)
      (invInnerBases.getD 3 []).toArray (invInnerDerivs 3) 4 = true ∧
    (rawOrbitSizes 1782 (invInnerStrongArrs 3) (invInnerBases.getD 3 []).toArray).prod =
      1209600 := by
  refine ⟨chain_of bindsF3 gensF3.1 (by norm_num) gensF3.2 genF3 ?_, ?_,
    chain_of bindsI3 gensI3.1 (by norm_num) gensI3.2 genI3 ?_, ?_⟩
  · rw [derivsF3]
    exact rawChainK_sound (NS := 223) (CH := 8) bindsF3 SuzInvF3.head SuzInvF3.hl (by norm_num)
      SuzInvF3.hs
  · rw [rawOrbitSizesK_sound bindsF3 permF3 SuzInvF3.hl]
    decide
  · rw [derivsI3]
    exact rawChainK_sound (NS := 223) (CH := 8) bindsI3 SuzInvI3.head SuzInvI3.hl (by norm_num)
      SuzInvI3.hs
  · rw [rawOrbitSizesK_sound bindsI3 permI3 SuzInvI3.hl]
    decide

end CertificateChecks.KernelSpor.SuzInv

end
