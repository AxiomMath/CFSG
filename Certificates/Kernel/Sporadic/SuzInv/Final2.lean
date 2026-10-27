module

public import Certificates.Kernel.Sporadic.SuzInv.Glue
public import Certificates.Kernel.Sporadic.SuzInv.Full2
public import Certificates.Kernel.Sporadic.SuzInv.Inner2
import all CFSG.Sporadic.SuzOddCore.InvArrays
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.SuzOddCore CFSG.Certificates.Native

theorem derivsF2 : invFullDerivs 2 = CFSG.Sporadic.Schreier.Co3.Native.wordsArr 3 8 derivF2 := by
  decide

theorem derivsI2 : invInnerDerivs 2 =
    CFSG.Sporadic.Schreier.Co3.Native.wordsArr 2 6 derivI2 := by
  decide

theorem facts2 : rawChainOK 1782 (invFullGenArrs 2) (invFullStrongArrs 2)
      (invFullBases.getD 2 []).toArray (invFullDerivs 2) 4 = true ∧
    (rawOrbitSizes 1782 (invFullStrongArrs 2) (invFullBases.getD 2 []).toArray).prod = 380160 ∧
    rawChainOK 1782 (invInnerGenArrs 2) (invInnerStrongArrs 2)
      (invInnerBases.getD 2 []).toArray (invInnerDerivs 2) 4 = true ∧
    (rawOrbitSizes 1782 (invInnerStrongArrs 2) (invInnerBases.getD 2 []).toArray).prod =
      190080 := by
  refine ⟨chain_of bindsF2 gensF2.1 (by norm_num) gensF2.2 genF2 ?_, ?_,
    chain_of bindsI2 gensI2.1 (by norm_num) gensI2.2 genI2 ?_, ?_⟩
  · rw [derivsF2]
    exact rawChainK_sound (NS := 223) (CH := 8) bindsF2 SuzInvF2.head SuzInvF2.hl (by norm_num)
      SuzInvF2.hs
  · rw [rawOrbitSizesK_sound bindsF2 permF2 SuzInvF2.hl]
    decide
  · rw [derivsI2]
    exact rawChainK_sound (NS := 223) (CH := 8) bindsI2 SuzInvI2.head SuzInvI2.hl (by norm_num)
      SuzInvI2.hs
  · rw [rawOrbitSizesK_sound bindsI2 permI2 SuzInvI2.hl]
    decide

end CertificateChecks.KernelSpor.SuzInv

end
