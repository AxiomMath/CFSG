module

public import Certificates.Data.SmithB45TitsTor
public import Certificates.Kernel.TitsW.Alg
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsW.P260420

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.B45Tor
open CertificateChecks.KernelTitsW

theorem facts : titsTorWordsCheck = true ∧ titsTorPlaneCheck = true ∧ titsTorNormCheck = true ∧
    titsTorRelCheck = true ∧ titsTorClassCheck = true := by
  have l1 : CFSG.KS.Raw.lettersK 13 titsWordR₁ = true := by quickRfl
  have l2 : CFSG.KS.Raw.lettersK 13 titsWordR₂ = true := by quickRfl
  have l3 : CFSG.KS.Raw.lettersK 13 titsWordI = true := by quickRfl
  have l4 : CFSG.KS.Raw.lettersK 13 titsWordJ = true := by quickRfl
  have l5 : CFSG.KS.Raw.lettersK 13 titsWordH = true := by quickRfl
  have l6 : CFSG.KS.Raw.lettersK 13 titsWordGy = true := by quickRfl
  have l7 : CFSG.KS.Raw.lettersK 13 titsWordG₁ = true := by quickRfl
  have l8 : CFSG.KS.Raw.lettersK 13 titsWordG₂ = true := by quickRfl
  have l9 : CFSG.KS.Raw.lettersK 13 titsTWord = true := by quickRfl
  have l10 : CFSG.KS.Raw.lettersK 13 titsCenterWord = true := by quickRfl
  have hpow : ∀ p, Gd p → ∀ k, titsTorPow (CFSG.KS.Raw.unpack 1755 11 p) k =
      CFSG.KS.Raw.unpack 1755 11 (ppw p k) := fun p hp =>
    pow_G hp (by simp [titsTorPow]) (fun k => by simp [titsTorPow])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals simp (maxDischargeDepth := 64) only [titsTorWordsCheck, titsTorPlaneCheck,
    titsTorNormCheck, titsTorRelCheck, titsTorClassCheck, titsTorR, titsTorY, titsTorArr,
    titsTArr, titsZArr, conjArr, List.all_cons, List.all_nil, Bool.and_true,
    wordArr_D l1, wordArr_D l2, wordArr_D l3, wordArr_D l4, wordArr_D l5, wordArr_D l6,
    wordArr_D l7, wordArr_D l8, wordArr_D l9, wordArr_D l10,
    invCand_G, compA_G, eqA_G, isInvA_G, idA_G, hpow, allLt_allN, Gd.mul, Gd.inv, Gd.one, Gd_WD,
    Gd.pow]
  all_goals quickRfl

end CertificateChecks.KernelTitsW.P260420

end
