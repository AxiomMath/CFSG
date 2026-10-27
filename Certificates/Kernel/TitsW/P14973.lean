module

public import CFSG.RankThree.PartOne.S12.Sec1511AutTitsInputs
public import Certificates.Kernel.TitsW.Alg
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Schreier.TitsInvCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsW.P14973

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits CFSG.RankThree.PartOne.K159
open CFSG.RankThree.PartOne.Sec1511 CertificateChecks.KernelTitsW

theorem lA : CFSG.KS.Raw.lettersK 13 titsAWord = true := by quickRfl
theorem lB : CFSG.KS.Raw.lettersK 13 titsBWord = true := by quickRfl
theorem lG : CFSG.KS.Raw.lettersK 13 titsGWord = true := by quickRfl

theorem pow_eq {p : Nat} (hp : Gd p) (k : Nat) :
    powArr (CFSG.KS.Raw.unpack 1755 11 p) k = CFSG.KS.Raw.unpack 1755 11 (ppw p k) :=
  pow_G hp (by simp [powArr]) (fun k => by simp [powArr]) k

theorem autCheck : TitsAutCheck := by
  unfold TitsAutCheck
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp (maxDischargeDepth := 64) only [pairArr, titsAArr, titsBArr, titsGArr,
    wordArr_D lA, wordArr_D lB, wordArr_D lG,
    invCand_G, compA_G, eqA_G, isInvA_G, idA_G, pow_eq, allLt_allN, Gd.mul, Gd.inv, Gd.one, Gd_WD,
    Gd.pow]
  all_goals quickRfl

theorem rWord_letters : ∀ k, CFSG.KS.Raw.lettersK 13 (titsRWord k) = true
  | 0 => by quickRfl
  | 1 => by quickRfl
  | 2 => by quickRfl
  | _ + 3 => by quickRfl

theorem bigWord_letters (n : Nat) : CFSG.KS.Raw.lettersK 13 (titsBigWord n) = true := by
  rw [titsBigWord, lettersK_append, lettersK_flatten_replicate lG, rWord_letters]
  rfl

theorem bigArr_eq (n : Nat) : titsBigArr n = CFSG.KS.Raw.unpack 1755 11 (WD (titsBigWord n)) :=
  wordArr_D (bigWord_letters n)

theorem bigCheck : TitsBigCheck := by
  unfold TitsBigCheck
  refine ⟨by decide, by decide, ?_⟩
  rw [allLt_allN]
  change CFSG.KC.Enum.allN 48 (fun n => titsBigOK n) = true
  simp (maxDischargeDepth := 64) only [titsBigOK, pairArr, titsAArr, titsBArr, bigArr_eq,
    wordArr_D lA, wordArr_D lB,
    invCand_G, compA_G, eqA_G, isInvA_G, idA_G, pow_eq, allLt_allN, Gd.mul, Gd.inv, Gd.one, Gd_WD,
    Gd.pow]
  quickRfl

end CertificateChecks.KernelTitsW.P14973

end
