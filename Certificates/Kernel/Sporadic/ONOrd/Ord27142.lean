module

public import Certificates.Kernel.Sporadic.ONOrd.Seed2128
public import Certificates.Kernel.Sporadic.ONOrd.Chk27142
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.ONOrderEightCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONOrd

open CFSG.KS.ONLin CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Sporadic.ONOddCore
open CFSG.EvenSporadicStandard.Induction CertificateChecks.KernelSpor.ON8

theorem lin_codeK (c : Nat) : L (codeK c) := by
  unfold codeK
  cases Nat.beq c 0 <;> cases Nat.beq c 1 <;> cases Nat.beq c 2 <;>
    first | exact lin_fA | exact lin_fAI | exact lin_fB | exact lin_fBI

theorem lin_word : ∀ w : List Nat, L fun x => w.foldr codeK x
  | [] => Lin.id
  | c :: w => Lin.comp (lin_codeK c) (lin_word w)

theorem lin_o8K : L o8K := lin_word o8W

section

variable {a ai b bi : Array Nat} (ha : Rd (nPts ()) a fA) (hai : Rd (nPts ()) ai fAI)
  (hb : Rd (nPts ()) b fB) (hbi : Rd (nPts ()) bi fBI)

include ha hai hb hbi in
theorem rd_code (c : Nat) : Rd (nPts ()) (onCodeTab a ai b bi c) (codeK c) := by
  unfold onCodeTab
  by_cases h0 : c = 0
  · subst h0
    exact ha
  rw [if_neg h0]
  by_cases h1 : c = 1
  · subst h1
    exact hai
  rw [if_neg h1]
  by_cases h2 : c = 2
  · subst h2
    exact hb
  rw [if_neg h2]
  have e : codeK c = fBI := by
    funext x
    unfold codeK
    rw [Bool.eq_false_iff.2 fun h => h0 (Nat.eq_of_beq_eq_true h),
      Bool.eq_false_iff.2 fun h => h1 (Nat.eq_of_beq_eq_true h),
      Bool.eq_false_iff.2 fun h => h2 (Nat.eq_of_beq_eq_true h)]
  rw [e]
  exact hbi

include ha hai hb hbi in
theorem rd_word : ∀ w : List Nat,
    Rd (nPts ()) (onWordTab a ai b bi w) (fun x => w.foldr codeK x)
  | [] => by
    unfold onWordTab
    rw [List.foldr_nil]
    exact rd_pid.congr fun _ _ => rfl
  | c :: w => by
    unfold onWordTab
    rw [List.foldr_cons]
    exact (rd_pcomp (rd_code ha hai hb hbi c) (rd_word w)).congr fun _ _ => rfl

end

theorem ord27142 : onOrderEightOK (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).alpha)
    (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).beta) = true := by
  have ra := rd_alpha
  have rb := rd_beta
  generalize natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).alpha = a at ra ⊢
  generalize natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).beta = b at rb ⊢
  have rai := rd_pinvCand ra (fun x hx => fAI_lt hx) fun x hx => fAI_fA hx
  have rbi := rd_pinvCand rb (fun x hx => fBI_lt hx) fun x hx => fBI_fB hx
  have rx : Rd (nPts ()) (onWordTab a (pinvCand (nPts ()) a) b (pinvCand (nPts ()) b) onWordO8) o8K :=
    rd_word ra rai rb rbi onWordO8
  unfold onOrderEightOK
  dsimp only
  rw [pisInv_of ra rai fun x hx => fAI_fA hx, pisInv_of rb rbi fun x hx => fBI_fB hx,
    peq_id (rd_ppow rx 8) (lin_powK lin_o8K 8) o8_ok, peq_ne (rd_ppow rx 4) o4_ne]
  rfl

end CertificateChecks.KernelSpor.ONOrd

end
