module

public import Certificates.Kernel.Sporadic.ONVec.CertStrB
public import Certificates.Kernel.Sporadic.ONVec.CertStrC

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native
open CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.ON (TT UU)

theorem band' {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

theorem strong_a : peq nPts TTA[0]!
    (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).alpha) = true := by
  have h : peq 245520 (Array.ofFn (n := 245520) fun i => TT 0 i.val) (tabArr ONV.A 245520) = true :=
    peq_ofFn2 (f := TT 0) (g := fun i => tab ONV.A i) fun _ _ => rfl
  rw [← (ON.orb_tabs ON.mvAll ON.ordAll ON.sortAll).1, ← TTA_get (by norm_num)] at h
  exact h

theorem strong_b : peq nPts TTA[1]!
    (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).beta) = true := by
  have h : peq 245520 (Array.ofFn (n := 245520) fun i => TT 1 i.val) (tabArr ONV.B 245520) = true :=
    peq_ofFn2 (f := TT 1) (g := fun i => tab ONV.B i) fun _ _ => rfl
  rw [← (ON.orb_tabs ON.mvAll ON.ordAll ON.sortAll).2, ← TTA_get (by norm_num)] at h
  exact h

theorem strong_words_ok : allBelowN 7 (fun j => decide (j < 2) ||
    (plettersOK j CFSG.ONSchreier.Data.strongWords[j]! &&
      peq 245520 TTA[j]! (pword 245520 TTA (pinvs 245520 TTA) CFSG.ONSchreier.Data.strongWords[j]!))) =
    true := by
  refine allBelowN_of fun j hj => ?_
  by_cases h2 : j < 2
  · simp only [h2, decide_true, Bool.true_or]
  · have hw := strong_word hj (by omega)
    simp only [h2, decide_false, Bool.false_or, Bool.and_eq_true]
    exact hw

theorem strong_TTA : strongOK nPts (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).alpha)
    (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).beta) TTA
    CFSG.ONSchreier.Data.strongWords = true := by
  obtain ⟨w1, -, -⟩ := ON.words_ok
  have hs : TTA.size = CFSG.ONSchreier.Data.strongWords.size := by rw [TTA_size, w1]
  have h2 : 2 ≤ CFSG.ONSchreier.Data.strongWords.size := by rw [w1]; norm_num
  have hi := strong_inv
  have hw := strong_words_ok
  rw [← TTA_size] at hi hw
  unfold strongOK
  have hb : (TTA.size == CFSG.ONSchreier.Data.strongWords.size) = true := by
    rw [hs, beq_self_eq_true]
  refine band' (band' (band' (band' (band' (decide_eq_true h2) hb) ?_) ?_) ?_) ?_
  · exact strong_a
  · exact strong_b
  · exact hi
  · exact hw

theorem strong_ok : strongOK nPts (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).alpha)
    (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).beta)
    (strongArrs nPts (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).alpha)
      (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).beta) CFSG.ONSchreier.Data.strongWords)
    CFSG.ONSchreier.Data.strongWords = true := by
  have hq : strongArrs nPts (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).alpha)
      (natTab (vorbit (digitsW CFSG.ONSchreier.Data.rootDigits)).beta)
      CFSG.ONSchreier.Data.strongWords = TTA := ON.qon_eq'
  have h := strong_TTA
  rw [← hq] at h
  exact h

end CertificateChecks.KernelSpor.ONVec

end
