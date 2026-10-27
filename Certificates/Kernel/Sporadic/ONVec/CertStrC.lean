module

public import Certificates.Kernel.Sporadic.ONVec.CertStrA

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.Sporadic.ON.Native CFSG.ONSchreier.Native
open CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.ON (TT UU)

theorem word_peq {j : Nat} (hj : j < 7) {w : List Int} (hwl : ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 7)
    (key : ∀ x < 245520, TT j x = w.foldr (CFSG.KS.TW.GZ TT UU) x) :
    peq 245520 TTA[j]! (pword 245520 TTA (pinvs 245520 TTA) w) = true := by
  have e1 : pword 245520 TTA (pinvs 245520 TTA) w =
      Array.ofFn (n := 245520) fun i => w.foldr (CFSG.KS.TW.GZ TT UU) i.val :=
    CFSG.KS.PW.pword_eq letters_TTA hwl
  have e2 : TTA[j]! = Array.ofFn (n := 245520) fun i => TT j i.val := TTA_get hj
  have h : peq 245520 (Array.ofFn (n := 245520) fun i => TT j i.val)
      (Array.ofFn (n := 245520) fun i => w.foldr (CFSG.KS.TW.GZ TT UU) i.val) = true :=
    peq_ofFn2 (f := TT j) (g := fun x => w.foldr (CFSG.KS.TW.GZ TT UU) x) key
  rw [← e1, ← e2] at h
  exact h

theorem word_key {j : Nat} (hj : j < 7) (h2 : 2 ≤ j) {w : List Int}
    (e1 : encW w = ONV.WC j) (e2 : w.length = ONV.WL j)
    (hd : CFSG.KS.Words.decW (encW w) w.length = w) :
    ∀ x < 245520, TT j x = w.foldr (CFSG.KS.TW.GZ TT UU) x := by
  intro x hx
  rw [tr_word hx hj h2, CFSG.KS.TW.trace_eq, ← e1, ← e2, hd]

theorem letters_of {j : Nat} {w : List Int} (e3 : plettersOK j w = true) (hj : j < 7) :
    ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 7 := by
  intro l hl
  have := List.all_eq_true.1 e3 l hl
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
  exact ⟨this.1, by omega⟩

theorem strong_word {j : Nat} (hj : j < 7) (h2 : 2 ≤ j) :
    plettersOK j CFSG.ONSchreier.Data.strongWords[j]! = true ∧
      peq 245520 TTA[j]! (pword 245520 TTA (pinvs 245520 TTA) CFSG.ONSchreier.Data.strongWords[j]!) =
        true := by
  obtain ⟨-, -, w3⟩ := ON.words_ok
  obtain ⟨e1, e2, e3⟩ := w3 j hj h2
  have hwl := letters_of e3 hj
  exact ⟨e3, word_peq hj hwl (word_key hj h2 e1 e2
    (decW_encW' _ fun l hl => ⟨(hwl l hl).1, by have := (hwl l hl).2; omega⟩))⟩

end CertificateChecks.KernelSpor.ONVec

end
