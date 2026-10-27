module

public import Certificates.Kernel.HN1408.ShVChk
public import Certificates.Kernel.HN1408.CayleyGlue

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem shvNot {c : Bool} (h : bIf(c, false, true) = true) : c = false := by
  cases c
  · rfl
  · exact absurd h (by decide)

theorem shvConj_of {c : List Nat} {CI X Z : Nat} (hc : lettersOK c = true) (hX : Cn X) (hZ : Cn Z)
    (h : shvConj (WK c) CI X Z = true) :
    conjEqOK c (tabT (unpack 1408 11 X)) (tabT (unpack 1408 11 Z)) = true := by
  unfold shvConj at h
  obtain ⟨h1, h2⟩ := cyBA h
  obtain ⟨h3, h4⟩ := cyBA h2
  exact conjEqOK_of hc h1 h3 hX hZ h4

theorem shvUK_spec {u r a z C CI : Nat} (h : shvUK u r a z C CI = true) :
    Nat.beq (ppK u 2) idK = true ∧ Nat.beq u idK = false ∧ Nat.beq u a = false ∧
      commP u r = true ∧ shvConj C CI z u = true := by
  unfold shvUK at h
  obtain ⟨h1, h⟩ := cyBA h
  obtain ⟨h2, h⟩ := cyBA h
  obtain ⟨h3, h⟩ := cyBA h
  obtain ⟨h4, h5⟩ := cyBA h
  exact ⟨h1, shvNot h2, shvNot h3, h4, h5⟩

theorem shvA8K_spec {p r b : Nat} {CK CI : Nat → Nat} (h : shvA8K p r b CK CI = true) :
    Nat.beq (ppK p 5) idK = true ∧ Nat.beq p idK = false ∧ commP p b = true ∧
      ∀ k < 4, shvConj (CK k) (CI (k + 1)) r (ppK p (k + 1)) = true := by
  unfold shvA8K at h
  obtain ⟨h1, h⟩ := cyBA h
  obtain ⟨h2, h⟩ := cyBA h
  obtain ⟨h3, h4⟩ := cyBA h
  exact ⟨h1, shvNot h2, h3, fun k hk => allN_spec h4 k hk⟩

theorem shv_d5_letters : ∀ w ∈ d5Words, lettersOK w = true := by decide

theorem shv_ck_letters : ∀ k < 4, lettersOK (ckWords.getD k []) = true := by decide

theorem shapeD5OK_true : shapeD5OK = true := by
  have r := tabW_eq (wd := fix5C.rep) (by decide)
  have hcomm : commWordsOK d5Words (tabW fix5C.rep) = true := by
    unfold commWordsOK
    rw [List.all_eq_true]
    intro w hw
    have hw' := tabW_eq (shv_d5_letters w hw)
    rw [hw'.1, r.1, commTT_eq hw'.2 r.2]
    exact List.all_eq_true.1 shvkD5 w hw
  have hcay : cayleyOK capS 120 d5Words imgD5 = true :=
    cayleyOK_of sl25Code shv_d5_letters shvkHd shvkRec rfl (by decide +kernel)
      (by decide +kernel) shvkCay
  unfold shapeD5OK
  rw [wordOK_of (w := fix5C.rep) (by decide), hcomm, hcay]
  rfl

theorem shapeUOK_true : shapeUOK = true := by
  have u := tabW_eq (wd := u0Word) (by decide)
  have b := tabW_eq (wd := fix5B.rep) (by decide)
  have a := tabW_eq (wd := wordA) (by decide)
  have z := tabW_eq (wd := wordZ₁) (by decide)
  obtain ⟨h1, h2, h3, h4, h5⟩ := shvUK_spec shvkU
  unfold shapeUOK
  simp only []
  rw [gensOK_true, wordOK_of (w := fix5B.rep) (by decide), wordOK_of (w := u0Word) (by decide),
    u.1, b.1, a.1, z.1,
    primeOrderOK_eq u.2, tblEq_eq u.2 a.2, commTT_eq u.2 b.2, h1, h2, h3, h4,
    shvConj_of (c := c0Word) (by decide) z.2 u.2 h5]
  rfl

theorem shapeA8OK_true : shapeA8OK = true := by
  have rp := tabW_eq (wd := rpWord) (by decide)
  have r := tabW_eq (wd := fix5C.rep) (by decide)
  have b := tabW_eq (wd := wordB) (by decide)
  obtain ⟨h1, h2, h3, h4⟩ := shvA8K_spec shvkA8
  have hk : ∀ k < 4, rpConjOK (k + 1) (ckWords.getD k []) = true := by
    intro k hk
    unfold rpConjOK
    rw [r.1, rp.1, powT_eq rp.2]
    exact shvConj_of (shv_ck_letters k hk) r.2 (cn_ppK rp.2 _) (h4 k hk)
  have k1 : rpConjOK 1 (ckWords.getD 0 []) = true := hk 0 (by decide)
  have k2 : rpConjOK 2 (ckWords.getD 1 []) = true := hk 1 (by decide)
  have k3 : rpConjOK 3 (ckWords.getD 2 []) = true := hk 2 (by decide)
  have k4 : rpConjOK 4 (ckWords.getD 3 []) = true := hk 3 (by decide)
  unfold shapeA8OK
  rw [k1, k2, k3, k4, gensOK_true, wordOK_of (w := fix5C.rep) (by decide),
    wordOK_of (w := rpWord) (by decide), rp.1, b.1, primeOrderOK_eq rp.2, commTT_eq rp.2 b.2, h1,
    h2, h3]
  rfl

theorem shapesVOK_true : shapesVOK = true := by
  unfold shapesVOK
  rw [shapeD5OK_true, shapeUOK_true, shapeA8OK_true]
  rfl

end CFSG.KD.HN1408

end
