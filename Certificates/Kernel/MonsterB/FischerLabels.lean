
module

public import Certificates.Kernel.MonsterB.FischerLabChk
public import CFSG.Certificates.Kernel.MonsterB.FischerWordSound
public import CFSG.Certificates.Kernel.MonsterB.FischerPackSound

public section

namespace CertificateChecks.KernelMonB.F3067

open CFSG.Monster.B.TwoA.Fischer CFSG.Monster.B.TwoA.Fischer.Cert CFSG.Monster.B.Fischer
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KC.FischerK CFSG.KC.FischerE CFSG.KLie.CT
  CertificateChecks.KernelMonB.IndCand

theorem allN_true {n : Nat} {f : Nat → Bool} (h : allN n f = true) : ∀ i < n, f i = true := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    change Bool.rec (motive := fun _ => Bool) false (allN n f) (f n) = true at h
    cases hf : f n
    · rw [hf] at h
      exact absurd h Bool.false_ne_true
    · rw [hf] at h
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact ih h i hi
      · exact hf

theorem allN_of {n : Nat} {f : Nat → Bool} (h : ∀ i < n, f i = true) : allN n f = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Bool.rec (motive := fun _ => Bool) false (allN n f) (f n) = true
    rw [h n (by omega)]
    exact ih fun i hi => h i (by omega)

theorem invChk_all : ∀ k < 13, invChk k = true := by
  intro k hk
  interval_cases k
  exacts [kInv0, kInv1, kInv2, kInv3, kInv4, kInv5, kInv6, kInv7, kInv8, kInv9, kInv10, kInv11,
    kInv12]

theorem invPair_apply : ∀ k < 13, ∀ y < 3510, candF k y < 3510 ∧ invF k (candF k y) = y ∧
    invF k y < 3510 ∧ candF k (invF k y) = y := by
  intro k hk y hy
  have h := allN_true (invChk_all k hk) y hy
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem invPair : InvPair 3510 13 candF invF := invPair_apply

theorem jWordArr_get : ∀ w : List Nat, (∀ j ∈ w, j < 13) → ∀ y < 3510,
    (jWordArr w)[y]! = wordL candF w y
  | [], _, y, hy => by
    simp only [jWordArr]
    exact idA_get hy
  | j :: w, hw, y, hy => by
    have hw' : ∀ k ∈ w, k < 13 := fun k hk => hw k (List.mem_cons_of_mem j hk)
    simp only [jWordArr, wordL_cons]
    rw [compA_get hy, jWordArr_get w hw' y hy,
      cand_get (hw j List.mem_cons_self) (wordL_lt invPair w hw' y hy)]

theorem invCand_word {w : List Nat} (hw : ∀ j ∈ w, j < 13) {x : Nat} (hx : x < 3510) :
    (invCand 3510 (jWordArr w))[x]! = invWordL invF w x := by
  refine invCand_get (fun i hi => ?_) (fun x hx => ?_) hx
  · rw [jWordArr_get w hw i hi]
    exact ⟨wordL_lt invPair w hw i hi, invWord_word invPair w hw i hi⟩
  · rw [jWordArr_get w hw _ (invWordL_lt invPair w hw x hx)]
    exact ⟨invWordL_lt invPair w hw x hx, word_invWord invPair w hw x hx⟩

theorem jLabelArr_get {w : List Nat} (hw : ∀ j ∈ w, j < 13) {x : Nat} (hx : x < 3510) :
    (jLabelArr w)[x]! = labF w x := by
  have hs := invWordL_lt invPair w hw x hx
  have hc := (invPair_apply 12 (by omega) _ hs).1
  unfold jLabelArr
  rw [compA_get hx, invCand_word hw hx, compA_get hs, ← indCandidate_twelve,
    cand_get (by omega) hs, jWordArr_get w hw _ hc]
  rfl

theorem isInvA_word {w : List Nat} (hw : ∀ j ∈ w, j < 13) :
    isInvA 3510 (jWordArr w) (invCand 3510 (jWordArr w)) = true := by
  unfold isInvA
  rw [allLt_iff]
  intro i hi
  have hl := wordL_lt invPair w hw i hi
  rw [jWordArr_get w hw i hi, invCand_word hw hl, invWord_word invPair w hw i hi]
  simp [hl]

theorem labelCoord_eq (y : Nat) : labelCoord y = lcF y := by
  have h := kLC
  unfold lcChk at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hp, hl⟩, hb⟩ := h
  have := packW_get_all hp (by rw [hl]; exact hb) y
  rw [Array.toArray_toList] at this
  exact this

end CertificateChecks.KernelMonB.F3067

end
