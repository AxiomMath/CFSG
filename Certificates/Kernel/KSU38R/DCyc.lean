module

public import Certificates.Kernel.KSU38R.NoV4
import Mathlib.Tactic.Ring

public section

namespace CertificateChecks.KSU38RK

open CFSG.LieType.SeitzGeneration.HeisSmall HuppertU38F KSU38R CFSG.KC.HeisN

@[expose] def mulVecN (A : M3 ℕ) (c : ColN) : ColN :=
  (fk8.eAdd (fk8.eAdd (fk8.eMul A.a00 c.1) (fk8.eMul A.a01 c.2.1)) (fk8.eMul A.a02 c.2.2),
    fk8.eAdd (fk8.eAdd (fk8.eMul A.a10 c.1) (fk8.eMul A.a11 c.2.1)) (fk8.eMul A.a12 c.2.2),
    fk8.eAdd (fk8.eAdd (fk8.eMul A.a20 c.1) (fk8.eMul A.a21 c.2.1)) (fk8.eMul A.a22 c.2.2))

@[expose] def hasCycN (A : M3 ℕ) : Bool :=
  (fk8.cols4N 8).any fun c =>
    !Nat.beq (fk8.mDet (ofColsN c (mulVecN A c) (mulVecN A (mulVecN A c)))) 0

@[expose] def regFlagN (A : M3 ℕ) : Bool :=
  isScalarN (fk8.mMul (fk8.mMul A A) A) &&
    Nat.beq (fk8.ePow (fk8.mMul (fk8.mMul A A) A).a00 3) 1 && hasCycN A

@[expose] def commModN (A B : M3 ℕ) : Bool :=
  (List.range (fk8.p * fk8.p)).any fun n => mEq (fk8.mMul A B) (fk8.mSmul n (fk8.mMul B A))

@[expose] def proptoN (A B : M3 ℕ) : Bool :=
  (List.range (fk8.p * fk8.p)).any fun n => mEq A (fk8.mSmul n B)

@[expose] def ncommN (A B : M3 ℕ) : Bool :=
  !Nat.beq (fk8.mDet A) 0 && !Nat.beq (fk8.mDet B) 0 &&
    !(fk8.f4nzN 8).any fun n => mEq (fk8.mMul A B) (fk8.mSmul n (fk8.mMul B A))

@[expose] noncomputable def dCheckOneN2 (D : M3 ℕ) : Bool :=
  fk8.forallUnitaryN 8 fun Z =>
    !isScalarN (fk8.mMul (fk8.mMul Z Z) Z) || isScalarN Z || ncommN D Z ||
      proptoN Z D || proptoN Z (fk8.mMul D D) ||
      (List.range 3).any fun j => regFlagN (fk8.mMul (mpowN D j) Z)

@[expose] noncomputable def dN2 : Bool := dCheckOneN2 (matN [1, 0, 0, 0, 1, 0, 0, 0, 8])

theorem mulVec_toQ (A : M3 ℕ) (c : ColN) :
    mulVec (toQ A) (FK.colL fk8 GF8.ofNat' c) = FK.colL fk8 GF8.ofNat' (mulVecN A c) := by
  simp only [mulVec, FK.colL, mulVecN, FK.toL, FK.dec_eAdd fk8_sound, FK.dec_eMul fk8_sound]

theorem hasCyc_of (A : M3 ℕ) (h : hasCycN A = true) : hasCyc (toQ A) = true := by
  unfold hasCyc
  rw [FK.cols4_eq fk8_sound ho, List.any_map]
  obtain ⟨c, hc, hb⟩ := List.any_eq_true.1 h
  refine List.any_eq_true.2 ⟨c, hc, ?_⟩
  rw [Function.comp_apply]
  refine decide_eq_true fun h0 => ?_
  unfold cycDet at h0
  rw [mulVec_toQ, mulVec_toQ, FK.ofCols_colL, ← FK.toL_mDet fk8_sound] at h0
  have hlt : fk8.mDet (ofColsN c (mulVecN A c) (mulVecN A (mulVecN A c))) < fk8.p * fk8.p := by
    unfold FK.mDet FK.eSub
    exact FK.eAdd_lt fk8_sound _ _
  have e := FK.dec_inj fk8_sound hlt (FK.zero_lt_sq fk8_sound)
    (h0.trans (FK.dec_zero fk8_sound).symm)
  rw [e] at hb
  exact absurd hb (by decide)

theorem regFlag_of (A : M3 ℕ) (h : regFlagN A = true) : regFlagD A = true := by
  simp only [regFlagN, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [regFlagD, Bool.and_eq_true]
  refine ⟨⟨FK.isScalarN_sound fk8_sound _ h1, decide_eq_true ?_⟩, hasCyc_of A h3⟩
  have e := Nat.eq_of_beq_eq_true h2
  have k := FK.dec_ePow fk8_sound (fk8.mMul (fk8.mMul A A) A).a00 3
  rw [e, FK.dec_one fk8_sound] at k
  exact k.symm

theorem eMul_lt8 (x y : ℕ) : fk8.eMul x y < fk8.p * fk8.p := by
  unfold FK.eMul
  exact FK.pack_lt fk8_sound (fk8_sound.add_lt _ _) (fk8_sound.add_lt _ _)

theorem mEq_refl (A : M3 ℕ) : mEq A A = true := by
  simp only [mEq, Nat.beq_refl, Bool.and_self]

theorem commModN_of (A B : M3 ℕ) (h : commModD A B = true) : commModN A B = true := by
  obtain ⟨n, hn, he⟩ := List.any_eq_true.1 h
  refine List.any_eq_true.2 ⟨n, hn, ?_⟩
  have e := of_decide_eq_true he
  obtain ⟨l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ := FK.mMul_lt fk8_sound A B
  have i : ∀ {x y : ℕ}, x < fk8.p * fk8.p → y < fk8.p * fk8.p →
      FK.dec fk8 GF8.ofNat' x = FK.dec fk8 GF8.ofNat' y → x = y :=
    fun hx hy hd => FK.dec_inj fk8_sound hx hy hd
  have hX : fk8.mMul A B = fk8.mSmul n (fk8.mMul B A) :=
    M3.ext (i l0 (eMul_lt8 _ _) (congrArg M3.a00 e)) (i l1 (eMul_lt8 _ _) (congrArg M3.a01 e))
      (i l2 (eMul_lt8 _ _) (congrArg M3.a02 e)) (i l3 (eMul_lt8 _ _) (congrArg M3.a10 e))
      (i l4 (eMul_lt8 _ _) (congrArg M3.a11 e)) (i l5 (eMul_lt8 _ _) (congrArg M3.a12 e))
      (i l6 (eMul_lt8 _ _) (congrArg M3.a20 e)) (i l7 (eMul_lt8 _ _) (congrArg M3.a21 e))
      (i l8 (eMul_lt8 _ _) (congrArg M3.a22 e))
  rw [hX]
  exact mEq_refl _

theorem proptoD_of (A B : M3 ℕ) (h : proptoN A B = true) : proptoD A B = true := by
  obtain ⟨n, hn, he⟩ := List.any_eq_true.1 h
  exact List.any_eq_true.2 ⟨n, hn, decide_eq_true (congrArg toQ (FK.mEq_sound he))⟩

theorem m3_mul_assoc (a b c : M3 Q8) : a * b * c = a * (b * c) := by
  simp only [M3.mul_def, M3.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem m3_mul_one (a : M3 Q8) : a * 1 = a := by
  have e : (1 : M3 Q8) = ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩ := rfl
  rw [e, M3.mul_def]
  simp

theorem m3_det_mul (A B : M3 Q8) : (A * B).det = A.det * B.det := by
  simp only [M3.det, M3.mul_def]
  ring

theorem m3_det_smul (c : Q8) (A : M3 Q8) : (M3.smul c A).det = c ^ 3 * A.det := by
  simp only [M3.det, M3.smul]
  ring

theorem cube_one_mem : ∀ n, n < fk8.p * fk8.p → Nat.beq (fk8.ePow n 3) 1 = true →
    n ∈ fk8.f4nzN 8 := by
  decide +kernel

theorem toQ_det_ne {A : M3 ℕ} (h : Nat.beq (fk8.mDet A) 0 = false) : (toQ A).det ≠ 0 := by
  intro h0
  rw [← FK.toL_mDet fk8_sound] at h0
  have hlt : fk8.mDet A < fk8.p * fk8.p := by
    unfold FK.mDet FK.eSub
    exact FK.eAdd_lt fk8_sound _ _
  have e := FK.dec_inj fk8_sound hlt (FK.zero_lt_sq fk8_sound) (h0.trans (FK.dec_zero fk8_sound).symm)
  rw [e] at h
  exact absurd h (by decide)

theorem ncommN_sound {A B : M3 ℕ} (h : ncommN A B = true) : commModD A B = false := by
  simp only [ncommN, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hA, hB⟩, hn⟩ := h
  cases e : commModD A B
  · rfl
  · exfalso
    obtain ⟨n, hn64, he⟩ := List.any_eq_true.1 (commModN_of A B e)
    have hd := congrArg (fun M => (toQ M).det) (FK.mEq_sound he)
    simp only [toQ_mMul, toQ_mSmul, m3_det_mul, m3_det_smul] at hd
    have hab : (toQ A).det * (toQ B).det ≠ 0 := mul_ne_zero (toQ_det_ne hA) (toQ_det_ne hB)
    have hc : FK.dec fk8 GF8.ofNat' n ^ 3 = 1 := by
      refine mul_right_cancel₀ hab ?_
      rw [one_mul]
      nth_rw 2 [hd]
      rw [mul_comm (toQ B).det]
    have hlt : fk8.ePow n 3 < fk8.p * fk8.p := eMul_lt8 _ _
    have h3 : fk8.ePow n 3 = 1 := FK.dec_inj fk8_sound hlt (FK.one_lt_sq fk8_sound)
      (by rw [FK.dec_ePow fk8_sound, hc, FK.dec_one fk8_sound])
    have hm := cube_one_mem n (List.mem_range.1 hn64) (by rw [h3]; rfl)
    rw [List.any_eq_true.2 ⟨n, hm, he⟩] at hn
    exact absurd hn (by decide)

theorem m3_smul_mul (c : Q8) (A B : M3 Q8) : M3.smul c A * B = M3.smul c (A * B) := by
  simp only [M3.smul, M3.mul_def, M3.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem m3_mul_smul (c : Q8) (A B : M3 Q8) : A * M3.smul c B = M3.smul c (A * B) := by
  simp only [M3.smul, M3.mul_def, M3.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem m3_smul_smul (c d : Q8) (A : M3 Q8) : M3.smul c (M3.smul d A) = M3.smul (c * d) A := by
  simp only [M3.smul, M3.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem forallUnitary_mono {P Q : M3 Q8 → Bool} (hPQ : ∀ A, P A = true → Q A = true)
    (h : forallUnitary P = true) : forallUnitary Q = true := by
  rw [FK.forallUnitary_eq fk8_sound ho] at h ⊢
  exact FK.forallUnitaryN_mono 8 (fun A => hPQ _) h

theorem dCheckOne_sq {d e : M3 Q8} (hde : d * d = e) (hed : e * e = d) (h : dCheckOne d = true) :
    dCheckOne e = true := by
  unfold dCheckOne at h ⊢
  refine forallUnitary_mono (fun Z hZ => ?_) h
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hZ ⊢
  rcases hZ with ((((h1 | h1) | h1) | h1) | h1) | h1
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h1))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h1))))
  · refine Or.inl (Or.inl (Or.inl (Or.inr ?_)))
    cases k : commMod e Z
    · rfl
    · exfalso
      obtain ⟨l, hl⟩ := of_decide_eq_true k
      have key : e * e * Z = M3.smul (l * l) (Z * (e * e)) :=
        calc e * e * Z = e * (e * Z) := m3_mul_assoc _ _ _
          _ = e * M3.smul l (Z * e) := by rw [hl]
          _ = M3.smul l (e * Z * e) := by rw [m3_mul_smul, m3_mul_assoc]
          _ = M3.smul l (M3.smul l (Z * e) * e) := by rw [hl]
          _ = M3.smul (l * l) (Z * (e * e)) := by rw [m3_smul_mul, m3_smul_smul, m3_mul_assoc]
      rw [hed] at key
      have hd : commMod d Z = true := decide_eq_true ⟨l * l, key⟩
      rw [hd] at h1
      exact absurd h1 (by decide)
  · rw [← hed] at h1
    exact Or.inl (Or.inr h1)
  · rw [hde] at h1
    exact Or.inl (Or.inl (Or.inr h1))
  · obtain ⟨j, hj, hr⟩ := List.any_eq_true.1 h1
    have hj3 := List.mem_range.1 hj
    have p1 : ∀ a : M3 Q8, mpow a 1 = a := fun a => m3_mul_one a
    have p2 : ∀ a : M3 Q8, mpow a 2 = a * a := fun a => congrArg (a * ·) (m3_mul_one a)
    refine Or.inr (List.any_eq_true.2 ?_)
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · exact ⟨0, by simp, hr⟩
    · refine ⟨2, by simp, ?_⟩
      rw [p2, hed, ← p1 d]
      exact hr
    · refine ⟨1, by simp, ?_⟩
      rw [p1, ← hde, ← p2 d]
      exact hr

theorem dCheckOneN_of (D : M3 ℕ) (h : dCheckOneN2 D = true) : dCheckOneN D = true := by
  refine FK.forallUnitaryN_mono 8 (fun Z hZ => ?_) h
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hZ ⊢
  rcases hZ with ((((h1 | h1) | h1) | h1) | h1) | h1
  · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ?_))))
    cases e : isScalar (toQ (fk8.mMul (fk8.mMul Z Z) Z))
    · rfl
    · rw [FK.isScalarN_of_mMul fk8_sound _ _ e] at h1
      exact absurd h1 Bool.noConfusion
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (FK.isScalarN_sound fk8_sound _ h1)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (ncommN_sound h1))))
  · exact Or.inl (Or.inl (Or.inr (proptoD_of _ _ h1)))
  · exact Or.inl (Or.inr (proptoD_of _ _ h1))
  · obtain ⟨j, hj, hr⟩ := List.any_eq_true.1 h1
    exact Or.inr (List.any_eq_true.2 ⟨j, hj, regFlag_of _ hr⟩)

@[expose] def pow12N (A : M3 ℕ) : M3 ℕ :=
  fk8.mMul (fk8.mMul (fk8.mMul (fk8.mMul A A) A) (fk8.mMul (fk8.mMul A A) A))
    (fk8.mMul (fk8.mMul (fk8.mMul A A) A) (fk8.mMul (fk8.mMul A A) A))

@[expose] noncomputable def expN2 : Bool :=
  fk8.forallUnitaryN 8 fun A => isScalar (toQ (pow12N A))

theorem pow12_eq (A : M3 ℕ) : toQ (pow12N A) = toQ (mpowN A 12) := by
  rw [← mpow_toQ]
  simp only [pow12N, toQ_mMul, mpow, m3_mul_assoc, m3_mul_one]

theorem expN_of (h : expN2 = true) : expN = true := by
  unfold expN2 at h
  unfold expN
  simp only [pow12_eq] at h
  exact h

@[expose] def noV4N2 : Bool :=
  fk8.forallUnitaryN 8 (fun A => !isInvolD A || decide (toQ A ∈ invsN.map toQ)) &&
    invsN.all fun U => invsN.all fun V => ncommN U V || proptoN U V

theorem noV4N_of (h : noV4N2 = true) : noV4N = true := by
  unfold noV4N2 at h
  rw [Bool.and_eq_true] at h
  unfold noV4N
  rw [Bool.and_eq_true]
  refine ⟨h.1, List.all_eq_true.2 fun U hU => List.all_eq_true.2 fun V hV => ?_⟩
  have k := List.all_eq_true.1 (List.all_eq_true.1 h.2 U hU) V hV
  rw [Bool.or_eq_true] at k
  rw [Bool.or_eq_true, Bool.not_eq_true']
  rcases k with k | k
  · exact Or.inl (ncommN_sound k)
  · exact Or.inr (proptoD_of U V k)

theorem dN_of (h : dN2 = true) : dN = true := by
  unfold dN2 at h
  have h1 := dCheckOneN_of _ h
  have hde : toQ (matN [1, 0, 0, 0, 1, 0, 0, 0, 8]) * toQ (matN [1, 0, 0, 0, 1, 0, 0, 0, 8]) =
      toQ (matN [1, 0, 0, 0, 1, 0, 0, 0, 9]) :=
    (toQ_mMul _ _).symm.trans (congrArg toQ (FK.mEq_sound (by decide +kernel)))
  have hed : toQ (matN [1, 0, 0, 0, 1, 0, 0, 0, 9]) * toQ (matN [1, 0, 0, 0, 1, 0, 0, 0, 9]) =
      toQ (matN [1, 0, 0, 0, 1, 0, 0, 0, 8]) :=
    (toQ_mMul _ _).symm.trans (congrArg toQ (FK.mEq_sound (by decide +kernel)))
  have h2 := dCheckOne_sq hde hed (by rw [dCheckOne_eq]; exact h1)
  rw [dCheckOne_eq] at h2
  unfold dN
  rw [h1, h2]
  rfl

end CertificateChecks.KSU38RK
