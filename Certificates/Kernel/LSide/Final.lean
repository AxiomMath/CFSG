module

public import Certificates.Kernel.LSide.Checks
public import Certificates.Kernel.Sp6A2.Final

public section

namespace CFSG.KD.LSide

open CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.KD.Sp6A2 CFSG.KC.Sp6A2 CFSG.KC.Loop CFSG.Quasithin.G2U
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
  CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData

theorem letL_eq (y : ℕ) (k : ℕ → Bool) : letL y k = k y := by cases y <;> rfl

theorem allNL_iff (m : ℕ) (f : ℕ → Bool) : allNL m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ m ih =>
    have e : allNL (m + 1) f = (f m && allNL m f) := by
      change Bool.rec (motive := fun _ => Bool) false (allNL m f) (f m) = _
      cases f m <;> rfl
    rw [e, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      · exact h2 i h
      · exact h1
    · intro h
      exact ⟨h m (Nat.lt_succ_self m), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem beq_num {a b : List ℕ} {A B : ℕ} (ha : canon6 a = true ∧ pk a = A)
    (hb : canon6 b = true ∧ pk b = B) : (a == b) = Nat.beq A B := by
  rw [beq_pk ha.1 hb.1, ha.2, hb.2]

theorem comm_num {a b : List ℕ} {A B : ℕ} (ha : canon6 a = true ∧ pk a = A)
    (hb : canon6 b = true ∧ pk b = B) : commutes6 a b = Nat.beq (MULF A B) (MULF B A) := by
  unfold commutes6
  exact beq_num (mulE ha hb) (mulE hb ha)

theorem sig_c : canon6 lsSig = true := by decide +kernel

theorem x2p_c : canon6 lsX2p = true := by decide +kernel

theorem z_pk (i : Fin 3) : canon6 (zCode i) = true ∧ pk (zCode i) = pk (zCode i) :=
  ⟨zc_ok i, rfl⟩

theorem sigK_pk (k : ℕ) : canon6 (lsSigK k) = true ∧ pk (lsSigK k) = sigK (pk (zCode 0)) (pk lsSig) k :=
  mulE (mulE (powCode_pk (z_pk 0) k) ⟨sig_c, rfl⟩) (powCode_pk (z_pk 0) (3 - k))

theorem v_pk : canon6 lsV = true ∧ pk lsV = VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) 1 2 0 :=
  vecCode_pk zc_ok 1 2 0

theorem vi_pk :
    canon6 lsVInv = true ∧ pk lsVInv = VC (pk (zCode 0)) (pk (zCode 1)) (pk (zCode 2)) 2 1 0 :=
  vecCode_pk zc_ok 2 1 0

theorem adm_part : admCheck = true := by
  have hC := cz3_799751
  have h := ch799750_adm
  unfold admK at h
  simp only [letL_eq] at h
  unfold admCheck
  refine CFSG.KC.G2Three.allCheck_of fun t ht => ?_
  rw [hC.1] at ht
  have hx := hC.2 t ht
  have ht' := (allNL_iff _ _).1 h t ht
  unfold admP at ht'
  unfold lsAdm
  rw [beq_num (mulE hx hx) one_pk, comm_num hx (z_pk 2), beq_num (mulE hx v_pk) (mulE vi_pk hx),
    beq_num hx (sigK_pk 0), beq_num hx (sigK_pk 1), beq_num hx (sigK_pk 2)]
  exact ht'

theorem count3 {E : Array (List ℕ)} {R : ℕ → ℕ} {o n hi A B C : ℕ} {a b c : List ℕ}
    (hE : E.size = n)
    (hr : ∀ t < n, canon6 (E.getD t []) = true ∧ pk (E.getD t []) = recX R o t)
    (ha : canon6 a = true ∧ pk a = A) (hb : canon6 b = true ∧ pk b = B)
    (hc : canon6 c = true ∧ pk c = C) (hm : n ≤ 64 * hi) :
    CFSG.RankThree.PartTwo.Sec21.FF81.Am6.LSideData.countP
      (fun y => commutes6 y a && commutes6 y b && commutes6 y c) E =
      cnt3K R o n A B C hi := by
  rw [countP_range, hE, cnt3K, sumBelow_eq_sum n hi _ hm]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hx := hr t (Finset.mem_range.1 ht)
  rw [nIf_eq', comm_num hx ha, comm_num hx hb, comm_num hx hc]
  rfl

theorem count_part : countCheck = true := by
  have hC := cz4_799751
  unfold countCheck
  rw [countP_comm (hi := 2) hC.1 hC.2 ⟨sig_c, rfl⟩ (by norm_num),
    count3 (hi := 2) hC.1 hC.2 ⟨sig_c, rfl⟩ (z_pk 2) ⟨x2p_c, rfl⟩ (by norm_num), Bool.and_eq_true,
    beq_iff_eq, beq_iff_eq]
  exact ⟨Nat.eq_of_beq_eq_true ch799750_c1, Nat.eq_of_beq_eq_true ch799750_c2⟩

theorem frameOne_of {p₁ p₂ p₃ : Fin 3} {a₁ a₂ a₃ : ℕ} (h : frameK p₁ p₂ p₃ a₁ a₂ a₃ = true) :
    frameOne p₁ p₂ p₃ a₁ a₂ a₃ = true := by
  unfold frameK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨hp, h1⟩, h2⟩, h3⟩ := h
  have hpt := hp
  unfold pairT at hpt
  simp only [Bool.and_eq_true] at hpt
  obtain ⟨⟨⟨cR, cRI⟩, -⟩, -⟩ := hpt
  have eR : canon6 (rhoC p₁ p₂ p₃ a₁ a₂ a₃) = true ∧
      pk (rhoC p₁ p₂ p₃ a₁ a₂ a₃) = pk (rhoC p₁ p₂ p₃ a₁ a₂ a₃) := ⟨cR, rfl⟩
  have eRI : canon6 (rhoIC p₁ p₂ p₃ a₁ a₂ a₃) = true ∧
      pk (rhoIC p₁ p₂ p₃ a₁ a₂ a₃) = pk (rhoIC p₁ p₂ p₃ a₁ a₂ a₃) := ⟨cRI, rfl⟩
  unfold frameOne
  rw [pairCheck_of hp, beq_num (mulE (mulE eR (powCode_pk (z_pk p₁) a₁)) eRI) (z_pk 2),
    beq_num (mulE (mulE eR (powCode_pk (z_pk p₂) a₂)) eRI) (z_pk 0),
    beq_num (mulE (mulE eR (powCode_pk (z_pk p₃) a₃)) eRI) (z_pk 1), h1, h2, h3]
  rfl

theorem frame_part : frameCheck = true := by
  have h := ch799750_frame
  unfold frameCheckK at h
  unfold frameCheck
  simp only [List.all_eq_true] at h ⊢
  intro p₁ hp₁ p₂ hp₂ p₃ hp₃ a₁ ha₁ a₂ ha₂ a₃ ha₃
  have e := h p₁ hp₁ p₂ hp₂ p₃ hp₃ a₁ ha₁ a₂ ha₂ a₃ ha₃
  rw [Bool.or_eq_true] at e ⊢
  exact e.imp id frameOne_of

theorem lside_ok : lsideCheck = true := by
  unfold lsideCheck
  rw [adm_part, count_part, frame_part]
  rfl

end CFSG.KD.LSide

end
