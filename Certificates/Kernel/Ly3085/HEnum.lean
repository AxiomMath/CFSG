
module

public import Certificates.Kernel.Ly3085.FiberGlue
public import Certificates.Kernel.Ly3085.Omega.SmallK
public import CFSG.Certificates.Kernel.LyOmega.SpanCount
public import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CFSG.KD.LyH2

#kc_forall_tree leavesOK (fun b => CFSG.KC.LyOm.sLeaf SC KX PT KS m n b = true) 95 CFSG.KD.LyH2.h2

#kc_forall_tree countsOK (fun b => CFSG.KC.LyOm.sCountRange SC KX CT n b 1 = true) 95
  CFSG.KD.LyH2.h2c

theorem n_eq : n = 6048 := by decide +kernel

theorem nl_eq : nl = 95 := by decide +kernel

end CFSG.KD.LyH2

namespace CFSG.KD.LyH3

#kc_forall_tree leavesOK (fun b => CFSG.KC.LyOm.sLeaf SC KX PT KS m n b = true) 45 CFSG.KD.LyH3.h3

#kc_forall_tree countsOK (fun b => CFSG.KC.LyOm.sCountRange SC KX CT n b 1 = true) 45
  CFSG.KD.LyH3.h3c

theorem n_eq : n = 2880 := by decide +kernel

theorem nl_eq : nl = 45 := by decide +kernel

end CFSG.KD.LyH3

namespace CFSG.KD.LyH4

#kc_forall_tree leavesOK (fun b => CFSG.KC.LyOm.sLeaf SC KX PT KS m n b = true) 16 CFSG.KD.LyH4.h4

#kc_forall_tree countsOK (fun b => CFSG.KC.LyOm.sCountRange SC KX CT n b 1 = true) 16
  CFSG.KD.LyH4.h4c

theorem n_eq : n = 1008 := by decide +kernel

theorem nl_eq : nl = 16 := by decide +kernel

end CFSG.KD.LyH4

noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm CFSG.KC.LyOm CFSG.KC.LL CFSG.KC.Loop
open Matrix MulAction

@[expose] def cls (k : ℕ) (X : Matrix (Fin 7) (Fin 7) (ZMod 5)) : Prop :=
  if k = 0 then X ^ 2 = 1 ∧ X ≠ 1
  else if k = 1 then X ^ 3 = 1 ∧ X ≠ 1 ∧ X.trace = 1
  else if k = 2 then X ^ 5 = 1 ∧ X ≠ 1 ∧ (X - 1) ^ 2 = 0
  else X ^ 5 = 1 ∧ X ≠ 1 ∧ 2 ≤ ((X - 1) ^ 2).rank

open scoped Classical in
theorem sClass_cls {X : ℕ} (hX : LCanon 11 7 7 X) :
    sClass CFSG.KD.LyOm.SC X = (if cls 0 (smM X) then 1 else 0) +
      (if cls 1 (smM X) then 2 ^ 16 else 0) + (if cls 2 (smM X) then 2 ^ 32 else 0) +
      (if cls 3 (smM X) then 2 ^ 48 else 0) := by
  rw [sClass_sound hSC hX]
  simp only [cls]
  norm_num

theorem cls_conj (k : ℕ) {R X : Matrix (Fin 7) (Fin 7) (ZMod 5)} (hR : IsUnit R.det)
    (h : cls k X) : cls k (R * X * R⁻¹) := by
  have hRR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hR
  have hRR' : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv R hR
  have hpow : ∀ e : ℕ, (R * X * R⁻¹) ^ e = R * X ^ e * R⁻¹ := by
    intro e
    induction e with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one, hRR']
    | succ e ih =>
      rw [pow_succ, ih, pow_succ]
      calc R * X ^ e * R⁻¹ * (R * X * R⁻¹) = R * X ^ e * (R⁻¹ * R) * X * R⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = R * (X ^ e * X) * R⁻¹ := by rw [hRR, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hne : X ≠ 1 → R * X * R⁻¹ ≠ 1 := by
    intro hX e
    apply hX
    calc X = R⁻¹ * (R * X * R⁻¹) * R := by
          simp only [← Matrix.mul_assoc]
          rw [hRR, Matrix.one_mul, Matrix.mul_assoc, hRR, Matrix.mul_one]
      _ = 1 := by rw [e, Matrix.mul_one, hRR]
  have hsub : R * X * R⁻¹ - 1 = R * (X - 1) * R⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hRR']
  have hsq : (R * X * R⁻¹ - 1) ^ 2 = R * (X - 1) ^ 2 * R⁻¹ := by
    rw [hsub, sq, sq]
    calc R * (X - 1) * R⁻¹ * (R * (X - 1) * R⁻¹) = R * (X - 1) * (R⁻¹ * R) * (X - 1) * R⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = R * ((X - 1) * (X - 1)) * R⁻¹ := by rw [hRR, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hRi : IsUnit R⁻¹.det := by
    rw [Matrix.det_nonsing_inv]
    exact hR.ringInverse
  unfold cls at h ⊢
  by_cases k0 : k = 0
  · simp only [k0, if_true] at h ⊢
    exact ⟨by rw [hpow, h.1, Matrix.mul_one, hRR'], hne h.2⟩
  simp only [k0, if_false] at h ⊢
  by_cases k1 : k = 1
  · simp only [k1, if_true] at h ⊢
    refine ⟨by rw [hpow, h.1, Matrix.mul_one, hRR'], hne h.2.1, ?_⟩
    rw [Matrix.trace_mul_cycle, hRR, Matrix.one_mul]
    exact h.2.2
  simp only [k1, if_false] at h ⊢
  by_cases k2 : k = 2
  · simp only [k2, if_true] at h ⊢
    refine ⟨by rw [hpow, h.1, Matrix.mul_one, hRR'], hne h.2.1, ?_⟩
    rw [hsq, h.2.2, Matrix.mul_zero, Matrix.zero_mul]
  simp only [k2, if_false] at h ⊢
  refine ⟨by rw [hpow, h.1, Matrix.mul_one, hRR'], hne h.2.1, ?_⟩
  rw [hsq, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hRi,
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hR]
  exact h.2.2

theorem cls_of_isConj
    [LySeed] (k : ℕ) {t h : lyH} (hc : IsConj t h)
    (ht : cls k (restr7 (t : J))) : cls k (restr7 (h : J)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  have hcS := lyH_le_stabU c.2
  have htS := lyH_le_stabU t.2
  have e : restr7 ((c * t * c⁻¹ : lyH) : J) = restr7 (c : J) * restr7 (t : J) * (restr7 (c : J))⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [restr7_mul (stabU.mul_mem hcS htS) (stabU.inv_mem hcS), restr7_mul hcS htS,
      restr7_inv hcS]
  rw [e]
  refine cls_conj k ?_ ht
  have e1 : restr7 (c : J) * restr7 (c : J)⁻¹ = 1 := restr7_mul_inv hcS
  exact Matrix.isUnit_det_of_right_inverse e1

theorem fm_kron2 {X Y K A B : ℕ} (hK : ∀ i j k l : Fin 7,
      kM K ⟨7 * i + j, by omega⟩ ⟨7 * k + l, by omega⟩ = smM A i k * smM B j l)
    (h : vec49 Y = Matrix.vecMul (vec49 X) (kM K)) : (fm Y).M = (smM A)ᵀ * (fm X).M * smM B := by
  ext a b
  simp only [fm, Matrix.of_apply]
  rw [h, Matrix.vecMul, dotProduct]
  rw [← (finProdFinEquiv (m := 7) (n := 7)).sum_comp, Fintype.sum_prod_type]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have e1 : (⟨7 * i.val + j.val, by omega⟩ : Fin 49) = finProdFinEquiv (i, j) := by
    ext
    rw [finProdFinEquiv_apply_val]
    simp only
    ring
  have hK' := hK i j a b
  rw [e1] at hK'
  rw [hK']
  simp only [Matrix.of_apply]
  rw [e1]
  ring

theorem canon_sq {X : ℕ} (h : LCanon 11 1 49 X) : LCanon 11 7 7 X := by
  refine ⟨by rw [show 11 * 7 * 7 = 11 * 49 * 1 by norm_num]; exact h.1, fun i hi j hj => ?_⟩
  have := h.2 0 (by norm_num) (7 * i + j) (by omega)
  have e : 11 * 49 * 0 + 11 * (7 * i + j) = 11 * 7 * i + 11 * j := by ring
  rwa [e] at this

theorem hMaps_rec {KS : List ℕ} : ∀ (ws : List (List ℕ)) (k₀ : ℕ),
    (List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
      (fun w _ ih k => bAnd(kronOK CFSG.KD.LyOm.SC.ONE
        (sWord CFSG.KD.LyOm.SC CFSG.KD.LyOm.GR2 CFSG.KD.LyOm.SC.ONE w) (pickL KS k),
        ih (Nat.succ k))) ws) k₀ = true →
    ∀ k < ws.length, kronOK CFSG.KD.LyOm.SC.ONE
      (sWord CFSG.KD.LyOm.SC CFSG.KD.LyOm.GR2 CFSG.KD.LyOm.SC.ONE (ws.getD k [])) (pickL KS (k₀ + k)) =
        true
  | [], _, _ => fun k hk => absurd hk (Nat.not_lt_zero _)
  | w :: ws, k₀, h => by
    obtain ⟨h1, h2⟩ := bAnd_true h
    intro k hk
    rcases k with _ | k
    · exact h1
    · have := hMaps_rec ws (Nat.succ k₀) h2 k (by simpa using hk)
      rw [show k₀ + (k + 1) = Nat.succ k₀ + k by omega]
      exact this

theorem hMaps_sound {KS : List ℕ} {m : ℕ} {ws : List (List ℕ)}
    (h : CFSG.KD.LyOm.hMaps KS m ws = true) :
    m = ws.length ∧ ∀ k < ws.length, kronOK CFSG.KD.LyOm.SC.ONE
      (sWord CFSG.KD.LyOm.SC CFSG.KD.LyOm.GR2 CFSG.KD.LyOm.SC.ONE (ws.getD k [])) (pickL KS k) =
        true := by
  unfold CFSG.KD.LyOm.hMaps at h
  obtain ⟨h1, h2⟩ := bAnd_true h
  refine ⟨beq_eq h1, fun k hk => ?_⟩
  have := hMaps_rec ws 0 h2 k hk
  rwa [Nat.zero_add] at this

theorem enum_tree
    [LySeed] {KX PT SG : ℕ → ℕ} {KS : List ℕ} {m n nl : ℕ}
    {ws : List (List ℕ)} (K : Subgroup lyH)
    (hws : ∀ k < ws.length, (∀ l ∈ ws.getD k [], l < 4) ∧
      (⟨wordJ (ws.getD k []), wordJ_mem _⟩ : lyH) ∈ K)
    (hmaps : CFSG.KD.LyOm.hMaps KS m ws = true) (hroot : getRec KX 539 0 = CFSG.KD.LyOm.SC.ONE)
    (hnl : n ≤ 64 * nl) (hleaf : ∀ b < nl, sLeaf CFSG.KD.LyOm.SC KX PT KS m n b = true)
    (hsg : ∀ k < n, getRec SG 20 k < n)
    (hsort : ∀ k, k + 1 < n → getRec KX 539 (getRec SG 20 k) < getRec KX 539 (getRec SG 20 (k + 1))) :
    (∀ i < n, LCanon 11 7 7 (getRec KX 539 i) ∧ ∃ k ∈ K, smM (getRec KX 539 i) = restr7 (k : J)) ∧
      (∀ i < n, ∀ j < n, smM (getRec KX 539 i) = smM (getRec KX 539 j) → i = j) := by
  obtain ⟨hm, hkr⟩ := hMaps_sound hmaps
  have eGR : CFSG.KD.LyOm.GR2 = CFSG.KD.LyY.GR := rfl
  have hKs : ∀ s < m, LCanon 11 49 49 (pickL KS s) ∧ ∀ X Y : ℕ,
      vec49 Y = Matrix.vecMul (vec49 X) (kM (pickL KS s)) →
      (fm Y).M = (fm X).M * restr7 (wordJ (ws.getD s [])) := by
    intro s hs
    rw [hm] at hs
    obtain ⟨cK, eK⟩ := kronOK_sound (hkr s hs)
    obtain ⟨-, eQ⟩ := restr7_wordJ (hws s hs).1
    refine ⟨cK, fun X Y hXY => ?_⟩
    rw [fm_kron2 eK hXY, smM_one, Matrix.transpose_one, Matrix.one_mul, eGR, eQ]
  have hnode : ∀ i < n, 0 < i → _ := fun i hi hi0 =>
    sLeaf_sound hSC (fun s hs => (hKs s hs).1) (hleaf (i / 64) (by omega)) (r := i % 64)
      (Nat.mod_lt _ (by norm_num)) (by omega) (by omega)
  have e64 : ∀ i, 64 * (i / 64) + i % 64 = i := fun i => by omega
  have hcan : ∀ i < n, LCanon 11 1 49 (getRec KX 539 i) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rw [hroot]
        exact canon_row canon_one
      · have := (hnode i hi hpos).2.2 (by
          rw [e64]
          exact fun j hj => ih j hj (by omega))
        rw [e64] at this
        exact this.1
  have hmem : ∀ i < n, ∃ k ∈ K, (fm (getRec KX 539 i)).M = restr7 (k : J) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · refine ⟨1, K.one_mem, ?_⟩
        rw [hroot, fm_smM, smM_one, Subgroup.coe_one, restr7_one]
      · have h := hnode i hi hpos
        rw [e64] at h
        obtain ⟨hp, hl, hv⟩ := h
        obtain ⟨-, e⟩ := hv (fun j hj => hcan j (by omega))
        obtain ⟨k, hk, ek⟩ := ih _ hp (by omega)
        have hs := (hws _ (by rw [← hm]; exact hl)).2
        refine ⟨k * ⟨_, wordJ_mem _⟩, K.mul_mem hk hs, ?_⟩
        rw [(hKs _ hl).2 _ _ e, ek, Subgroup.coe_mul,
          restr7_mul (lyH_le_stabU k.2) (lyH_le_stabU (wordJ_mem _))]
  refine ⟨fun i hi => ⟨canon_sq (hcan i hi), ?_⟩, fun i hi j hj e => ?_⟩
  · obtain ⟨k, hk, ek⟩ := hmem i hi
    exact ⟨k, hk, by rw [← fm_smM, ek]⟩
  · refine sorted_inj (getRec KX 539) (fun k => getRec SG 20 k) hsg hsort i hi j hj ?_
    exact smM_inj (canon_sq (hcan i hi)) (canon_sq (hcan j hj)) e

theorem enum_count
    [LySeed] {n : ℕ} (K : Subgroup lyH) (key : ℕ → ℕ)
    (hmem : ∀ i < n, ∃ k ∈ K, smM (key i) = restr7 (k : J))
    (hinj : ∀ i < n, ∀ j < n, smM (key i) = smM (key j) → i = j)
    (hK : Nat.card K ≤ n) (P : Matrix (Fin 7) (Fin 7) (ZMod 5) → Prop) :
    Nat.card {h : lyH // h ∈ K ∧ P (restr7 (h : J))} =
      Nat.card {i : Fin n // P (smM (key i.val))} := by
  have hc : ∀ i : Fin n, ∃ k : K, smM (key i.val) = restr7 ((k : lyH) : J) := fun i => by
    obtain ⟨k, hk, e⟩ := hmem i.val i.2
    exact ⟨⟨k, hk⟩, e⟩
  choose f hf using hc
  have hfi : Function.Injective f := by
    intro i j e
    exact Fin.ext (hinj i.val i.2 j.val j.2 (by rw [hf, hf, e]))
  have hK' : Nat.card K ≤ Nat.card (Fin n) := by
    rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]
    exact hK
  have hb : Function.Bijective f := hfi.bijective_of_nat_card_le hK'
  have e1 : {i : Fin n // P (smM (key i.val))} ≃ {k : K // P (restr7 ((k : lyH) : J))} :=
    Equiv.subtypeEquiv (Equiv.ofBijective f hb) fun i => by
      change P (smM (key i.val)) ↔ P (restr7 ((f i : lyH) : J))
      rw [hf]
  have e2 : {k : K // P (restr7 ((k : lyH) : J))} ≃ {h : lyH // h ∈ K ∧ P (restr7 (h : J))} :=
    Equiv.subtypeSubtypeEquivSubtypeInter (fun h : lyH => h ∈ K) (fun h : lyH => P (restr7 (h : J)))
  exact (Nat.card_congr (e1.trans e2)).symm

theorem card_fin_filter {n : ℕ} (P : ℕ → Prop) [DecidablePred P] :
    Nat.card {i : Fin n // P i.val} = ((Finset.range n).filter P).card := by
  have e : {i : Fin n // P i.val} ≃ (((Finset.range n).filter P : Finset ℕ) : Set ℕ) :=
    { toFun := fun i => ⟨i.1.1, by simp [i.1.2, i.2]⟩
      invFun := fun j => ⟨⟨j.1, by have := j.2; simp at this; exact this.1⟩,
        by have := j.2; simp at this; exact this.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem sum_leaves (n nl : ℕ) (hnl : n ≤ 64 * nl) (f : ℕ → ℕ) :
    ∑ b ∈ Finset.range nl, ∑ r ∈ (Finset.range 64).filter (fun r => 64 * b + r < n), f (64 * b + r) =
      ∑ i ∈ Finset.range n, f i := by
  have h1 : ∀ k, ∑ b ∈ Finset.range k, ∑ r ∈ (Finset.range 64).filter (fun r => 64 * b + r < n),
      f (64 * b + r) = ∑ i ∈ Finset.range (64 * k), if i < n then f i else 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add, Finset.sum_filter]
  rw [h1, show 64 * nl = n + (64 * nl - n) by omega, Finset.sum_range_add,
    Finset.sum_eq_zero (s := Finset.range (64 * nl - n)) (fun i _ => if_neg (by omega)), Nat.add_zero]
  exact Finset.sum_congr rfl fun i hi => if_pos (Finset.mem_range.1 hi)

theorem sum_ite_pow (s : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (c : ℕ) :
    ∑ i ∈ s, (if P i then c else 0) = c * (s.filter P).card := by
  rw [Finset.sum_ite, Finset.sum_const_zero, Nat.add_zero, Finset.sum_const, smul_eq_mul,
    Nat.mul_comm]

theorem class_counts {KX CT : ℕ → ℕ} {n nl : ℕ} (hnl : n ≤ 64 * nl)
    (hcan : ∀ i < n, LCanon 11 7 7 (getRec KX 539 i))
    (hct : ∀ b < nl, sCountRange CFSG.KD.LyOm.SC KX CT n b 1 = true) :
    sCountSum CT nl = Nat.card {i : Fin n // cls 0 (smM (getRec KX 539 i.val))} +
      65536 * Nat.card {i : Fin n // cls 1 (smM (getRec KX 539 i.val))} +
      4294967296 * Nat.card {i : Fin n // cls 2 (smM (getRec KX 539 i.val))} +
      281474976710656 * Nat.card {i : Fin n // cls 3 (smM (getRec KX 539 i.val))} := by
  classical
  rw [card_fin_filter (fun x => cls 0 (smM (getRec KX 539 x))),
    card_fin_filter (fun x => cls 1 (smM (getRec KX 539 x))),
    card_fin_filter (fun x => cls 2 (smM (getRec KX 539 x))),
    card_fin_filter (fun x => cls 3 (smM (getRec KX 539 x))), SpanC.sCountSum_eq]
  have h1 : ∀ b < nl, getRec CT 64 b = sCountLeaf CFSG.KD.LyOm.SC KX n b := fun b hb => by
    have := SpanC.sCountRange_sound (hct b hb) 0 (by norm_num)
    rw [Nat.add_zero] at this
    exact this.symm
  rw [Finset.sum_congr rfl fun b hb => h1 b (Finset.mem_range.1 hb)]
  simp only [sCountLeaf_eq]
  rw [sum_leaves n nl hnl (fun i => sClass CFSG.KD.LyOm.SC (getRec KX 539 i)),
    Finset.sum_congr rfl fun i hi => sClass_cls (hcan i (Finset.mem_range.1 hi))]
  simp only [Finset.sum_add_distrib]
  rw [sum_ite_pow, sum_ite_pow, sum_ite_pow, sum_ite_pow]
  norm_num

theorem wh_lt : (∀ l ∈ CFSG.KD.LyOm.WH2_0, l < 4) ∧ (∀ l ∈ CFSG.KD.LyOm.WH2_1, l < 4) ∧
    (∀ l ∈ CFSG.KD.LyOm.WH3_0, l < 4) ∧ (∀ l ∈ CFSG.KD.LyOm.WH3_1, l < 4) ∧
    (∀ l ∈ CFSG.KD.LyOm.WH3_2, l < 4) ∧ (∀ l ∈ CFSG.KD.LyOm.WH4_0, l < 4) ∧
    (∀ l ∈ CFSG.KD.LyOm.WH4_1, l < 4) ∧ (∀ l ∈ CFSG.KD.LyOm.WH4_2, l < 4) ∧
    (∀ l ∈ CFSG.KD.LyOm.WH4_3, l < 4) := by decide +kernel

theorem h2_counts
    [LySeed] (K : Subgroup lyH)
    (h0 : (⟨wordJ CFSG.KD.LyOm.WH2_0, wordJ_mem _⟩ : lyH) ∈ K)
    (h1 : (⟨wordJ CFSG.KD.LyOm.WH2_1, wordJ_mem _⟩ : lyH) ∈ K) (hK : Nat.card K ≤ 6048) :
    Nat.card {h : lyH // h ∈ K ∧ cls 0 (restr7 (h : J))} = 63 ∧
      Nat.card {h : lyH // h ∈ K ∧ cls 1 (restr7 (h : J))} = 672 ∧
      Nat.card {h : lyH // h ∈ K ∧ cls 2 (restr7 (h : J))} = 0 ∧
      Nat.card {h : lyH // h ∈ K ∧ cls 3 (restr7 (h : J))} = 0 := by
  obtain ⟨l0, l1, -⟩ := wh_lt
  have hb := CFSG.KD.LyOm.h2
  generalize hr0 : getRec CFSG.KD.LyH2.KX 539 0 = r0 at hb
  generalize hm0 : CFSG.KD.LyOm.hMaps CFSG.KD.LyH2.KS CFSG.KD.LyH2.m
    [CFSG.KD.LyOm.WH2_0, CFSG.KD.LyOm.WH2_1] = mb at hb
  generalize hone : CFSG.KD.LyOm.SC.ONE = one at hb
  obtain ⟨hm1, hr⟩ := bAnd_true hb
  have hmaps : CFSG.KD.LyOm.hMaps CFSG.KD.LyH2.KS CFSG.KD.LyH2.m
      [CFSG.KD.LyOm.WH2_0, CFSG.KD.LyOm.WH2_1] = true := by rw [hm0]; exact hm1
  subst hone
  have hroot : getRec CFSG.KD.LyH2.KX 539 0 = CFSG.KD.LyOm.SC.ONE := by rw [hr0]; exact beq_eq hr
  have hn := CFSG.KD.LyH2.n_eq
  have hnl : CFSG.KD.LyH2.n ≤ 64 * CFSG.KD.LyH2.nl := by rw [hn, CFSG.KD.LyH2.nl_eq]; norm_num
  have hn' : CFSG.KD.LyH2.n ≤ 6048 := hn.le
  obtain ⟨hA, hB⟩ := enum_tree (KX := CFSG.KD.LyH2.KX) (PT := CFSG.KD.LyH2.PT)
    (SG := CFSG.KD.LyH2.SG) (KS := CFSG.KD.LyH2.KS) (m := CFSG.KD.LyH2.m) (n := CFSG.KD.LyH2.n)
    (nl := CFSG.KD.LyH2.nl) (ws := [CFSG.KD.LyOm.WH2_0, CFSG.KD.LyOm.WH2_1]) K
    (fun k hk => by
      change k < 2 at hk
      interval_cases k
      · exact ⟨l0, h0⟩
      · exact ⟨l1, h1⟩) hmaps hroot hnl
    (fun b hb => CFSG.KD.LyH2.leavesOK b (by rw [CFSG.KD.LyH2.nl_eq] at hb; change b < 95; exact hb))
    (fun k hk => by
      have hk' := hk
      rw [hn] at hk'
      by_cases hl : k < 4096
      · exact (sSort_sound CFSG.KD.LyH2.h2s0 k (by change 0 ≤ k; omega)
          (by change k < 0 + 4096; omega)).1
      · by_cases hm' : k < 6047
        · exact (sSort_sound CFSG.KD.LyH2.h2s1 k (by change 4096 ≤ k; omega)
            (by change k < 4096 + 1951; omega)).1
        · have : k = 6046 + 1 := by omega
          rw [this]
          exact (sSort_sound CFSG.KD.LyH2.h2s1 6046 (by change 4096 ≤ 6046; omega)
            (by change 6046 < 4096 + 1951; omega)).2.1)
    (fun k hk => by
      rw [hn] at hk
      by_cases hl : k < 4096
      · exact (sSort_sound CFSG.KD.LyH2.h2s0 k (by change 0 ≤ k; omega)
          (by change k < 0 + 4096; omega)).2.2
      · exact (sSort_sound CFSG.KD.LyH2.h2s1 k (by change 4096 ≤ k; omega)
          (by change k < 4096 + 1951; omega)).2.2)
  have hc := class_counts (CT := CFSG.KD.LyH2.CT) hnl (fun i hi => (hA i hi).1)
    (fun b hb => CFSG.KD.LyH2.countsOK b (by rw [CFSG.KD.LyH2.nl_eq] at hb; change b < 95; exact hb))
  have hT : sCountSum CFSG.KD.LyH2.CT CFSG.KD.LyH2.nl = 44040255 := beq_eq CFSG.KD.LyH2.h2cs
  rw [hT] at hc
  have hcnt := fun P => enum_count (n := CFSG.KD.LyH2.n) K (getRec CFSG.KD.LyH2.KX 539)
    (fun i hi => (hA i hi).2) hB (by omega) P
  have b0 := Finite.card_subtype_le (fun i : Fin CFSG.KD.LyH2.n =>
    cls 0 (smM (getRec CFSG.KD.LyH2.KX 539 i.val)))
  have b1 := Finite.card_subtype_le (fun i : Fin CFSG.KD.LyH2.n =>
    cls 1 (smM (getRec CFSG.KD.LyH2.KX 539 i.val)))
  have b2 := Finite.card_subtype_le (fun i : Fin CFSG.KD.LyH2.n =>
    cls 2 (smM (getRec CFSG.KD.LyH2.KX 539 i.val)))
  have b3 := Finite.card_subtype_le (fun i : Fin CFSG.KD.LyH2.n =>
    cls 3 (smM (getRec CFSG.KD.LyH2.KX 539 i.val)))
  rw [Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at b0 b1 b2 b3
  rw [hcnt, hcnt, hcnt, hcnt]
  omega

theorem h3_counts
    [LySeed] (K : Subgroup lyH)
    (h0 : (⟨wordJ CFSG.KD.LyOm.WH3_0, wordJ_mem _⟩ : lyH) ∈ K)
    (h1 : (⟨wordJ CFSG.KD.LyOm.WH3_1, wordJ_mem _⟩ : lyH) ∈ K)
    (h2 : (⟨wordJ CFSG.KD.LyOm.WH3_2, wordJ_mem _⟩ : lyH) ∈ K) (hK : Nat.card K ≤ 2880) :
    Nat.card {h : lyH // h ∈ K ∧ cls 0 (restr7 (h : J))} = 211 ∧
      Nat.card {h : lyH // h ∈ K ∧ cls 1 (restr7 (h : J))} = 168 ∧
      Nat.card {h : lyH // h ∈ K ∧ cls 2 (restr7 (h : J))} = 0 ∧
      Nat.card {h : lyH // h ∈ K ∧ cls 3 (restr7 (h : J))} = 0 := by
  obtain ⟨-, -, l0, l1, l2, -⟩ := wh_lt
  have hb := CFSG.KD.LyOm.h3
  generalize hr0 : getRec CFSG.KD.LyH3.KX 539 0 = r0 at hb
  generalize hm0 : CFSG.KD.LyOm.hMaps CFSG.KD.LyH3.KS CFSG.KD.LyH3.m
    [CFSG.KD.LyOm.WH3_0, CFSG.KD.LyOm.WH3_1, CFSG.KD.LyOm.WH3_2] = mb at hb
  generalize hone : CFSG.KD.LyOm.SC.ONE = one at hb
  obtain ⟨hm1, hr⟩ := bAnd_true hb
  have hmaps : CFSG.KD.LyOm.hMaps CFSG.KD.LyH3.KS CFSG.KD.LyH3.m
      [CFSG.KD.LyOm.WH3_0, CFSG.KD.LyOm.WH3_1, CFSG.KD.LyOm.WH3_2] = true := by rw [hm0]; exact hm1
  subst hone
  have hroot : getRec CFSG.KD.LyH3.KX 539 0 = CFSG.KD.LyOm.SC.ONE := by rw [hr0]; exact beq_eq hr
  have hn := CFSG.KD.LyH3.n_eq
  have hnl : CFSG.KD.LyH3.n ≤ 64 * CFSG.KD.LyH3.nl := by rw [hn, CFSG.KD.LyH3.nl_eq]; try norm_num
  obtain ⟨hA, hB⟩ := enum_tree (KX := CFSG.KD.LyH3.KX) (PT := CFSG.KD.LyH3.PT)
    (SG := CFSG.KD.LyH3.SG) (KS := CFSG.KD.LyH3.KS) (m := CFSG.KD.LyH3.m) (n := CFSG.KD.LyH3.n)
    (nl := CFSG.KD.LyH3.nl) (ws := [CFSG.KD.LyOm.WH3_0, CFSG.KD.LyOm.WH3_1, CFSG.KD.LyOm.WH3_2]) K
    (fun k hk => by
      change k < 3 at hk
      interval_cases k
      · exact ⟨l0, h0⟩
      · exact ⟨l1, h1⟩
      · exact ⟨l2, h2⟩) hmaps hroot hnl
    (fun b hb => CFSG.KD.LyH3.leavesOK b (by rw [CFSG.KD.LyH3.nl_eq] at hb; change b < 45; exact hb))
    (fun k hk => by
      have hk' := hk
      rw [hn] at hk'
      by_cases hm' : k < 2879
      · exact (sSort_sound CFSG.KD.LyH3.h3s0 k (by change 0 ≤ k; omega)
          (by change k < 0 + 2879; omega)).1
      · have : k = 2878 + 1 := by omega
        rw [this]
        exact (sSort_sound CFSG.KD.LyH3.h3s0 2878 (by change 0 ≤ 2878; omega)
          (by change 2878 < 0 + 2879; omega)).2.1)
    (fun k hk => by
      rw [hn] at hk
      exact (sSort_sound CFSG.KD.LyH3.h3s0 k (by change 0 ≤ k; omega)
        (by change k < 0 + 2879; omega)).2.2)
  have hc := class_counts (CT := CFSG.KD.LyH3.CT) hnl (fun i hi => (hA i hi).1)
    (fun b hb => CFSG.KD.LyH3.countsOK b (by rw [CFSG.KD.LyH3.nl_eq] at hb; change b < 45; exact hb))
  have hT : sCountSum CFSG.KD.LyH3.CT CFSG.KD.LyH3.nl = 11010259 := beq_eq CFSG.KD.LyH3.h3cs
  rw [hT] at hc
  have hcnt := fun P => enum_count (n := CFSG.KD.LyH3.n) K (getRec CFSG.KD.LyH3.KX 539)
    (fun i hi => (hA i hi).2) hB (by omega) P
  have b0 := Finite.card_subtype_le (fun i : Fin CFSG.KD.LyH3.n =>
    cls 0 (smM (getRec CFSG.KD.LyH3.KX 539 i.val)))
  have b1 := Finite.card_subtype_le (fun i : Fin CFSG.KD.LyH3.n =>
    cls 1 (smM (getRec CFSG.KD.LyH3.KX 539 i.val)))
  have b2 := Finite.card_subtype_le (fun i : Fin CFSG.KD.LyH3.n =>
    cls 2 (smM (getRec CFSG.KD.LyH3.KX 539 i.val)))
  have b3 := Finite.card_subtype_le (fun i : Fin CFSG.KD.LyH3.n =>
    cls 3 (smM (getRec CFSG.KD.LyH3.KX 539 i.val)))
  rw [Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at b0 b1 b2 b3
  rw [hcnt, hcnt, hcnt, hcnt]
  omega

theorem h4_counts
    [LySeed] (K : Subgroup lyH)
    (h0 : (⟨wordJ CFSG.KD.LyOm.WH4_0, wordJ_mem _⟩ : lyH) ∈ K)
    (h1 : (⟨wordJ CFSG.KD.LyOm.WH4_1, wordJ_mem _⟩ : lyH) ∈ K)
    (h2 : (⟨wordJ CFSG.KD.LyOm.WH4_2, wordJ_mem _⟩ : lyH) ∈ K)
    (h3 : (⟨wordJ CFSG.KD.LyOm.WH4_3, wordJ_mem _⟩ : lyH) ∈ K) (hK : Nat.card K ≤ 1008) :
    Nat.card {h : lyH // h ∈ K ∧ cls 0 (restr7 (h : J))} = 105 ∧
      Nat.card {h : lyH // h ∈ K ∧ cls 1 (restr7 (h : J))} = 168 ∧
      Nat.card {h : lyH // h ∈ K ∧ cls 2 (restr7 (h : J))} = 0 ∧
      Nat.card {h : lyH // h ∈ K ∧ cls 3 (restr7 (h : J))} = 0 := by
  obtain ⟨-, -, -, -, -, l0, l1, l2, l3⟩ := wh_lt
  have hb := CFSG.KD.LyOm.h4
  generalize hr0 : getRec CFSG.KD.LyH4.KX 539 0 = r0 at hb
  generalize hm0 : CFSG.KD.LyOm.hMaps CFSG.KD.LyH4.KS CFSG.KD.LyH4.m
    [CFSG.KD.LyOm.WH4_0, CFSG.KD.LyOm.WH4_1, CFSG.KD.LyOm.WH4_2, CFSG.KD.LyOm.WH4_3] = mb at hb
  generalize hone : CFSG.KD.LyOm.SC.ONE = one at hb
  obtain ⟨hm1, hr⟩ := bAnd_true hb
  have hmaps : CFSG.KD.LyOm.hMaps CFSG.KD.LyH4.KS CFSG.KD.LyH4.m
      [CFSG.KD.LyOm.WH4_0, CFSG.KD.LyOm.WH4_1, CFSG.KD.LyOm.WH4_2, CFSG.KD.LyOm.WH4_3] = true := by
    rw [hm0]; exact hm1
  subst hone
  have hroot : getRec CFSG.KD.LyH4.KX 539 0 = CFSG.KD.LyOm.SC.ONE := by rw [hr0]; exact beq_eq hr
  have hn := CFSG.KD.LyH4.n_eq
  have hnl : CFSG.KD.LyH4.n ≤ 64 * CFSG.KD.LyH4.nl := by rw [hn, CFSG.KD.LyH4.nl_eq]; try norm_num
  obtain ⟨hA, hB⟩ := enum_tree (KX := CFSG.KD.LyH4.KX) (PT := CFSG.KD.LyH4.PT)
    (SG := CFSG.KD.LyH4.SG) (KS := CFSG.KD.LyH4.KS) (m := CFSG.KD.LyH4.m) (n := CFSG.KD.LyH4.n)
    (nl := CFSG.KD.LyH4.nl)
    (ws := [CFSG.KD.LyOm.WH4_0, CFSG.KD.LyOm.WH4_1, CFSG.KD.LyOm.WH4_2, CFSG.KD.LyOm.WH4_3]) K
    (fun k hk => by
      change k < 4 at hk
      interval_cases k
      · exact ⟨l0, h0⟩
      · exact ⟨l1, h1⟩
      · exact ⟨l2, h2⟩
      · exact ⟨l3, h3⟩) hmaps hroot hnl
    (fun b hb => CFSG.KD.LyH4.leavesOK b (by rw [CFSG.KD.LyH4.nl_eq] at hb; change b < 16; exact hb))
    (fun k hk => by
      have hk' := hk
      rw [hn] at hk'
      by_cases hm' : k < 1007
      · exact (sSort_sound CFSG.KD.LyH4.h4s0 k (by change 0 ≤ k; omega)
          (by change k < 0 + 1007; omega)).1
      · have : k = 1006 + 1 := by omega
        rw [this]
        exact (sSort_sound CFSG.KD.LyH4.h4s0 1006 (by change 0 ≤ 1006; omega)
          (by change 1006 < 0 + 1007; omega)).2.1)
    (fun k hk => by
      rw [hn] at hk
      exact (sSort_sound CFSG.KD.LyH4.h4s0 k (by change 0 ≤ k; omega)
        (by change k < 0 + 1007; omega)).2.2)
  have hc := class_counts (CT := CFSG.KD.LyH4.CT) hnl (fun i hi => (hA i hi).1)
    (fun b hb => CFSG.KD.LyH4.countsOK b (by rw [CFSG.KD.LyH4.nl_eq] at hb; change b < 16; exact hb))
  have hT : sCountSum CFSG.KD.LyH4.CT CFSG.KD.LyH4.nl = 11010153 := beq_eq CFSG.KD.LyH4.h4cs
  rw [hT] at hc
  have hcnt := fun P => enum_count (n := CFSG.KD.LyH4.n) K (getRec CFSG.KD.LyH4.KX 539)
    (fun i hi => (hA i hi).2) hB (by omega) P
  have b0 := Finite.card_subtype_le (fun i : Fin CFSG.KD.LyH4.n =>
    cls 0 (smM (getRec CFSG.KD.LyH4.KX 539 i.val)))
  have b1 := Finite.card_subtype_le (fun i : Fin CFSG.KD.LyH4.n =>
    cls 1 (smM (getRec CFSG.KD.LyH4.KX 539 i.val)))
  have b2 := Finite.card_subtype_le (fun i : Fin CFSG.KD.LyH4.n =>
    cls 2 (smM (getRec CFSG.KD.LyH4.KX 539 i.val)))
  have b3 := Finite.card_subtype_le (fun i : Fin CFSG.KD.LyH4.n =>
    cls 3 (smM (getRec CFSG.KD.LyH4.KX 539 i.val)))
  rw [Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at b0 b1 b2 b3
  rw [hcnt, hcnt, hcnt, hcnt]
  omega

end CertificateChecks.KernelLy.Omega

end

end
