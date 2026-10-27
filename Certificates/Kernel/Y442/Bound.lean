module

public import Certificates.Kernel.Y442.Assembly
public import CFSG.Certificates.Kernel.TwistDce.Cover

public section

namespace CertificateChecks.KernelY442

open CFSG.YGroups CFSG.YGroups.Y442Tw CFSG.KC CFSG.KC.YModel CFSG.KC.TwDce
  CFSG.Certificates.TwDce CFSG.Certificates.CosetEnumeration

@[expose] def nType (j : ℕ) : ℕ := [0, 1, 2, 2, 1, 0, 1, 0, 1, 0].getD j 0

@[expose] def nEven (j : ℕ) : Bool := [false, false, false, false, false, false, true, true, true,
  true].getD j false

@[expose] def nBound (j : ℕ) : ℕ :=
  [1, 31671, 825792, 825792, 31671, 1, 63342, 2, 63342, 2].getD j 0

@[expose] def nSub (j : ℕ) : Subgroup (YGroup 4 3 2) :=
  if nEven j then evenSub (lt3 (nType j)) 0 else lsub (lt3 (nType j))

@[expose] def gRec (j : ℕ) : List ℕ :=
  [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [19, 20, 21, 22, 23, 24, 25, 26, 27],
    [28, 29, 30, 31, 43, 32, 33, 34, 35], [44, 45, 46, 47, 48, 49, 50, 51, 52],
    [53, 54, 55, 56, 57, 58, 59, 60, 61], [62, 63, 64, 65, 82, 66, 67, 68, 69, 70],
    [71, 72, 114, 73, 74, 75, 76, 77], [115, 116, 117, 118, 119, 120, 121, 122, 123],
    [98, 100, 91, 96, 94, 101, 103, 105], [106, 107, 108, 126, 109, 110, 111, 112, 113]].getD j []

@[expose] def covR (j : ℕ) : List (ℕ × ℕ) :=
  [[(10, 0)], [(10, 1), (11, 0), (127, 0)], [(11, 1), (128, 0), (129, 0)],
    [(130, 0), (12, 1), (131, 0)], [(14, 0), (13, 1), (132, 0)], [(14, 1)],
    [(16, 0), (15, 1), (133, 0)], [(16, 1)], [(18, 0), (134, 0), (135, 0)], [(18, 1)]].getD j []

@[expose] noncomputable def recStab (r j : ℕ) (w : List ℕ) : Prop :=
  r < 136 ∧ 3 ≤ dKind (CFSG.KD.Y442D.RD r) ∧ dKind (CFSG.KD.Y442D.RD r) < 5 ∧
    dN2 (CFSG.KD.Y442D.RD r) = j ∧ wList (CFSG.KD.Y442D.RW r) = w

@[expose] noncomputable def recCov (e : ℕ × ℕ) (j : ℕ) (w : List ℕ) : Prop :=
  e.1 < 136 ∧ dKind (CFSG.KD.Y442D.RD e.1) < 3 ∧
    ((e.2 = 0 ∧ dN1 (CFSG.KD.Y442D.RD e.1) = j ∧ wList (CFSG.KD.Y442D.RW e.1) = w) ∨
      (e.2 = 1 ∧ dN2 (CFSG.KD.Y442D.RD e.1) = j ∧ wList (CFSG.KD.Y442D.RA e.1) = w))

noncomputable instance (r j : ℕ) (w : List ℕ) : Decidable (recStab r j w) := by
  unfold recStab
  infer_instance

noncomputable instance (e : ℕ × ℕ) (j : ℕ) (w : List ℕ) : Decidable (recCov e j w) := by
  unfold recCov
  infer_instance

theorem nType_lt : ∀ j < 10, nType j < 3 := by decide

theorem tL_spec : ∀ c ∈ tL, c < 10 ∧ c ≠ 4 := by decide

theorem gen_ok : ∀ j < 10, ∀ c ∈ lt3 (nType j),
    (nEven j = false → ∃ r ∈ gRec j, recStab r j [c]) ∧
      (nEven j = true → c ≠ 0 → ∃ r ∈ gRec j, recStab r j [0, c]) := by
  decide +kernel

theorem cov_ok : ∀ j < 10, ∀ a < (cw (nType j)).length,
    ∃ e ∈ covR j, recCov e j ((cw (nType j)).getD a []) := by
  decide +kernel

theorem even_type : ∀ j < 10, nEven j = true → nType j < 2 := by decide

theorem zero_mem_lt3 : ∀ t < 2, 0 ∈ lt3 t := by decide

theorem F432_mem_lt3 : ∀ t < 2, ∀ c ∈ F432Word, c ∈ lt3 t := by decide

theorem nBound_sum : ∑ i : Fin 10, nBound i = 1841616 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  decide

section

theorem index_nSub (j : ℕ) (hj : j < 10) : (nSub j).index ≤ nBound j := by
  have hT := index_tL_le.2
  have hY := index_yL_le
  have hH : (lsub allL).index = 1 := by rw [lsub_all, Subgroup.index_top]
  have hTe := index_evenSub_le (L := tL) (by decide) (c₀ := 0) (by decide)
  have hHe := index_evenSub_le (L := allL) (by decide) (c₀ := 0) (by decide)
  interval_cases j <;> simp only [nSub, nEven, nType, lt3, nBound, List.getD_cons_succ,
    List.getD_cons_zero, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem u_conj_T : ∀ c ∈ (lsub tL).map (psiG swSp432_eq_one),
    (u swSp432_eq_one)⁻¹ * c * u swSp432_eq_one ∈ (psiG swSp432_eq_one).range := by
  rintro _ ⟨y, hy, rfl⟩
  rw [u_inv]
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨hc10, hc4⟩ := tL_spec c hc
    rw [u_conj _ hc10 hc4]
    exact ⟨_, rfl⟩
  | one => rw [map_one, mul_one, u_mul_self]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    have e : u swSp432_eq_one * psiG swSp432_eq_one (x * y) * u swSp432_eq_one =
        (u swSp432_eq_one * psiG swSp432_eq_one x * u swSp432_eq_one) *
          (u swSp432_eq_one * psiG swSp432_eq_one y * u swSp432_eq_one) := by
      rw [map_mul]
      calc u swSp432_eq_one * (psiG swSp432_eq_one x * psiG swSp432_eq_one y) * u swSp432_eq_one
          = u swSp432_eq_one * psiG swSp432_eq_one x * 1 * psiG swSp432_eq_one y *
              u swSp432_eq_one := by group
        _ = _ := by rw [← u_mul_self swSp432_eq_one]; group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : u swSp432_eq_one * psiG swSp432_eq_one x⁻¹ * u swSp432_eq_one =
        (u swSp432_eq_one * psiG swSp432_eq_one x * u swSp432_eq_one)⁻¹ := by
      rw [map_inv]
      calc u swSp432_eq_one * (psiG swSp432_eq_one x)⁻¹ * u swSp432_eq_one
          = (u swSp432_eq_one)⁻¹ * (psiG swSp432_eq_one x)⁻¹ * (u swSp432_eq_one)⁻¹ := by
            rw [u_inv]
        _ = _ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem wVal_eq {w : ℕ} {l : List ℕ} (h : wList w = l) :
    wVal xL w = psiG swSp432_eq_one (evalWord (yGen 4 3 2) l) := by
  rw [wVal, h, evalWord_xL]

theorem index_le : (psiG swSp432_eq_one).range.FiniteIndex ∧
    (psiG swSp432_eq_one).range.index ≤ 1841616 := by
  classical
  have hfin := finite_y432
  set φ := psiG swSp432_eq_one
  set H := φ.range
  obtain ⟨X, hX0, hX⟩ := facts
  let tP : Fin 10 → Ghat swSp432_eq_one → Prop := fun i k =>
    ∃ j : Fin 10, ∃ v, v ∈ H ∧ X i * k * u swSp432_eq_one * (X j * v)⁻¹ ∈ H
  have htP : ∀ i : Fin 10, ∀ a < (cw (nType i)).length,
      tP i (φ (evalWord (yGen 4 3 2) ((cw (nType i)).getD a []))) := by
    intro i a ha
    obtain ⟨⟨r, d⟩, -, hr, hk, hcase⟩ := cov_ok i i.2 a ha
    obtain ⟨h1, h2, hf⟩ := (hX r hr).1 hk
    rcases hcase with ⟨-, hn, hw⟩ | ⟨-, hn, hw⟩
    · refine ⟨⟨_, h2⟩, wVal xL (CFSG.KD.Y442D.RA r), ?_, ?_⟩
      · rw [wVal, evalWord_xL]; exact ⟨_, rfl⟩
      · simp only at hn hw
        rw [← wVal_eq hw, ← hn]
        exact hf
    · refine ⟨⟨_, h1⟩, wVal xL (CFSG.KD.Y442D.RW r), ?_, ?_⟩
      · rw [wVal, evalWord_xL]; exact ⟨_, rfl⟩
      · simp only at hn hw
        rw [← wVal_eq hw]
        have := H.inv_mem hf
        rw [show (X (dN1 (CFSG.KD.Y442D.RD r)) * wVal xL (CFSG.KD.Y442D.RW r) *
            u swSp432_eq_one * (X (dN2 (CFSG.KD.Y442D.RD r)) * wVal xL (CFSG.KD.Y442D.RA r))⁻¹)⁻¹ =
            X (dN2 (CFSG.KD.Y442D.RD r)) * wVal xL (CFSG.KD.Y442D.RA r) * (u swSp432_eq_one)⁻¹ *
            (X (dN1 (CFSG.KD.Y442D.RD r)) * wVal xL (CFSG.KD.Y442D.RW r))⁻¹ by group,
          u_inv, hn] at this
        exact this
  let D : TwistData H ((lsub tL).map φ) (u swSp432_eq_one) 10 :=
    { x := fun i => X i
      S := fun i => (nSub i).map φ
      rep := fun i => {k | ∃ a < (cw (nType i)).length,
        k = φ (evalWord (yGen 4 3 2) ((cw (nType i)).getD a []))}
      tgt := fun i k => if h : tP i k then h.choose else 0
      tgtElt := fun i k => if h : tP i k then h.choose_spec.choose else 1
      base := 0
      base_mem := by
        change X 0 ∈ H
        rw [hX0]
        exact H.one_mem
      S_le := fun i => Subgroup.map_le_range _ _
      S_conj := by
        rintro i _ ⟨y, hy, rfl⟩
        have hgen : ∀ g ∈ (if nEven i then (fun c => yGen 4 3 2 0 * yGen 4 3 2 c) ''
            {c | c ∈ lt3 (nType i)} else yGen 4 3 2 '' {c | c ∈ lt3 (nType i)}),
            X i * φ g * (X i)⁻¹ ∈ H := by
          have hstab : ∀ r w, recStab r i w → X i * φ (evalWord (yGen 4 3 2) w) * (X i)⁻¹ ∈ H := by
            rintro r w ⟨hr, hk1, hk2, hn, hw⟩
            have := ((hX r hr).2 hk1 hk2).2
            rw [hn, wVal_eq hw] at this
            exact this
          by_cases he : nEven i = true
          · rw [if_pos he]
            rintro _ ⟨c, hc, rfl⟩
            by_cases hc0 : c = 0
            · subst hc0
              simp only [yGen_mul_self, map_one, mul_one, mul_inv_cancel]
              exact H.one_mem
            · obtain ⟨r, -, hr⟩ := (gen_ok i i.2 c hc).2 he hc0
              have := hstab r _ hr
              simpa only [evalWord_cons, evalWord_nil, mul_one] using this
          · rw [if_neg he]
            rintro _ ⟨c, hc, rfl⟩
            obtain ⟨r, -, hr⟩ := (gen_ok i i.2 c hc).1 (by simpa using he)
            have := hstab r _ hr
            simpa only [evalWord_cons, evalWord_nil, mul_one] using this
        have hsub : nSub i = Subgroup.closure (if nEven i then
            (fun c => yGen 4 3 2 0 * yGen 4 3 2 c) '' {c | c ∈ lt3 (nType i)} else
            yGen 4 3 2 '' {c | c ∈ lt3 (nType i)}) := by
          unfold nSub
          split_ifs <;> rfl
        rw [hsub] at hy
        induction hy using Subgroup.closure_induction with
        | mem g hg => exact hgen g hg
        | one => rw [map_one, mul_one, mul_inv_cancel]; exact H.one_mem
        | mul a b _ _ ha hb =>
          have e : X i * φ (a * b) * (X i)⁻¹ = (X i * φ a * (X i)⁻¹) * (X i * φ b * (X i)⁻¹) := by
            rw [map_mul]; group
          rw [e]
          exact H.mul_mem ha hb
        | inv a _ ha =>
          have e : X i * φ a⁻¹ * (X i)⁻¹ = (X i * φ a * (X i)⁻¹)⁻¹ := by
            rw [map_inv]; group
          rw [e]
          exact H.inv_mem ha
      rep_le := by
        rintro i _ ⟨a, -, rfl⟩
        exact ⟨_, rfl⟩
      rep_cover := by
        rintro i _ ⟨y, rfl⟩
        obtain ⟨a, ha, ℓ, hℓ, z, hz, rfl⟩ := cover (nType_lt i i.2) y
        set w := evalWord (yGen 4 3 2) ((cw (nType i)).getD a [])
        by_cases he : nEven i = true
        · have ht := even_type i i.2 he
          have h0 := zero_mem_lt3 _ ht
          have hsub : nSub i = evenSub (lt3 (nType i)) 0 := by rw [nSub, if_pos he]
          rcases mem_evenSub_or' h0 hℓ with hE | hE
          · exact ⟨φ w, ⟨a, ha, rfl⟩, φ ℓ, ⟨ℓ, by rw [hsub]; exact hE, rfl⟩, φ z,
              ⟨z, hz, rfl⟩, by rw [map_mul, map_mul]⟩
          ·
            have hF : F432 ∈ lsub (lt3 (nType i)) := by
              rw [F432_eq_evalWord]
              exact evalWord_mem_lsub (F432_mem_lt3 _ ht)
            have hFE : yGen 4 3 2 0 * F432 ∈ evenSub (lt3 (nType i)) 0 := by
              rcases mem_evenSub_or h0 hF with h | h
              · exfalso
                have := evenSub_le_ker (lt3_lt _ (by omega)) (by norm_num) h
                exact F432_ne_one_par this
              · exact h
            have hℓF : ℓ * F432 ∈ evenSub (lt3 (nType i)) 0 := by
              have := (evenSub (lt3 (nType i)) 0).mul_mem hE hFE
              rwa [mul_assoc, ← mul_assoc (yGen 4 3 2 0), yGen_mul_self, one_mul] at this
            have hc : w⁻¹ * F432⁻¹ * w ∈ lsub tL := by
              apply stab_zero
              rw [map_mul, map_mul, map_inv, map_inv, MonoidHom.mem_ker.1 F432_mem_ker]
              simp
            refine ⟨φ w, ⟨a, ha, rfl⟩, φ (ℓ * F432), ⟨_, by rw [hsub]; exact hℓF, rfl⟩,
              φ (w⁻¹ * F432⁻¹ * w * z), ⟨_, (lsub tL).mul_mem hc hz, rfl⟩, ?_⟩
            rw [← map_mul, ← map_mul]
            congr 1
            group
        · have hsub : nSub i = lsub (lt3 (nType i)) := by
            rw [nSub, if_neg he]
          exact ⟨φ w, ⟨a, ha, rfl⟩, φ ℓ, ⟨ℓ, by rw [hsub]; exact hℓ, rfl⟩, φ z, ⟨z, hz, rfl⟩,
            by rw [map_mul, map_mul]⟩
      tgtElt_mem := by
        rintro i _ ⟨a, ha, rfl⟩
        have h := htP i a ha
        simp only [dif_pos h]
        exact h.choose_spec.choose_spec.1
      tgt_spec := by
        rintro i _ ⟨a, ha, rfl⟩
        have h := htP i a ha
        simp only [dif_pos h]
        exact h.choose_spec.choose_spec.2 }
  have : Finite H := Finite.of_surjective _ φ.rangeRestrict_surjective
  obtain ⟨hfi, hle⟩ := D.index_le_sum (u_mul_self _) u_conj_T (closure_H_u _)
  refine ⟨hfi, hle.trans ?_⟩
  calc ∑ i, (D.S i).relIndex H ≤ ∑ i : Fin 10, nBound i := by
        refine Finset.sum_le_sum fun i _ => ?_
        exact (relIndex_map_range_le φ (nSub i)).trans (index_nSub i i.2)
    _ = 1841616 := nBound_sum

theorem y442_bound : Finite (YGroup 4 4 2) ∧ Nat.card (YGroup 4 4 2) ≤ 7531234255143970327756800 := by
  have hfin := finite_y432
  obtain ⟨hfi, hle⟩ := index_le
  set H := (psiG swSp432_eq_one).range
  have hH : Nat.card H ≤ 8178940946586009600 := by
    rw [← card_y432]
    exact Nat.card_le_card_of_surjective _ (psiG swSp432_eq_one).rangeRestrict_surjective
  have hmul := H.card_mul_index
  have hHpos : 0 < Nat.card H := by
    have : Finite H := Finite.of_surjective _ (psiG swSp432_eq_one).rangeRestrict_surjective
    exact Nat.card_pos
  have hGpos : Nat.card (Ghat swSp432_eq_one) ≠ 0 := by
    rw [← hmul]
    exact Nat.mul_ne_zero hHpos.ne' hfi.index_ne_zero
  have hGfin : Finite (Ghat swSp432_eq_one) := Nat.finite_of_card_ne_zero hGpos
  refine ⟨Finite.of_injective _ (SemidirectProduct.inl_injective (φ := act swSp432_eq_one)), ?_⟩
  have h2 := card_Ghat swSp432_eq_one
  have h3 : Nat.card H * H.index ≤ 8178940946586009600 * 1841616 := Nat.mul_le_mul hH hle
  omega

end

end CertificateChecks.KernelY442

end
