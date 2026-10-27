
module

public import Certificates.Kernel.Parrott946.Glue17i

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups CertificateChecks.KernelA45 Subgroup

local notation "P45" => Equiv.Perm (Fin 45)

theorem allL_of {f : ℕ → ℕ → Bool} : ∀ {L : List ℕ} {k : ℕ},
    (∀ j < L.length, f (k + j) (L.getD j 0) = true) → allL L f k = true
  | [], _, _ => rfl
  | x :: L, k, h => by
    have h0 := h 0 (by simp)
    have h1 : allL L f (Nat.succ k) = true := allL_of fun j hj => by
      have := h (j + 1) (by simpa using hj)
      rwa [List.getD_cons_succ, Nat.add_succ, ← Nat.succ_add] at this
    have e : allL (x :: L) f k = bAnd(f k x, allL L f (Nat.succ k)) := rfl
    rw [e, bAnd_eq, h1, Bool.and_true]
    simpa using h0

theorem anyL_of {f : ℕ → ℕ → Bool} : ∀ {L : List ℕ} {k : ℕ} (j : ℕ), j < L.length →
    f (k + j) (L.getD j 0) = true → anyL L f k = true
  | [], _, j, hj, _ => absurd hj (by simp)
  | x :: L, k, j, hj, h => by
    have e : anyL (x :: L) f k =
        Bool.rec (motive := fun _ => Bool) (anyL L f (Nat.succ k)) true (f k x) := rfl
    rw [e]
    cases hf : f k x
    · cases j with
      | zero => simp at h; rw [hf] at h; exact absurd h (by decide)
      | succ j =>
        refine anyL_of j (by simpa using hj) ?_
        rwa [List.getD_cons_succ, Nat.add_succ, ← Nat.succ_add] at h
    · rfl

@[expose] def NormS (r : P45) : Prop := ∀ x ∈ Sgens, r * x * r⁻¹ ∈ Slist ()

theorem Slist_eq : Slist () = prodSpan ([6, 21, 31, 41].map xI) := by
  rw [Slist, tabList_eq, tabList_eq, gens_eq.1]

theorem mem_S {x : P45} : x ∈ Slist () ↔ x = 1 ∨ ∃ j < 43, bitB D17.M0 j = true ∧ x = xI j := by
  rw [Slist_eq]
  exact span_set (mem43 (by decide)) c17_spans.1 masks_lt.1 x

theorem sG_rec : ∀ j < 4, PRep 45 6 (sG.getD j 0) (Sgens.getD j 1) := by
  intro j hj
  rw [gens_eq.1]
  interval_cases j
  · exact (xI_spec (by norm_num)).1
  · exact (xI_spec (by norm_num)).1
  · exact (xI_spec (by norm_num)).1
  · exact (xI_spec (by norm_num)).1

theorem mem_Sgens {x : P45} (hx : x ∈ Sgens) : ∃ j < 4, Sgens.getD j 1 = x := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  exact ⟨j, hj, List.getD_eq_getElem _ _ hj⟩

theorem normS_of_mask {P : ℕ} {r : P45} (hP : PRep 45 6 P r)
    (h : normMaskK 45 6 D17.I D17.M0 (pidn 45 6) P sG = true) : NormS r := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := mem_Sgens hx
  rcases normMaskK_spec h (j := j) (by exact hj) with h1 | ⟨k, hk, hb, h1⟩
  · have e := mul_eq_of_eq22 hP (sG_rec j hj) prep_pid hP h1
    rw [e, one_mul, mul_inv_cancel]
    exact mem_S.2 (Or.inl rfl)
  · rw [len_I] at hk
    have e := mul_eq_of_eq22 hP (sG_rec j hj) (by rw [← iE_eq hk]; exact (xI_spec hk).1) hP h1
    rw [e, mul_inv_cancel_right]
    exact mem_S.2 (Or.inr ⟨k, hk, hb, rfl⟩)

theorem mask_of_normS {P : ℕ} {r : P45} (hP : PRep 45 6 P r) (h : NormS r) :
    normMaskK 45 6 D17.I D17.M0 (pidn 45 6) P sG = true := by
  unfold normMaskK
  refine allL_of fun j hj => ?_
  have hj4 : j < 4 := hj
  have hmem : Sgens.getD j 1 ∈ Sgens := by
    rw [List.getD_eq_getElem _ _ (by rw [gens_eq.1]; exact hj4)]
    exact List.getElem_mem _
  rw [Bool.or_eq_true]
  rcases mem_S.1 (h _ hmem) with e | ⟨k, hk, hb, e⟩
  · refine Or.inl (eq22_of_mul17 hP (sG_rec j hj4) prep_pid hP ?_)
    calc r * Sgens.getD j 1 = r * Sgens.getD j 1 * r⁻¹ * r := by group
      _ = 1 * r := by rw [e]
  · refine Or.inr (anyL_of k (by rw [len_I]; exact hk) ?_)
    rw [Nat.zero_add, bAnd_eq, Bool.and_eq_true, ← iE_eq hk]
    refine ⟨hb, eq22_of_mul17 hP (sG_rec j hj4) (xI_spec hk).1 hP ?_⟩
    calc r * Sgens.getD j 1 = r * Sgens.getD j 1 * r⁻¹ * r := by group
      _ = xI k * r := by rw [e]

abbrev SH : Subgroup P45 := closure {x | x ∈ Sgens}

abbrev NS : Subgroup P45 := Subgroup.normalizer (SH : Set P45)

theorem S_set : ∀ x, x ∈ Slist () ↔ x ∈ SH := by
  have hsq : ∀ x ∈ Sgens, x * x = 1 := by
    rw [gens_eq.1]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    exact (xI_spec (mem43 (by decide) j hj)).2.2.1
  have hcomm : ∀ a ∈ Sgens, ∀ b ∈ Sgens, a * b = b * a := by
    rw [gens_eq.1]
    intro a ha b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ha
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hb
    exact comm_bit (mem43 (by decide) j hj) (mem43 (by decide) k hk) (cm_bits.1 j hj k hk)
  intro x
  rw [Slist, tabList_eq, tabList_eq]
  exact ⟨fun hx => prodSpan_mem SH (fun g hg => subset_closure hg) x hx,
    fun hx => mem_prodSpan_of_mem_closure _ hsq hcomm x hx⟩

theorem normS_iff {r : P45} : NormS r ↔ ∀ x ∈ SH, r * x * r⁻¹ ∈ SH := by
  constructor
  · intro h
    have hmap : SH.map (MulAut.conj r).toMonoidHom ≤ SH := by
      rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨x, hx, rfl⟩
      exact (S_set _).1 (h x hx)
    exact fun x hx => hmap ⟨x, hx, rfl⟩
  · intro h x hx
    exact (S_set _).2 (h x (subset_closure hx))

theorem mem_normalizer_of {r : P45} (h : NormS r) : r ∈ NS := by
  have h' := normS_iff.1 h
  have hmap : SH.map (MulAut.conj r).toMonoidHom ≤ SH := by
    rintro _ ⟨x, hx, rfl⟩
    exact h' x hx
  have heq : SH.map (MulAut.conj r).toMonoidHom = SH :=
    Subgroup.eq_of_le_of_card_ge hmap (by
      rw [Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj r))])
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact h' x
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, e⟩ := hx
    have e' : r * y * r⁻¹ = r * x * r⁻¹ := e
    rw [mul_left_inj, mul_right_inj] at e'
    rw [← e']
    exact hy

theorem normS_of_mem {r : P45} (h : r ∈ NS) : NormS r := by
  rw [normS_iff]
  intro x hx
  exact (mem_normalizer_iff.1 h x).1 hx

theorem T0g_le_norm : T0g ≤ NS := by
  rw [closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have h := c17_ns
  rw [strictB_eq', Bool.and_eq_true] at h
  have h0 := h.1
  simp only [Bool.and_eq_true] at h0
  exact mem_normalizer_of (normS_of_mask (prep_g0 k hk) (allN_spec h0.1.1.1.1.1.1.1 k hk))

theorem rep_norm {i : ℕ} (hi : i < 9) (h : NormS (rr i)) : i = 0 ∨ i = 5 ∨ i = 6 := by
  have hns := c17_ns
  simp only [strictB_eq', Bool.and_eq_true, Bool.not_eq_true'] at hns
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, n1⟩, n2⟩, n3⟩, n4⟩, n7⟩, n8⟩ := hns
  have key : ∀ {k : ℕ}, k < 9 → normMaskK 45 6 D17.I D17.M0 (pidn 45 6) (rE k) sG = false →
      ¬ NormS (rr k) := by
    intro k hk hf hN
    rw [mask_of_normS (prep_rr hk).1 hN] at hf
    exact absurd hf (by decide)
  interval_cases i
  · exact Or.inl rfl
  · exact absurd h (key (by norm_num) n1)
  · exact absurd h (key (by norm_num) n2)
  · exact absurd h (key (by norm_num) n3)
  · exact absurd h (key (by norm_num) n4)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
  · exact absurd h (key (by norm_num) n7)
  · exact absurd h (key (by norm_num) n8)

theorem t_mem_Sgens : t ∈ Sgens := by simp [Sgens]

theorem cent_S {c : P45} (hc : c ∈ A)
    (hcom : ∀ x ∈ Sgens, c * x = x * c) : c ∈ Slist () := by
  obtain ⟨i, hi, hs⟩ := cent_t_cosets hc (hcom t t_mem_Sgens)
  have hcN : c ∈ NS := by
    refine mem_normalizer_of fun x hx => ?_
    rw [hcom x hx, mul_inv_cancel_right]
    exact (S_set x).2 (subset_closure hx)
  have hrN : NormS (rr i) := by
    refine normS_of_mem ?_
    have e : rr i = (c * (rr i)⁻¹)⁻¹ * c := by group
    rw [e]
    exact NS.mul_mem (NS.inv_mem (T0g_le_norm hs)) hcN
  obtain ⟨e0, he, hall, -⟩ := t0_enum
  obtain ⟨i', hi', hei'⟩ := hall _ hs
  have hrec : PRep 45 6 (pc (T0Z.T i') (rE i)) c := by
    have := prep_pc (he i' hi').1 (prep_rr hi).1
    rwa [hei', inv_mul_cancel_right] at this
  have hcs := c17_cs
  rw [strictB_eq'] at hcs
  have h1 := allN_spec hcs i' hi'
  have hpos : ∃ p < 3, [rE 0, rE 5, rE 6].getD p 0 = rE i := by
    rcases rep_norm hi hrN with rfl | rfl | rfl
    · exact ⟨0, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, by norm_num, rfl⟩
  obtain ⟨p, hp, ep⟩ := hpos
  have h2 := allL_spec h1 p hp
  rw [ep, strictB_eq', Bool.or_eq_true, Bool.not_eq_true'] at h2
  rcases h2 with h2 | h2
  · exfalso
    have : allL sG (fun _ g => cmm (pc (T0Z.T i') (rE i)) g) 0 = true := by
      refine allL_of fun j hj => ?_
      have hj4 : j < 4 := hj
      have hmem : Sgens.getD j 1 ∈ Sgens := by
        rw [List.getD_eq_getElem _ _ (by rw [gens_eq.1]; exact hj4)]
        exact List.getElem_mem _
      exact eq22_of_mul17 hrec (sG_rec j hj4) (sG_rec j hj4) hrec (hcom _ hmem)
    rw [this] at h2
    exact absurd h2 (by decide)
  · rcases inMaskK_spec h2 with e | ⟨j, hj, hb, e⟩
    · rw [e] at hrec
      rw [prep_eq hrec prep_pid]
      exact mem_S.2 (Or.inl rfl)
    · rw [len_I] at hj
      rw [← e, ← iE_eq hj] at hrec
      rw [prep_eq hrec (xI_spec hj).1]
      exact mem_S.2 (Or.inr ⟨j, hj, hb, rfl⟩)

theorem s_centralizer : centralizerSCheck () = true := by
  unfold centralizerSCheck
  rw [tabList_eq]
  refine List.all_eq_true.2 fun c hc => ?_
  have hcA : c ∈ A := (mem_elemsT QA45 QA45_ok c).1 hc
  rw [Bool.or_eq_true]
  by_cases hn : ∀ x ∈ Sgens, c * x = x * c
  · exact Or.inr (decide_eq_true (cent_S hcA hn))
  · refine Or.inl ?_
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro h
    exact hn fun x hx => of_decide_eq_true (List.all_eq_true.1 h x hx)

end CertificateChecks.Parrott946

end
