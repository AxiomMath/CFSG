module

public import Certificates.Kernel.J3Coset.Local
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3CoverOver
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3SylowPrim

public section

namespace CertificateChecks.KernelJ3C

open CFSG.KC.J3C CFSG.KD.J3C CFSG.KS CFSG.KS.Raw.Orb MulAction
  CFSG.AGLEmbedding.KFactProofs.J3Sylow CFSG.Quasithin

theorem roots_head : roots.head? = some 0 := fix_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem roots_len : roots.length = 20 := fix_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem gws_facts : ∀ i < 19, codesAB (gws.getD i []) = true ∧
    wv tb (gws.getD i []) 0 = roots.getD (i + 1) 0 :=
  fix_facts.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem zero_mem_roots : 0 ∈ roots := List.mem_of_mem_head? (by rw [roots_head]; rfl)

theorem roots_zero : roots[0]'(by rw [roots_len]; decide) = 0 := by
  have h := roots_head
  rw [List.head?_eq_getElem?] at h
  exact (List.getElem?_eq_some_iff.1 h).2

theorem getD_roots (t : ℕ) : roots.getD t 0 ∈ roots := by
  rw [List.getD_eq_getElem?_getD]
  cases h : roots[t]? with
  | none => exact zero_mem_roots
  | some v => exact List.mem_of_getElem? h

theorem root_index {r : ℕ} (hr : r ∈ roots) (h0 : r ≠ 0) :
    ∃ i < 19, roots.getD (i + 1) 0 = r := by
  obtain ⟨j, hj, hjr⟩ := List.getElem_of_mem hr
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact h0 (hjr.symm.trans roots_zero)
  refine ⟨j - 1, by rw [roots_len] at hj; omega, ?_⟩
  rw [show j - 1 + 1 = j by omega, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    Option.getD_some, hjr]

theorem fgw1 (j : ℕ) : fgw 1 j = if j = 0 then [4] else [5] := by simp [fgw]

theorem fgwP (i j : ℕ) (hi : i < 19) :
    fgw (2 + i) j = if j = 0 then [4] else if j = 1 then [5] else gws.getD i [] := by
  unfold fgw
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show 2 + i - 2 = i by omega]

theorem fgwO (i j : ℕ) (hi : i < 19) :
    fgw (21 + i) j = if j = 0 then [6] else if j = 1 then [7]
      else if j = 2 then gws.getD i [] ++ [6] ++ invW (gws.getD i [])
      else gws.getD i [] ++ [7] ++ invW (gws.getD i []) := by
  unfold fgw
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show 21 + i - 21 = i by omega]

theorem rf_ne {f r : ℕ} (hf : f ≠ 1) : rf f r = 0 := by
  unfold rf
  rw [if_neg hf]

theorem invW_codes {w : List ℕ} (hw : codesAB w = true) : codesAB (invW w) = true := by
  unfold codesAB at hw ⊢
  rw [List.all_eq_true] at hw ⊢
  intro c hc
  unfold invW at hc
  rw [List.mem_reverse, List.mem_map] at hc
  obtain ⟨d, hd, rfl⟩ := hc
  have := hw d hd
  simp only [decide_eq_true_eq] at this ⊢
  unfold invC
  split_ifs <;> omega

section Prim

variable {J : Type} [Group J] [Finite J] [MulAction J (Fin nn)] {g : ℕ → J}

variable (hg : Acts g)
include hg

theorem forest_k {f : ℕ} (hf : f < 40) (S : Subgroup J) (hgS : ∀ j < 4, ev g (fgw f j) ∈ S)
    (hcodes : ∀ j < 4, ∀ c ∈ fgw f j, c < 8) (p : Fin nn) :
    ∃ r, ∃ hr : r < nn, rf f (frt (e64 FT (Nat.add (Nat.mul f 25856) p.val))) = r ∧
      ∃ k ∈ S, k • (⟨r, hr⟩ : Fin nn) = p := by
  obtain ⟨r, hr, hRr, k, hk, hkr⟩ := forest_reach (MulAction.toPermHom J (Fin nn))
    (forest_facts hf) S (fun j => ev g (fgw f j)) hgS (fun j hj i => by
      rw [MulAction.toPermHom_apply, MulAction.toPerm_apply]
      exact ev_smul hg (hcodes j hj) i) p.val p.isLt
  refine ⟨r, hr, hRr, k, hk, ?_⟩
  rw [MulAction.toPermHom_apply, MulAction.toPerm_apply] at hkr
  exact hkr

theorem gw_smul {i : ℕ} (hi : i < 19) :
    (ev g (gws.getD i []) • pt0).val = roots.getD (i + 1) 0 := by
  rw [ev_smul hg (codesAB_lt (gws_facts i hi).1)]
  exact (gws_facts i hi).2

theorem cover_roots (ω : Fin nn) : ∃ r ∈ {p : Fin nn | p.val ∈ roots},
    ∃ k ∈ Subgroup.closure ({g 4, g 5} : Set J), k • r = ω := by
  obtain ⟨r, hr, hRr, k, hk, hkr⟩ := forest_k hg (f := 1) (by decide)
    (Subgroup.closure ({g 4, g 5} : Set J))
    (fun j _ => by
      rw [fgw1]
      split_ifs
      · rw [ev_single]; exact Subgroup.subset_closure (by simp)
      · rw [ev_single]; exact Subgroup.subset_closure (by simp))
    (fun j _ => by rw [fgw1]; split_ifs <;> decide) ω
  refine ⟨⟨r, hr⟩, ?_, k, hk, hkr⟩
  change r ∈ roots
  rw [← hRr]
  unfold rf
  rw [if_pos rfl]
  exact getD_roots _

theorem coatom [IsSimpleGroup J] (hJ : Nat.card J = 50232960) : IsCoatom (stabilizer J pt0) := by
  refine isCoatom_stabilizer pt0 (trans hg) ⟨ptB, fun h => beta0_ne (congrArg Fin.val h)⟩
    ({g 4, g 5} : Set J) ?_ {p : Fin nn | p.val ∈ roots} (cover_roots hg) ?_
  · rintro x (rfl | rfl)
    · exact fix_letter hg (by decide) fix_facts.1
    · exact fix_letter hg (by decide) fix_facts.2.1
  · intro r hr hr0
    have hrv : r.val ≠ 0 := fun h => hr0 (Fin.ext h)
    obtain ⟨i, hi, hri⟩ := root_index hr hrv
    refine ⟨ev g (gws.getD i []), Fin.ext ((gw_smul hg hi).trans hri), fun ω => ?_⟩
    obtain ⟨r', hr', hRr', k, hk, hkr⟩ := forest_k hg (f := 2 + i) (by omega)
      (Subgroup.closure (({g 4, g 5} : Set J) ∪ {ev g (gws.getD i [])}))
      (fun j _ => by
        rw [fgwP i j hi]
        split_ifs
        · rw [ev_single]; exact Subgroup.subset_closure (by simp)
        · rw [ev_single]; exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp))
      (fun j _ => by
        rw [fgwP i j hi]
        split_ifs
        · decide
        · decide
        · exact codesAB_lt (gws_facts i hi).1) ω
    rw [rf_ne (by omega)] at hRr'
    subst hRr'
    exact ⟨k, hk, hkr⟩

theorem gen_inv (hJ : Nat.card J = 50232960) :
    g 1 = (g 0)⁻¹ ∧ g 0 = (g 1)⁻¹ ∧ g 3 = (g 2)⁻¹ ∧ g 2 = (g 3)⁻¹ := by
  have hA : g 0 * g 0 = 1 := by
    have := word_eq hJ hg [0, 0] [] (by decide) (by decide) (baseEq_of
      (by rw [wv_cons, wv_cons]; exact (perm_facts 0 (by decide)).2.1)
      (by rw [wv_cons, wv_cons]; exact (perm_facts beta0 beta0_lt).2.1))
    simpa [ev] using this
  have h10 : g 1 = g 0 := by
    have := word_eq hJ hg [1] [0] (by decide) (by decide) (baseEq_of rfl rfl)
    simpa [ev] using this
  have hB : g 2 * g 3 = 1 := by
    have := word_eq hJ hg [2, 3] [] (by decide) (by decide) (baseEq_of
      (by rw [wv_cons, wv_cons]; exact (perm_facts 0 (by decide)).2.2.2.2.2.1)
      (by rw [wv_cons, wv_cons]; exact (perm_facts beta0 beta0_lt).2.2.2.2.2.1))
    simpa [ev] using this
  have hA' : (g 0)⁻¹ = g 0 := (inv_eq_of_mul_eq_one_right hA)
  refine ⟨by rw [h10, hA'], by rw [h10, hA'], (eq_inv_of_mul_eq_one_right hB),
    (eq_inv_of_mul_eq_one_left hB)⟩

theorem ev_invW (hJ : Nat.card J = 50232960) :
    ∀ {w : List ℕ}, codesAB w = true → ev g (invW w) = (ev g w)⁻¹
  | [], _ => by simp [invW, ev]
  | c :: w, hw => by
    have hw2 : c < 4 ∧ codesAB w = true := by
      unfold codesAB at hw ⊢
      rw [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
      exact hw
    obtain ⟨hc, hw'⟩ := hw2
    have e : invW (c :: w) = invW w ++ [invC c] := by
      simp [invW, List.map_cons, List.reverse_cons]
    rw [e, ev_append, ev_invW hJ hw', ev_single, ev_cons, mul_inv_rev]
    congr 1
    obtain ⟨h1, h0, h3, h2⟩ := gen_inv hg hJ
    rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl
    · change g 1 = _
      exact h1
    · change g 0 = _
      exact h0
    · change g 3 = _
      exact h3
    · change g 2 = _
      exact h2

theorem overgroup [IsSimpleGroup J] (hJ : Nat.card J = 50232960) {K : Subgroup J}
    (hPK : PP g ≤ K) : K ≤ Subgroup.normalizer ((PP g : Subgroup J) : Set J) ∨ K = ⊤ := by
  have D := localData hg hJ
  have hN : Subgroup.normalizer ((PP g : Subgroup J) : Set J) = stabilizer J pt0 :=
    D.normalizer_eq (coatom hg hJ)
  refine CFSG.AGLEmbedding.KFactProofs.J3Cover.le_normalizer_or_eq_top (ω₀ := pt0) (P := PP g)
    (S₀ := Subgroup.closure ({g 4, g 5} : Set J)) (R := {p : Fin nn | p.val ∈ roots})
    (trans hg) (card_stab hJ hg) (card_P hg hJ) (P_le_stab hg) (le_of_eq hN.symm) ?_
    (cover_roots hg) ?_ (by rw [hJ]; decide) hPK
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact fix_letter hg (by decide) fix_facts.1
    · exact fix_letter hg (by decide) fix_facts.2.1
  · intro r hr hr0
    have hrv : r.val ≠ 0 := fun h => hr0 (Fin.ext h)
    obtain ⟨i, hi, hri⟩ := root_index hr hrv
    set x := ev g (gws.getD i [])
    have hcx := (gws_facts i hi).1
    refine ⟨x, Fin.ext ((gw_smul hg hi).trans hri), fun ω => ?_⟩
    have hconj : ∀ c, c = 6 ∨ c = 7 →
        ev g (gws.getD i [] ++ [c] ++ invW (gws.getD i [])) = x * g c * x⁻¹ := by
      intro c _
      rw [ev_append, ev_append, ev_single, ev_invW hg hJ hcx]
    obtain ⟨r', hr', hRr', k, hk, hkr⟩ := forest_k hg (f := 21 + i) (by omega)
      (PP g ⊔ (PP g).map (MulAut.conj x).toMonoidHom)
      (fun j _ => by
        rw [fgwO i j hi]
        split_ifs
        · rw [ev_single]
          exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
        · rw [ev_single]
          exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
        · rw [hconj 6 (Or.inl rfl)]
          exact Subgroup.mem_sup_right ⟨g 6, Subgroup.subset_closure (by simp), rfl⟩
        · rw [hconj 7 (Or.inr rfl)]
          exact Subgroup.mem_sup_right ⟨g 7, Subgroup.subset_closure (by simp), rfl⟩)
      (fun j _ => by
        have hca := codesAB_lt hcx
        have hci := codesAB_lt (invW_codes hcx)
        rw [fgwO i j hi]
        split_ifs
        · decide
        · decide
        · exact codes_app (codes_app hca (by decide)) hci
        · exact codes_app (codes_app hca (by decide)) hci) ω
    rw [rf_ne (by omega)] at hRr'
    subst hRr'
    exact ⟨k, hk, hkr⟩

end Prim

end CertificateChecks.KernelJ3C

end
