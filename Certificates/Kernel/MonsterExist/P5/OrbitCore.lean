module

public import CFSG.Monster.Existence.StdOdd.P5Inputs
public import CFSG.Certificates.Kernel.WeylE6Sound

public section

namespace CertificateChecks.MonsterExist.P5

open CFSG.Monster.Existence.StdOdd.P5 Matrix

@[expose] def gV (i : Fin 6) (n : ℕ) : ℕ := encV ((refl i).mulVec (decV n))

theorem refl_isom : ∀ i : Fin 6, (refl i).transpose * gram * refl i = gram := by
  decide +kernel

theorem refl_invol : ∀ i : Fin 6, refl i * refl i = 1 := by
  decide +kernel

theorem bil_refl (i : Fin 6) (u v : E5) :
    bil ((refl i).mulVec u) ((refl i).mulVec v) = bil u v := by
  have h : (refl i).transpose * gram * refl i = gram := refl_isom i
  unfold bil
  conv_lhs => rw [mulVec_mulVec, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose,
    mulVec_mulVec, ← Matrix.mul_assoc, h]
  exact dotProduct_comm _ _

theorem refl_refl (i : Fin 6) (v : E5) : (refl i).mulVec ((refl i).mulVec v) = v := by
  have h : refl i * refl i = 1 := refl_invol i
  rw [mulVec_mulVec, h, one_mulVec]

theorem refl_ne (i : Fin 6) {x : E5} (hx : x ≠ 0) : (refl i).mulVec x ≠ 0 := by
  intro h
  apply hx
  rw [← refl_refl i x, h, mulVec_zero]

theorem mem_rootVecs {α : E5} : α ∈ rootVecs ↔ bil α α = 2 := by
  simp only [rootVecs, Finset.mem_filter, Finset.mem_univ, true_and]

theorem rk_refl (i : Fin 6) (x : E5) : rk ((refl i).mulVec x) = rk x := by
  unfold rk
  apply Finset.card_nbij' (fun α => (refl i).mulVec α) (fun α => (refl i).mulVec α)
  · intro α hα
    simp only [Finset.mem_coe, Finset.mem_filter, mem_rootVecs] at hα ⊢
    refine ⟨by rw [bil_refl]; exact hα.1, ?_⟩
    rw [← refl_refl i x, bil_refl]
    exact hα.2
  · intro α hα
    simp only [Finset.mem_coe, Finset.mem_filter, mem_rootVecs] at hα ⊢
    exact ⟨by rw [bil_refl]; exact hα.1, by rw [bil_refl]; exact hα.2⟩
  · intro α _
    exact refl_refl i α
  · intro α _
    exact refl_refl i α

theorem encV_injective : Function.Injective encV := fun x y h => by
  rw [← CFSG.KC.WeylE6.decV_encV x, h, CFSG.KC.WeylE6.decV_encV]

theorem mem_rkFibre {c : ℕ} {x : E5} : x ∈ rkFibre c ↔ x ≠ 0 ∧ rk x = c := by
  simp only [rkFibre, Finset.mem_filter, Finset.mem_univ, true_and]

theorem orbit_sub_img (a : E5) (c : ℕ) (ha : a ≠ 0) (hrk : rk a = c) :
    ∀ k, vstep^[k] {encV a} ⊆ (rkFibre c).image encV := by
  intro k
  induction k with
  | zero =>
    intro m hm
    rw [Function.iterate_zero_apply, Finset.mem_singleton] at hm
    subst hm
    exact Finset.mem_image_of_mem _ (mem_rkFibre.2 ⟨ha, hrk⟩)
  | succ k ih =>
    intro m hm
    rw [Function.iterate_succ_apply'] at hm
    simp only [vstep, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_univ, true_and] at hm
    rcases hm with hm | ⟨n, hn, i, rfl⟩
    · exact ih hm
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 (ih hn)
      rw [CFSG.KC.WeylE6.decV_encV]
      obtain ⟨hy0, hyr⟩ := mem_rkFibre.1 hy
      exact Finset.mem_image_of_mem _ (mem_rkFibre.2 ⟨refl_ne i hy0, by rw [rk_refl]; exact hyr⟩)

theorem mem_vstep_of {S : Finset ℕ} {n : ℕ} (hn : n ∈ S) (i : Fin 6) : gV i n ∈ vstep S := by
  simp only [vstep, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
    true_and]
  exact Or.inr ⟨n, hn, i, rfl⟩

theorem iter_mono (S : Finset ℕ) (k : ℕ) : ∀ t, vstep^[k] S ⊆ vstep^[k + t] S
  | 0 => le_refl _
  | t + 1 => by
    rw [← Nat.add_assoc, Function.iterate_succ_apply']
    exact (iter_mono S k t).trans Finset.subset_union_left

abbrev Ent := ℕ × ℕ × ℕ × Fin 6

@[expose] def d0 : Ent := (0, 0, 0, 0)

@[expose] def entOK (a : ℕ) (E : List Ent) (k : ℕ) : Bool :=
  if (E.getD k d0).2.1 = 0 then (E.getD k d0).1 == a else
    decide ((E.getD k d0).2.1 ≤ 12) && decide ((E.getD k d0).2.2.1 < k) &&
      ((E.getD (E.getD k d0).2.2.1 d0).2.1 + 1 == (E.getD k d0).2.1) &&
      (gV (E.getD k d0).2.2.2 (E.getD (E.getD k d0).2.2.1 d0).1 == (E.getD k d0).1)

@[expose] def chkE (a : ℕ) (E : List Ent) : Bool := (List.range E.length).all (entOK a E)

theorem ent_mem {a : ℕ} {E : List Ent} (h : chkE a E = true) :
    ∀ k < E.length, (E.getD k d0).1 ∈ vstep^[(E.getD k d0).2.1] {a} ∧ (E.getD k d0).2.1 ≤ 12 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hok : entOK a E k = true := by
      unfold chkE at h
      rw [List.all_eq_true] at h
      exact h k (List.mem_range.2 hk)
    unfold entOK at hok
    by_cases hd : (E.getD k d0).2.1 = 0
    · rw [if_pos hd, beq_iff_eq] at hok
      rw [hd, hok]
      exact ⟨Finset.mem_singleton_self a, Nat.zero_le _⟩
    · rw [if_neg hd] at hok
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
      obtain ⟨⟨⟨h12, hj⟩, hdj⟩, hg⟩ := hok
      obtain ⟨hmem, -⟩ := ih _ hj (by omega)
      refine ⟨?_, h12⟩
      rw [← hdj, Function.iterate_succ_apply', ← hg]
      exact mem_vstep_of hmem _

theorem ent_memN {a : ℕ} {E : List Ent} (h : chkE a E = true) (N : ℕ) (hN : 12 ≤ N) :
    ∀ k < E.length, (E.getD k d0).1 ∈ vstep^[N] {a} := by
  intro k hk
  obtain ⟨hmem, h12⟩ := ent_mem h k hk
  have hsub := iter_mono {a} (E.getD k d0).2.1 (N - (E.getD k d0).2.1)
  rw [Nat.add_sub_of_le (Nat.le_trans h12 hN)] at hsub
  exact Finset.mem_of_subset hsub hmem

theorem ents_subN {a : ℕ} {E : List Ent} (h : chkE a E = true) (N : ℕ) (hN : 12 ≤ N) :
    (E.map Prod.fst).toFinset ⊆ vstep^[N] {a} := by
  refine Finset.subset_iff.2 fun m hm => ?_
  rw [List.mem_toFinset, List.mem_map] at hm
  obtain ⟨e, he, rfl⟩ := hm
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem he
  have h1 := ent_memN h N hN k hk
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, hke] at h1

theorem orbit_eq (a : E5) (c : ℕ) (E : List Ent) (ha : a ≠ 0) (hrk : rk a = c)
    (hchk : chkE (encV a) E = true) (hcard : (rkFibre c).card = E.length)
    (hnd : (E.map Prod.fst).Nodup) : orbitFin 12 a = (rkFibre c).image encV := by
  have h1 : orbitFin 12 a ⊆ (rkFibre c).image encV := orbit_sub_img a c ha hrk 12
  have h2 : (E.map Prod.fst).toFinset ⊆ orbitFin 12 a := ents_subN hchk 12 (Nat.le_refl 12)
  have hc1 : ((rkFibre c).image encV).card = E.length := by
    rw [Finset.card_image_of_injective _ encV_injective, hcard]
  have hc2 : (E.map Prod.fst).toFinset.card = E.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  exact Finset.eq_of_subset_of_card_le h1 (by rw [hc1, ← hc2]; exact Finset.card_le_card h2)

end CertificateChecks.MonsterExist.P5

end
