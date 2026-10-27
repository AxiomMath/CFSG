module

public import CFSG.RankThree.Native.ONTriplePresInputs
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import Certificates.Kernel.Misc.Coset.XON1
public import Certificates.Kernel.Misc.Coset.XON2
public import Certificates.Kernel.Misc.Coset.XON3
public import Certificates.Kernel.Misc.Coset.XON4
public import Certificates.Kernel.Misc.Coset.XON5
public import Certificates.Kernel.Misc.Coset.XON6
public import Certificates.Kernel.Misc.Coset.ONRoute

public section

namespace CertificateChecks.KernelMiscCoset.C8144

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.RankThree.Native.ONTriple CFSG.Certificates

theorem r1 : C1.map encW = CFSG.KBRoute.XON1.rels := by decide +kernel
theorem r2 : C2.map encW = CFSG.KBRoute.XON2.rels := by decide +kernel
theorem r3 : C3.map encW = CFSG.KBRoute.XON3.rels := by decide +kernel
theorem r4 : C4.map encW = CFSG.KBRoute.XON4.rels := by decide +kernel
theorem r5 : C5.map encW = CFSG.KBRoute.XON5.rels := by decide +kernel
theorem r6 : C6.map encW = CFSG.KBRoute.XON6.rels := by decide +kernel

theorem w1 : CFSG.KBRoute.XON1.T1.words =
    (subsetOf (subsetOf 8 [0, 1, 2, 3, 4, 5]).length [0, 2, 3, 4, 5]).map
      fun x => [(x.val, true)] := by decide +kernel
theorem w2 : CFSG.KBRoute.XON2.T1.words =
    (subsetOf (subsetOf (subsetOf 8 [0, 1, 2, 3, 4, 5]).length [0, 2, 3, 4, 5]).length
      [0, 2, 3, 4]).map fun x => [(x.val, true)] := by decide +kernel
theorem w3 : CFSG.KBRoute.XON3.T1.words = (subsetOf _ [1, 2, 3]).map
    (fun x : Fin (subsetOf (subsetOf (subsetOf 8 [0, 1, 2, 3, 4, 5]).length [0, 2, 3, 4, 5]).length
      [0, 2, 3, 4]).length => [(x.val, true)]) := by decide +kernel
theorem w4 : CFSG.KBRoute.XON4.T1.words = (subsetOf _ [1, 2]).map
    (fun x : Fin (subsetOf (subsetOf (subsetOf (subsetOf 8 [0, 1, 2, 3, 4, 5]).length
      [0, 2, 3, 4, 5]).length [0, 2, 3, 4]).length [1, 2, 3]).length => [(x.val, true)]) := by
  decide +kernel
theorem w5 : CFSG.KBRoute.XON5.T1.words = (subsetOf _ [1]).map
    (fun x : Fin (subsetOf (subsetOf (subsetOf (subsetOf (subsetOf 8 [0, 1, 2, 3, 4, 5]).length
      [0, 2, 3, 4, 5]).length [0, 2, 3, 4]).length [1, 2, 3]).length [1, 2]).length =>
      [(x.val, true)]) := by decide +kernel

theorem card_coxeter_le :
    Finite (PG (subsetOf 8 [0, 1, 2, 3, 4, 5]).length C1) ∧
    Nat.card (PG (subsetOf 8 [0, 1, 2, 3, 4, 5]).length C1) ≤ 3753792 := by
  have h6 := XON6.t1
  unfold CFSG.KBRoute.XON6.T1.ok at h6
  obtain ⟨f6, c6⟩ := card_le_of_tableOk C6 r6 h6 (by decide) CFSG.KBRoute.XON6.top rfl
  have h5 := XON5.t1
  unfold CFSG.KBRoute.XON5.T1.ok at h5
  obtain ⟨i5, j5⟩ := genSub_index_le_of_tableOk C5 r5 h5 (by decide) CFSG.KBRoute.XON5.top _ w5
  obtain ⟨f5, c5⟩ := card_le_of_genSub_index C5 _ i5 j5
  have h4 := XON4.t1
  unfold CFSG.KBRoute.XON4.T1.ok at h4
  obtain ⟨i4, j4⟩ := genSub_index_le_of_tableOk C4 r4 h4 (by decide) CFSG.KBRoute.XON4.top _ w4
  obtain ⟨f4, c4⟩ := card_le_of_genSub_index C4 _ i4 j4
  have h3 := XON3.t1
  unfold CFSG.KBRoute.XON3.T1.ok at h3
  obtain ⟨i3, j3⟩ := genSub_index_le_of_tableOk C3 r3 h3 (by decide) CFSG.KBRoute.XON3.top _ w3
  obtain ⟨f3, c3⟩ := card_le_of_genSub_index C3 _ i3 j3
  have h2 := XON2.t1
  unfold CFSG.KBRoute.XON2.T1.ok at h2
  obtain ⟨i2, j2⟩ := genSub_index_le_of_tableOk C2 r2 h2 (by decide) CFSG.KBRoute.XON2.top _ w2
  obtain ⟨f2, c2⟩ := card_le_of_genSub_index C2 _ i2 j2
  have h1 := XON1.t1
  unfold CFSG.KBRoute.XON1.T1.ok at h1
  obtain ⟨i1, j1⟩ := genSub_index_le_of_tableOk C1 r1 h1 (by decide) CFSG.KBRoute.XON1.top _ w1
  obtain ⟨f1, c1⟩ := card_le_of_genSub_index C1 _ i1 j1
  refine ⟨f1, ?_⟩
  have := c1.trans <| Nat.mul_le_mul_left _ <| c2.trans <| Nat.mul_le_mul_left _ <|
    c3.trans <| Nat.mul_le_mul_left _ <| c4.trans <| Nat.mul_le_mul_left _ <|
    c5.trans <| Nat.mul_le_mul_left _ c6
  exact this.trans (by norm_num)

section FHat

variable {e₁ e₂ e₃ : ℕ}

noncomputable abbrev zz (e₁ e₂ e₃ : ℕ) : PG 8 (coverRels e₁ e₂ e₃) := PresentedGroup.of 7

theorem rel_one {e₁ e₂ e₃ : ℕ} {w : List (Fin 8 × Bool)} (hw : w ∈ coverRels e₁ e₂ e₃) :
    KB.sword (pgGen (coverRels e₁ e₂ e₃)) (encW w) = 1 := by
  rw [sword_pgGen]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

theorem sword_z : KB.sword (pgGen (coverRels e₁ e₂ e₃)) [(7, true)] = zz e₁ e₂ e₃ := by
  simp [KB.sword, pgGen]

theorem sword_zinv : KB.sword (pgGen (coverRels e₁ e₂ e₃)) [(7, false)] = (zz e₁ e₂ e₃)⁻¹ := by
  simp [KB.sword, pgGen]

theorem sword_append' (gen : ℕ → PG 8 (coverRels e₁ e₂ e₃)) (u v : List (ℕ × Bool)) :
    KB.sword gen (u ++ v) = KB.sword gen u * KB.sword gen v := by
  simp [KB.sword, List.map_append, List.prod_append]

theorem z_pow_three : zz e₁ e₂ e₃ ^ 3 = 1 := by
  have h := rel_one (w := [(7, true), (7, true), (7, true)]) (e₁ := e₁) (e₂ := e₂) (e₃ := e₃)
    (by simp [coverRels])
  rw [show encW [((7 : Fin 8), true), (7, true), (7, true)] = [(7, true)] ++ [(7, true)] ++
    [(7, true)] from rfl, sword_append', sword_append', sword_z] at h
  rw [pow_three]
  exact (mul_assoc _ _ _).symm.trans h

theorem z_comm (i : Fin 8) : zz e₁ e₂ e₃ * PresentedGroup.of i = PresentedGroup.of i * zz e₁ e₂ e₃ := by
  have key : ∀ i : Fin 7, zz e₁ e₂ e₃ * PresentedGroup.of i.castSucc =
      PresentedGroup.of i.castSucc * zz e₁ e₂ e₃ := by
    intro i
    have h := rel_one (w := [(7, true), (i.castSucc, true), (7, false), (i.castSucc, false)])
      (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) (by fin_cases i <;> simp [coverRels])
    have e : encW [((7 : Fin 8), true), (i.castSucc, true), (7, false), (i.castSucc, false)] =
        [(7, true)] ++ [(i.val, true)] ++ [(7, false)] ++ [(i.val, false)] := rfl
    have hi : (i.val : ℕ) < 8 := by omega
    rw [e, sword_append', sword_append', sword_append', sword_z, sword_zinv] at h
    have h1 : KB.sword (pgGen (coverRels e₁ e₂ e₃)) [(i.val, true)] =
        PresentedGroup.of i.castSucc := by simp [KB.sword, pgGen, hi]; rfl
    have h2 : KB.sword (pgGen (coverRels e₁ e₂ e₃)) [(i.val, false)] =
        (PresentedGroup.of i.castSucc)⁻¹ := by simp [KB.sword, pgGen, hi]; rfl
    rw [h1, h2] at h
    have := mul_inv_eq_one.mp h
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · exact key j
  · rfl

theorem z_mem_center : zz e₁ e₂ e₃ ∈ Subgroup.center (PG 8 (coverRels e₁ e₂ e₃)) := by
  rw [Subgroup.mem_center_iff]
  intro g
  have hcl : g ∈ Subgroup.closure (Set.range (PresentedGroup.of : Fin 8 → PG 8 (coverRels e₁ e₂ e₃))) := by
    rw [PresentedGroup.closure_range_of]; trivial
  refine Subgroup.closure_induction (p := fun g _ => g * zz e₁ e₂ e₃ = zz e₁ e₂ e₃ * g) ?_ ?_ ?_ ?_ hcl
  · rintro _ ⟨i, rfl⟩
    exact (z_comm i).symm
  · simp
  · intro a b _ _ ha hb
    exact Commute.mul_left (a := a) (b := b) (c := zz e₁ e₂ e₃) ha hb
  · intro a _ ha
    exact Commute.inv_left (a := a) (b := zz e₁ e₂ e₃) ha

noncomputable abbrev zSub (e₁ e₂ e₃ : ℕ) : Subgroup (PG 8 (coverRels e₁ e₂ e₃)) :=
  Subgroup.zpowers (zz e₁ e₂ e₃)

instance : (zSub e₁ e₂ e₃).Normal :=
  Subgroup.normal_of_le_center ((Subgroup.zpowers_le).2 z_mem_center)

theorem card_FHat_le_of_rels
    (h : ∀ r ∈ CFSG.KBRoute.ON.rels, r ∈ (coverRels e₁ e₂ e₃).map encW ∨
      r ++ [(7, false)] ∈ (coverRels e₁ e₂ e₃).map encW) :
    Finite (PG 8 (coverRels e₁ e₂ e₃)) ∧ Nat.card (PG 8 (coverRels e₁ e₂ e₃)) ≤ 1382446517760 := by
  set F := PG 8 (coverRels e₁ e₂ e₃)
  set N := zSub e₁ e₂ e₃
  let q : F →* F ⧸ N := QuotientGroup.mk' N
  let gen : ℕ → F ⧸ N := fun g => q (pgGen (coverRels e₁ e₂ e₃) g)
  have hsw : ∀ r, KB.sword gen r = q (KB.sword (pgGen (coverRels e₁ e₂ e₃)) r) := by
    intro r
    simp only [KB.sword, gen, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply]
    split <;> simp
  have hzq : q (zz e₁ e₂ e₃) = 1 := (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)
  have hrels : ∀ r ∈ CFSG.KBRoute.ON.rels, KB.sword gen r = 1 := by
    intro r hr
    rw [hsw]
    rcases h r hr with h1 | h1
    · obtain ⟨w, hw, hwr⟩ := List.mem_map.1 h1
      rw [← hwr, rel_one hw, map_one]
    · obtain ⟨w, hw, hwr⟩ := List.mem_map.1 h1
      have := rel_one hw
      rw [hwr, sword_append', sword_zinv] at this
      rw [eq_of_mul_inv_eq_one this, hzq]
  have hgen : Subgroup.closure (gen '' {g | g < 7}) = ⊤ := by
    have hall : Subgroup.closure (gen '' {g | g < 8}) = ⊤ := by
      have : gen '' {g | g < 8} = q '' (pgGen (coverRels e₁ e₂ e₃) '' {g | g < 8}) := by
        rw [Set.image_image]
      rw [this, ← MonoidHom.map_closure, closure_pgGen, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top]
      exact QuotientGroup.mk'_surjective N
    rw [eq_top_iff, ← hall, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    by_cases h7 : g < 7
    · exact Subgroup.subset_closure ⟨g, h7, rfl⟩
    · have : g = 7 := by simp only [Set.mem_ofPred_eq] at hg; omega
      subst this
      have : gen 7 = 1 := by simp only [gen, pgGen]; simpa using hzq
      rw [this]
      exact Subgroup.one_mem _
  obtain ⟨hQf, hQc⟩ := card_le_of_ON_rels gen hrels hgen
  have hNc : Nat.card N ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one z_pow_three)
  have hNf : Finite N := by
    have hpos : 0 < orderOf (zz e₁ e₂ e₃) :=
      Nat.pos_of_dvd_of_pos (orderOf_dvd_of_pow_eq_one z_pow_three) (by norm_num)
    exact Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers]; omega)
  have hFf : Finite F := Finite.of_subgroup_quotient N
  refine ⟨hFf, ?_⟩
  rw [N.card_eq_card_quotient_mul_card_subgroup]
  calc Nat.card (F ⧸ N) * Nat.card N ≤ 460815505920 * 3 := Nat.mul_le_mul hQc hNc
    _ = 1382446517760 := by norm_num

end FHat

theorem card_one_le :
    Finite (PG 8 (coverRels 1 1 1)) ∧ Nat.card (PG 8 (coverRels 1 1 1)) ≤ 1382446517760 :=
  card_FHat_le_of_rels (by decide +kernel)

theorem card_zero_le :
    Finite (PG 8 (coverRels 0 0 0)) ∧ Nat.card (PG 8 (coverRels 0 0 0)) ≤ 1382446517760 :=
  card_FHat_le_of_rels (by decide +kernel)

end CertificateChecks.KernelMiscCoset.C8144

end
