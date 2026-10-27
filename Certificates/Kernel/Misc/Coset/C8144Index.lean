module

public import Certificates.Kernel.Misc.Coset.C8144

public section

namespace CertificateChecks.KernelMiscCoset.C8144

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.RankThree.Native.ONTriple CFSG.Certificates
open scoped Pointwise

theorem on_T1_words : CFSG.KBRoute.ON.T1.words =
    (subsetOf 8 [0, 1, 2, 3, 4, 5]).map fun x => [(x.val, true)] := by decide +kernel

theorem on_rels_one : ∀ r ∈ CFSG.KBRoute.ON.rels, r ∈ (coverRels 1 1 1).map encW ∨
    r ++ [(7, false)] ∈ (coverRels 1 1 1).map encW := by decide +kernel

theorem index_one_le :
    (genSub {r : FreeGroup (Fin 8) | r ∈ (coverRels 1 1 1).map FreeGroup.mk}
      (subsetOf 8 [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin 8) | r ∈ (coverRels 1 1 1).map FreeGroup.mk}
      (subsetOf 8 [0, 1, 2, 3, 4, 5])).index ≤ 368280 := by
  have hF : Finite (PG 8 (coverRels 1 1 1)) := card_one_le.1
  set G0 := genSub {r : FreeGroup (Fin 8) | r ∈ (coverRels 1 1 1).map FreeGroup.mk}
    (subsetOf 8 [0, 1, 2, 3, 4, 5]) with hG0
  set N := zSub 1 1 1
  let q : PG 8 (coverRels 1 1 1) →* PG 8 (coverRels 1 1 1) ⧸ N := QuotientGroup.mk' N
  let gen : ℕ → PG 8 (coverRels 1 1 1) ⧸ N := fun g => q (pgGen (coverRels 1 1 1) g)
  have hsw : ∀ r, KB.sword gen r = q (KB.sword (pgGen (coverRels 1 1 1)) r) := by
    intro r
    simp only [KB.sword, gen, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro x _
    simp only [Function.comp_apply]
    split <;> simp
  have hzq : q (zz 1 1 1) = 1 := (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)
  have hrels : ∀ r ∈ CFSG.KBRoute.ON.rels, KB.sword gen r = 1 := by
    intro r hr
    rw [hsw]
    rcases on_rels_one r hr with h1 | h1
    · obtain ⟨w, hw, hwr⟩ := List.mem_map.1 h1
      rw [← hwr, rel_one hw, map_one]
    · obtain ⟨w, hw, hwr⟩ := List.mem_map.1 h1
      have := rel_one hw
      rw [hwr, sword_append', sword_zinv] at this
      rw [eq_of_mul_inv_eq_one this, hzq]
  have hgen : Subgroup.closure (gen '' {g | g < 7}) = ⊤ := by
    have hall : Subgroup.closure (gen '' {g | g < 8}) = ⊤ := by
      have : gen '' {g | g < 8} = q '' (pgGen (coverRels 1 1 1) '' {g | g < 8}) := by
        rw [Set.image_image]
      rw [this, ← MonoidHom.map_closure, closure_pgGen, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top]
      exact QuotientGroup.mk'_surjective N
    rw [eq_top_iff, ← hall, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    by_cases h7 : g < 7
    · exact Subgroup.subset_closure ⟨g, h7, rfl⟩
    · have hg' : g < 8 := hg
      have : g = 7 := by omega
      subst this
      have : gen 7 = 1 := by simp only [gen, pgGen]; simpa using hzq
      rw [this]
      exact Subgroup.one_mem _
  obtain ⟨h1, -, -, htop, -, -⟩ := CertificateChecks.KernelBounds.ON.facts_holds
  delta CFSG.KBRoute.ON.T1.ok at h1
  obtain ⟨-, -, hN⟩ := KB.tableOk_sound gen hrels h1
  have hset : {g | KB.inAlpha CFSG.KBRoute.ON.T1.amap g} = {g | g < 7} :=
    Set.ext fun g => KB.topOk_sound (by norm_num) htop g
  have hK : KB.alphaSub gen CFSG.KBRoute.ON.T1.amap = ⊤ := by
    rw [KB.alphaSub, hset, hgen]
  have e : ∀ ws : List (List (ℕ × Bool)),
      KB.wordSub gen ws = (KB.wordSub (pgGen (coverRels 1 1 1)) ws).map q := by
    intro ws
    rw [KB.wordSub, KB.wordSub, MonoidHom.map_closure, Set.image_image]
    exact congrArg Subgroup.closure (Set.image_congr fun r _ => hsw r)
  have hmap : KB.wordSub gen CFSG.KBRoute.ON.T1.words = G0.map q := by
    rw [e, on_T1_words, wordSub_letters]
  rw [hK, Subgroup.relIndex_top_right, hmap] at hN
  have hker : q.ker = N := QuotientGroup.ker_mk' N
  have hKidx : (G0 ⊔ N).index = (G0.map q).index := by
    have hm : (G0 ⊔ N).map q = G0.map q := by
      rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 hker.ge, sup_bot_eq]
    have hle : q.ker ≤ G0 ⊔ N := by
      rw [hker]
      exact le_sup_right
    rw [← hm, ← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N),
      Subgroup.comap_map_eq_self hle]
  have hNc : Nat.card N ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one z_pow_three)
  have hrel : G0.relIndex (G0 ⊔ N) ≤ 3 := by
    have hc := Subgroup.relIndex_mul_card (H := G0) (K := G0 ⊔ N)
    rw [inf_of_le_left le_sup_left] at hc
    have hset : ((G0 ⊔ N : Subgroup _) : Set (PG 8 (coverRels 1 1 1))) =
        (G0 : Set (PG 8 (coverRels 1 1 1))) * (N : Set (PG 8 (coverRels 1 1 1))) :=
      Subgroup.mul_normal G0 N
    have hmul := Set.natCard_mul_le (s := (G0 : Set (PG 8 (coverRels 1 1 1))))
      (t := (N : Set (PG 8 (coverRels 1 1 1))))
    rw [← hset] at hmul
    have hpos : 0 < Nat.card G0 := Nat.card_pos
    have : G0.relIndex (G0 ⊔ N) * Nat.card G0 ≤ 3 * Nat.card G0 := by
      rw [hc]
      calc Nat.card (G0 ⊔ N : Subgroup _) ≤ Nat.card G0 * Nat.card N := hmul
        _ ≤ Nat.card G0 * 3 := Nat.mul_le_mul_left _ hNc
        _ = 3 * Nat.card G0 := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right this hpos
  refine ⟨inferInstance, ?_⟩
  rw [← Subgroup.relIndex_mul_index (le_sup_left : G0 ≤ G0 ⊔ N), hKidx]
  calc G0.relIndex (G0 ⊔ N) * (G0.map q).index ≤ 3 * 122760 := Nat.mul_le_mul hrel hN
    _ = 368280 := by norm_num

end CertificateChecks.KernelMiscCoset.C8144

end
