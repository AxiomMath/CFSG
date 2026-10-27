module

public import Certificates.Kernel.Fi23U3.W6
public import CFSG.Certificates.Kernel.InvWordsSound
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Cover3Sound

public section

namespace CFSG.KD.Fi23W6

open CFSG.SectionRank.Native CFSG.CosetTable CFSG.KC.InvWords CFSG.LieType.Multipliers
  CFSG.Sporadic.Recognition.CoverRecipe CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary

local instance : NeZero fi23U3Cover3.m := ⟨by decide⟩

theorem sq_mem :
    ∀ i : Fin fi23U3Cover3.m, List.replicate 2 (i, true) ∈ powWords fi23U3Cover3.ordF := by
  decide +kernel

theorem x1x2_pow_six :
    ((PresentedGroup.of 1 : PG 4 fi23U3Cover3.cover) * PresentedGroup.of 2) ^ 6 = 1 := by
  let x : Fin 4 → PG 4 fi23U3Cover3.cover := fun i => PresentedGroup.of i
  have hrel : ∀ w ∈ fi23U3Cover3.cover,
      (PresentedGroup.mk _ (FreeGroup.mk w) : PG 4 fi23U3Cover3.cover) = 1 :=
    fun w hw => PresentedGroup.one_of_mem (List.mem_map_of_mem hw)
  have hx2 : ∀ i, x i * x i = 1 := by
    intro i
    have h : (PresentedGroup.mk _ (FreeGroup.mk (List.replicate 2 (i, true))) :
        PG 4 fi23U3Cover3.cover) = 1 := hrel _ (mem_cover₃Words.2 (Or.inr (Or.inr (sq_mem i))))
    rw [mk_replicate, map_pow] at h
    rw [← pow_two]
    exact h
  have hxinv : ∀ i, (x i)⁻¹ = x i := fun i => (eq_inv_of_mul_eq_one_left (hx2 i)).symm
  let g : ℕ → PG 4 fi23U3Cover3.cover := fun n => if h : n < 4 then x ⟨n, h⟩ else 1
  have hg : ∀ n, g n * g n = 1 := by
    intro n
    by_cases h : n < 4
    · simp only [g, dif_pos h]
      exact hx2 _
    · simp only [g, dif_neg h, mul_one]
  have hgx : ∀ i : Fin 4, g i.val = x i := fun i => dif_pos i.isLt
  have hev : ∀ r : List (Fin 4 × Bool),
      (PresentedGroup.mk _ (FreeGroup.mk r) : PG 4 fi23U3Cover3.cover) =
        ev g (r.map fun p => p.1.val) := by
    intro r
    induction r with
    | nil => exact map_one _
    | cons p r ih =>
      obtain ⟨i, b⟩ := p
      have h1 : FreeGroup.mk ((i, b) :: r) = FreeGroup.mk [(i, b)] * FreeGroup.mk r :=
        by rw [FreeGroup.mul_mk, List.singleton_append]
      have h2 : (PresentedGroup.mk _ (FreeGroup.mk [(i, b)]) : PG 4 fi23U3Cover3.cover) = x i := by
        cases b with
        | true => rfl
        | false =>
          have : FreeGroup.mk [(i, false)] = (FreeGroup.of i)⁻¹ := by
            simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]
          rw [this, map_inv]
          exact hxinv i
      rw [h1, map_mul, h2, ih]
      simp only [List.map_cons, ev_cons, hgx]
  have hR : ∀ r ∈ rels0, Good (ev g r) := by
    intro r0 hr0
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hr0
    have hcm : ofCodes 4 c ∈ fi23U3Cover3.rels := List.mem_map_of_mem hc
    have hmap : (ofCodes 4 c).map (fun p => p.1.val) = c.map fun x => x / 2 % 4 := by
      simp [ofCodes, Fin.val_ofNat]
    rw [← hmap, ← hev]
    set Z := (PresentedGroup.mk _ (FreeGroup.mk (ofCodes 4 c)) : PG 4 fi23U3Cover3.cover)
    have hcomm : ∀ i : Fin 4, x i * Z = Z * x i := by
      intro i
      have h : (PresentedGroup.mk _ (FreeGroup.mk (commWord [(i, true)] (ofCodes 4 c))) :
          PG 4 fi23U3Cover3.cover) = 1 := hrel _ (mem_cover₃Words.2 (Or.inl
        (List.mem_append_left _ (List.mem_flatMap.2 ⟨i, List.mem_finRange i,
          List.mem_map_of_mem hcm⟩))))
      rw [mk_commWord, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h
      exact h
    refine ⟨fun y => ?_, ?_⟩
    · have htop : Subgroup.closure
          (Set.range (PresentedGroup.of : Fin 4 → PG 4 fi23U3Cover3.cover)) = ⊤ :=
        PresentedGroup.closure_range_of _
      have hle : Subgroup.closure
          (Set.range (PresentedGroup.of : Fin 4 → PG 4 fi23U3Cover3.cover)) ≤
          Subgroup.centralizer ({Z} : Set (PG 4 fi23U3Cover3.cover)) := by
        rw [Subgroup.closure_le]
        rintro _ ⟨i, rfl⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        exact hcomm i
      have hy := hle (by rw [htop]; exact Subgroup.mem_top y)
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      exact hy.symm
    · have h : (PresentedGroup.mk _ (FreeGroup.mk (ofCodes 4 c ++ ofCodes 4 c ++ ofCodes 4 c)) :
          PG 4 fi23U3Cover3.cover) = 1 :=
        hrel _ (mem_cover₃Words.2 (Or.inr (Or.inl (List.mem_map_of_mem (f :=
          fun r => r ++ r ++ r) hcm))))
      rw [← FreeGroup.mul_mk, ← FreeGroup.mul_mk, map_mul, map_mul] at h
      rw [pow_three, ← mul_assoc]
      exact h
  have hW := good_of_invCheck hg hR check
  have hevW : ev g [1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 2] = (x 1 * x 2) ^ 6 := by
    have h1 : g 1 = x 1 := hgx 1
    have h2 : g 2 = x 2 := hgx 2
    simp only [ev_cons, ev_nil, h1, h2, pow_succ, pow_zero, one_mul, mul_one, mul_assoc]
  rw [hevW] at hW
  change (x 1 * x 2) ^ 6 = 1
  have hconj : x 1 * (x 1 * x 2) ^ 6 * (x 1)⁻¹ = ((x 1 * x 2) ^ 6)⁻¹ := by
    have h : x 1 * (x 1 * x 2) * (x 1)⁻¹ = (x 1 * x 2)⁻¹ := by
      rw [mul_inv_rev, hxinv, hxinv, ← mul_assoc, hx2, one_mul]
    rw [← conj_pow, h, inv_pow]
  have hcen : x 1 * (x 1 * x 2) ^ 6 * (x 1)⁻¹ = (x 1 * x 2) ^ 6 := by
    rw [← (hW.1 (x 1)).eq, mul_inv_cancel_right]
  have hsq : (x 1 * x 2) ^ 6 * (x 1 * x 2) ^ 6 = 1 := by
    rw [mul_eq_one_iff_eq_inv, ← hconj, hcen]
  have h3 := hW.2
  rw [pow_three, hsq, mul_one] at h3
  exact h3

end CFSG.KD.Fi23W6
