module

public import CFSG.Sporadic.Recognition.HNMultiplierExact

public section

namespace CFSG.Sporadic.Recognition.HNMultiplier

open CFSG.CosetTable CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.Sporadic.Recognition.CoverTransfer CFSG.Sporadic.Recognition.CoverBootstrap Subgroup

theorem comm_of_central_comm {G : Type*} [Group G] {b t z : G} (hz : z ∈ center G)
    (hzz : z * z = 1) (hb : b ^ 7 = 1) (hdef : t⁻¹ * b⁻¹ * t * b = z) : t * b = b * t := by
  have htb : t * b = b * t * z := by rw [← hdef]; group
  have key : ∀ n : ℕ, t * b ^ n = b ^ n * t * z ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hc : z ^ n * b = b * z ^ n := (Subgroup.mem_center_iff.mp (pow_mem hz n) b).symm
      calc t * b ^ (n + 1) = t * b ^ n * b := by rw [pow_succ, mul_assoc]
        _ = b ^ n * t * (z ^ n * b) := by rw [ih, mul_assoc (b ^ n * t)]
        _ = b ^ n * (t * b) * z ^ n := by rw [hc]; group
        _ = b ^ n * (b * t * z) * z ^ n := by rw [htb]
        _ = b ^ (n + 1) * t * z ^ (n + 1) := by rw [pow_succ, pow_succ]; group
  have h7 : t * z ^ 7 = t * 1 := by
    have := key 7
    rw [hb, one_mul, mul_one] at this
    rw [mul_one]
    exact this.symm
  have hz7 : z ^ 7 = 1 := mul_left_cancel h7
  have hz1 : z = 1 := by
    have e : z ^ 7 = z * (z * z) * (z * z) * (z * z) := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e, hzz] at hz7
    simpa using hz7
  rw [htb, hz1, mul_one]

theorem comm_of_conj_central {G : Type*} [Group G] {b c g t w : G} (hw : w ∈ center G)
    (hc : c⁻¹ * t * c * t⁻¹ * t⁻¹ = w) (hg : g⁻¹ * c * b * c⁻¹ = 1) (hbt : t * b = b * t) :
    t * g = g * t := by
  have hg' : g = c * b * c⁻¹ := by
    rw [mul_assoc, mul_assoc] at hg
    have := inv_mul_eq_one.mp hg
    rw [this]; group
  have h1 : c⁻¹ * t * c = w * t * t := by rw [← hc]; group
  have hwb : b * w = w * b := Subgroup.mem_center_iff.mp hw b
  have h2 : b * (c⁻¹ * t * c) = c⁻¹ * t * c * b := by
    rw [h1]
    calc b * (w * t * t) = b * w * t * t := by group
      _ = w * (b * t) * t := by rw [hwb]; group
      _ = w * (t * b) * t := by rw [hbt]
      _ = w * t * (b * t) := by group
      _ = w * t * (t * b) := by rw [hbt]
      _ = w * t * t * b := by group
  rw [hg']
  calc t * (c * b * c⁻¹) = c * ((c⁻¹ * t * c) * b) * c⁻¹ := by group
    _ = c * (b * (c⁻¹ * t * c)) * c⁻¹ := by rw [h2]
    _ = c * b * c⁻¹ * t := by group

noncomputable def hnPCtoPP : PC →* PG 7 hnCoverPlus :=
  PresentedGroup.toGroup (f := (PresentedGroup.of : Fin 7 → PG 7 hnCoverPlus)) fun r hr => by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [← mk_eq_lift_of]
    exact PresentedGroup.one_of_mem (List.mem_map_of_mem (List.mem_append_left _ hw))

theorem hnPCtoPP_hx (i : Fin 7) : hnPCtoPP (hx i) = PresentedGroup.of i :=
  PresentedGroup.toGroup.of _

theorem lift_of_PP_eq :
    FreeGroup.lift (PresentedGroup.of : Fin 7 → PG 7 hnCoverPlus) =
      hnPCtoPP.comp (FreeGroup.lift hx) :=
  FreeGroup.ext_hom _ _ fun i => by
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of, hnPCtoPP_hx]

theorem rel_center_PP {r : List (Fin 7 × Bool)} (hr : r ∈ hnRels) :
    FreeGroup.lift (PresentedGroup.of : Fin 7 → PG 7 hnCoverPlus) (FreeGroup.mk r) ∈
      center (PG 7 hnCoverPlus) := by
  rw [lift_of_PP_eq, MonoidHom.comp_apply]
  refine mem_center_of_comm_gens fun i => ?_
  have h := congrArg hnPCtoPP
    (Subgroup.mem_center_iff.mp (lift_coverGen_rel_center (cw := hnCommWord) hr) (hx i))
  rwa [map_mul, map_mul, hnPCtoPP_hx] at h

theorem rel_sq_PP {r : List (Fin 7 × Bool)} (hr : r ∈ hnRels) :
    FreeGroup.lift (PresentedGroup.of : Fin 7 → PG 7 hnCoverPlus) (FreeGroup.mk r) *
      FreeGroup.lift (PresentedGroup.of : Fin 7 → PG 7 hnCoverPlus) (FreeGroup.mk r) = 1 := by
  rw [lift_of_PP_eq, MonoidHom.comp_apply, ← map_mul,
    lift_coverGen_rel_sq (R := hnRels) (cw := hnCommWord) hr, map_one]

theorem plain1_PP {w : List (Fin 7 × Bool)} (hw : w ∈ hnPlain1) :
    FreeGroup.lift (PresentedGroup.of : Fin 7 → PG 7 hnCoverPlus) (FreeGroup.mk w) = 1 := by
  rw [← mk_eq_lift_of]
  exact PresentedGroup.one_of_mem
    (List.mem_map_of_mem (List.mem_append_right _ (List.mem_append_left _ hw)))

noncomputable abbrev hnTP : Subgroup (PG 7 hnCoverPlus) :=
  Subgroup.closure {PresentedGroup.of 0, PresentedGroup.of 1}

theorem hnPP_t_comm_b :
    (PresentedGroup.of 6 : PG 7 hnCoverPlus) * PresentedGroup.of 0 =
      PresentedGroup.of 0 * PresentedGroup.of 6 := by
  have hr : [((6 : Fin 7), false), (0, false), (6, true), (0, true)] ∈ hnRels := by decide
  have hv : FreeGroup.lift (PresentedGroup.of : Fin 7 → PG 7 hnCoverPlus)
      (FreeGroup.mk [((6 : Fin 7), false), (0, false), (6, true), (0, true)]) =
      (PresentedGroup.of 6)⁻¹ * (PresentedGroup.of 0)⁻¹ * PresentedGroup.of 6 *
        PresentedGroup.of 0 := by
    simp [FreeGroup.lift_mk, mul_assoc]
  have hb : FreeGroup.lift (PresentedGroup.of : Fin 7 → PG 7 hnCoverPlus)
      (FreeGroup.mk [((0 : Fin 7), true), (0, true), (0, true), (0, true), (0, true), (0, true),
        (0, true)]) = 1 :=
    plain1_PP (by decide)
  refine comm_of_central_comm (rel_center_PP hr) (rel_sq_PP hr) ?_ hv.symm
  simpa [FreeGroup.lift_mk, pow_succ, mul_assoc] using hb

theorem hnPP_t_comm_g :
    (PresentedGroup.of 6 : PG 7 hnCoverPlus) * PresentedGroup.of 1 =
      PresentedGroup.of 1 * PresentedGroup.of 6 := by
  have hr : [((2 : Fin 7), false), (6, true), (2, true), (6, false), (6, false)] ∈ hnRels := by
    decide
  have hv : FreeGroup.lift (PresentedGroup.of : Fin 7 → PG 7 hnCoverPlus)
      (FreeGroup.mk [((2 : Fin 7), false), (6, true), (2, true), (6, false), (6, false)]) =
      (PresentedGroup.of 2)⁻¹ * PresentedGroup.of 6 * PresentedGroup.of 2 *
        (PresentedGroup.of 6)⁻¹ * (PresentedGroup.of 6)⁻¹ := by
    simp [FreeGroup.lift_mk, mul_assoc]
  have hg : FreeGroup.lift (PresentedGroup.of : Fin 7 → PG 7 hnCoverPlus)
      (FreeGroup.mk [((1 : Fin 7), false), (2, true), (0, true), (2, false)]) = 1 :=
    plain1_PP (by decide)
  refine comm_of_conj_central (b := PresentedGroup.of 0) (rel_center_PP hr) hv.symm ?_
    hnPP_t_comm_b
  simpa [FreeGroup.lift_mk, mul_assoc] using hg

theorem hnTP_le_centralizer :
    hnTP ≤ Subgroup.centralizer {(PresentedGroup.of 6 : PG 7 hnCoverPlus)} := by
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  · exact hnPP_t_comm_b.symm
  · exact hnPP_t_comm_g.symm

theorem hnTP_conj_t {x : PG 7 hnCoverPlus} (hx : x ∈ hnTP) :
    (PresentedGroup.of 6)⁻¹ * x * PresentedGroup.of 6 = x := by
  have h := Subgroup.mem_centralizer_singleton_iff.mp (hnTP_le_centralizer hx)
  rw [mul_assoc, h, inv_mul_cancel_left]

end CFSG.Sporadic.Recognition.HNMultiplier

end
