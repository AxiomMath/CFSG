module

public import Certificates.Kernel.Multipliers.L34HBase

set_option exponentiation.threshold 2048
set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelL34H

open CFSG.Certificates.LabZ CertificateChecks.KernelMult CFSG.LieType.Multipliers
  CFSG.LieType.Multipliers.L34 CFSG.LieType.Multipliers.L34Upper CFSG.CosetTable

@[expose] def ρ0 : List ℤ :=
  [0, -1, 0, 0, 0, 0, 0, 0, 0, 5]

theorem r0 : zprod gg 10 (fun d => ρ0.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.L34C.sY0 (by decide)

@[expose] def ρ1 : List ℤ :=
  [0, 0, 0, 0, -2, 0, 0, 0, 0, 0]

theorem r1 : zprod gg 10 (fun d => ρ1.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.L34C.sY1 (by decide)

@[expose] def ρ2 : List ℤ :=
  [8, 0, 0, -2, 0, 0, 0, 0, 0, 0]

theorem r2 : zprod gg 10 (fun d => ρ2.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.L34C.sY2 (by decide)

@[expose] def ρ3 : List ℤ :=
  [-11, -9, 1, 0, 6, 2, 0, -1, 0, 10]

theorem r3 : zprod gg 10 (fun d => ρ3.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.L34C.sY3 (by decide)

@[expose] def ρ4 : List ℤ :=
  [6, 15, 0, 2, -20, -4, 0, 0, -1, -20]

theorem r4 : zprod gg 10 (fun d => ρ4.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.L34C.sY4 (by decide)

@[expose] def ρ5 : List ℤ :=
  [-21, -45, 6, -7, 74, 8, 0, 0, -1, 70]

theorem r5 : zprod gg 10 (fun d => ρ5.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.L34C.sY5 (by decide)

@[expose] def ρ6 : List ℤ :=
  [33, 100, -12, 18, -172, -18, 0, 0, -1, -165]

theorem r6 : zprod gg 10 (fun d => ρ6.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.L34C.sY6 (by decide)

@[expose] def ρ7 : List ℤ :=
  [52, 64, -11, 7, -77, -12, 0, -1, 0, -75]

theorem r7 : zprod gg 10 (fun d => ρ7.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.L34C.sY7 (by decide)

@[expose] def ρ8 : List ℤ :=
  [-259, -39, 34, 21, -430, 28, -4, 0, -1, -380]

theorem r8 : zprod gg 10 (fun d => ρ8.getD d 0) = 1 :=
  rel_of _ (by decide) (by decide) CFSG.KD.L34C.sY8 (by decide)

@[expose] def rhos : List (List ℤ) :=
  [ρ0, ρ1, ρ2, ρ3, ρ4, ρ5, ρ6, ρ7, ρ8]

theorem rhos_one : ∀ ρ ∈ rhos, zprod gg 10 (fun d => ρ.getD d 0) = 1 := by
  intro ρ hρ
  simp only [rhos, List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact r0
  · exact r1
  · exact r2
  · exact r3
  · exact r4
  · exact r5
  · exact r6
  · exact r7
  · exact r8

@[expose] def c0 : List ℤ :=
  [18, -55, 6, 2, -1, -4, 0, -2, 0]

@[expose] def τ0 : List ℤ :=
  [0, 1, 0, 0, 0, 0, 0, 0, 5, 0]

theorem t0 : zprod gg 10 (fun d => τ0.getD d 0) = 1 :=
  zprod_target gg_comm 10 c0 rhos rhos_one _ (by decide)

@[expose] def c1 : List ℤ :=
  [14894, -42787, 5564, 1214, -1246, -38, 1228, -1250, 0]

@[expose] def τ1 : List ℤ :=
  [4, 0, 0, 0, 0, 4, 0, 36, 56, 0]

theorem t1 : zprod gg 10 (fun d => τ1.getD d 0) = 1 :=
  zprod_target gg_comm 10 c1 rhos rhos_one _ (by decide)

@[expose] def c2 : List ℤ :=
  [-896324, 2577054, -336140, -74760, 74670, -31, -74694, 74668, -1]

@[expose] def τ2 : List ℤ :=
  [4, 0, 0, 0, 0, 0, 4, 92, 56, 0]

theorem t2 : zprod gg 10 (fun d => τ2.getD d 0) = 1 :=
  zprod_target gg_comm 10 c2 rhos rhos_one _ (by decide)

@[expose] def c3 : List ℤ :=
  [22092, -63491, 8280, 1830, -1844, 2, 1842, -1842, 0]

@[expose] def τ3 : List ℤ :=
  [6, 0, 0, 0, 0, 0, 0, 12, 0, 0]

theorem t3 : zprod gg 10 (fun d => τ3.getD d 0) = 1 :=
  zprod_target gg_comm 10 c3 rhos rhos_one _ (by decide)

@[expose] def taus : List (List ℤ) :=
  [τ0, τ1, τ2, τ3]

theorem zprod_ten (g : ℕ → PG 2 hopfWs) (v : ℕ → ℤ) :
    zprod g 10 v = g 0 ^ v 0 * g 1 ^ v 1 * g 2 ^ v 2 * g 3 ^ v 3 * g 4 ^ v 4 * g 5 ^ v 5 *
      g 6 ^ v 6 * g 7 ^ v 7 * g 8 ^ v 8 * g 9 ^ v 9 := by
  simp only [zprod_succ, show zprod g 0 v = 1 from rfl, one_mul]

theorem g7 : gg 7 = 1 := gg_cover (i := 0) (by omega)

theorem g8 : gg 8 = 1 := gg_cover (i := 1) (by omega)

theorem z1_eq : z 1 = 1 := by
  have h := t0
  rw [zprod_ten] at h
  change gg 0 ^ (0 : ℤ) * gg 1 ^ (1 : ℤ) * gg 2 ^ (0 : ℤ) * gg 3 ^ (0 : ℤ) * gg 4 ^ (0 : ℤ) *
    gg 5 ^ (0 : ℤ) * gg 6 ^ (0 : ℤ) * gg 7 ^ (0 : ℤ) * gg 8 ^ (5 : ℤ) * gg 9 ^ (0 : ℤ) = 1 at h
  rw [g8] at h
  simp only [zpow_zero, zpow_one, one_zpow, one_mul, mul_one] at h
  rw [← gg_rel (by omega)]
  exact h

theorem z05 : z 0 ^ 4 * z 5 ^ 4 = 1 := by
  have h := t1
  rw [zprod_ten] at h
  change gg 0 ^ (4 : ℤ) * gg 1 ^ (0 : ℤ) * gg 2 ^ (0 : ℤ) * gg 3 ^ (0 : ℤ) * gg 4 ^ (0 : ℤ) *
    gg 5 ^ (4 : ℤ) * gg 6 ^ (0 : ℤ) * gg 7 ^ (36 : ℤ) * gg 8 ^ (56 : ℤ) * gg 9 ^ (0 : ℤ) = 1 at h
  rw [g7, g8, gg_rel (k := 0) (by omega), gg_rel (k := 5) (by omega)] at h
  simp only [zpow_zero, one_zpow, mul_one] at h
  exact_mod_cast h

theorem z06 : z 0 ^ 4 * z 6 ^ 4 = 1 := by
  have h := t2
  rw [zprod_ten] at h
  change gg 0 ^ (4 : ℤ) * gg 1 ^ (0 : ℤ) * gg 2 ^ (0 : ℤ) * gg 3 ^ (0 : ℤ) * gg 4 ^ (0 : ℤ) *
    gg 5 ^ (0 : ℤ) * gg 6 ^ (4 : ℤ) * gg 7 ^ (92 : ℤ) * gg 8 ^ (56 : ℤ) * gg 9 ^ (0 : ℤ) = 1 at h
  rw [g7, g8, gg_rel (k := 0) (by omega), gg_rel (k := 6) (by omega)] at h
  simp only [zpow_zero, one_zpow, mul_one] at h
  exact_mod_cast h

theorem z0_six : z 0 ^ 6 = 1 := by
  have h := t3
  rw [zprod_ten] at h
  change gg 0 ^ (6 : ℤ) * gg 1 ^ (0 : ℤ) * gg 2 ^ (0 : ℤ) * gg 3 ^ (0 : ℤ) * gg 4 ^ (0 : ℤ) *
    gg 5 ^ (0 : ℤ) * gg 6 ^ (0 : ℤ) * gg 7 ^ (12 : ℤ) * gg 8 ^ (0 : ℤ) * gg 9 ^ (0 : ℤ) = 1 at h
  rw [g7, gg_rel (k := 0) (by omega)] at h
  simp only [zpow_zero, one_zpow, mul_one] at h
  exact_mod_cast h

theorem mk_two (i j : ℕ) : PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ hopfWs.map FreeGroup.mk}
    (FreeGroup.mk (rels.getD i [] ++ rels.getD j [])) = z i * z j := by
  rw [← FreeGroup.mul_mk, map_mul]
  rfl

theorem pow_two_rel {i j : ℕ} (hi : i < 7) (k : ℕ) : (z i * z j) ^ k = z i ^ k * z j ^ k := by
  have hc : Commute (z i) (z j) := (Subgroup.mem_center_iff.mp (z_central hi) (z j)).symm
  exact hc.mul_pow k

theorem relations : ∀ u ∈ extraWs,
    PresentedGroup.mk {r : FreeGroup (Fin 2) | r ∈ hopfWs.map FreeGroup.mk} (FreeGroup.mk u) = 1 := by
  have e1 : bFive = rels.getD 1 [] := by decide +kernel
  have e5 : zOne = rels.getD 0 [] ++ rels.getD 5 [] := by decide +kernel
  have e6 : zTwo = rels.getD 0 [] ++ rels.getD 6 [] := by decide +kernel
  have e0 : zThree = rels.getD 0 [] ++ rels.getD 0 [] := by decide +kernel
  intro u hu
  simp only [extraWs, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · rw [e1]
    exact z1_eq
  · rw [mk_wpow, map_pow, e5, mk_two, pow_two_rel (by omega)]
    exact z05
  · rw [mk_wpow, map_pow, e6, mk_two, pow_two_rel (by omega)]
    exact z06
  · rw [mk_wpow, map_pow, e0, mk_two, pow_two_rel (by omega), ← pow_add]
    exact z0_six

end CertificateChecks.KernelL34H

end
