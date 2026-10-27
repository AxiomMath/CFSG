module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4O8Defs
public import Certificates.Kernel.OmegaEight.Quat125MemberB
public import Certificates.Kernel.OmegaEight.Quat125KL
import CFSG.Certificates.Kernel.Spor.Co2ChainSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.Q125

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
open CertificateChecks.KernelO8 CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KC.PCent CFSG.KC.Misc.ArrEnum
open CertificateChecks.KernelO8.E4C

theorem q125c_K0 : E4O8.K0 = q125K0 := by
  rw [q125K0_eq]
  rfl


theorem q125c_ws {k : Nat} (hk : k < 6300) :
    E4O8.wsP.getD k 1 = permOfArr 360 ((E4O8.wsA ()).getD k (idA 360)) := by
  have hl : k < (E4O8.wsA ()).length := by rw [q125_wsA_WP.1]; exact hk
  unfold E4O8.wsP E4O8.perms
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hl), List.getElem_map,
    List.getD_eq_getElem _ _ hl]

theorem q125c_wsWP {k : Nat} (hk : k < 6300) : E4O8.wsP.getD k 1 = q125WP (rowW (RT k)) := by
  rw [q125c_ws hk, q125_wsA_WP.2 k hk]

theorem q125c_wsPk {k : Nat} (hk : k < 6300) : CFSG.KC.BfsPin.PP 360 9 (wO (e4WW k)) ∧
    E4O8.wsP.getD k 1 = toPerm 360 9 (wO (e4WW k)) := by
  have hp := (e4Pm_iff.1 (e4_row_facts (e4_row_at hk)).2.2.1).1
  refine ⟨e4c_pp hp, ?_⟩
  rw [q125c_ws hk, wsA_pk, e4_ws_getD hk, e4c_toPerm hp]

theorem q125c_word {w : List Int} (h : lettersK 17 w = true) :
    ∃ g ∈ omegaT, Rep 360 (omegaW w) g := by
  have hs := omegaW_spec (w := w) (by rw [← CFSG.KS.Co2SShape.lettersK_eq]; exact h)
  exact ⟨_, hs.2, hs.1⟩

theorem q125c_data : ∀ a ∈ [E4O8.u0A (), E4O8.v0A (), E4O8.threeA ()] ++ E4O8.wsA (),
    ∃ g ∈ omegaT, Rep 360 a g := by
  intro a ha
  rcases List.mem_append.1 ha with ha | ha
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact q125c_word e4_facts.1
    · exact q125c_word e4_facts.2.2.1
    · exact q125c_word kThreeW125
  · unfold E4O8.wsA at ha
    rw [wsW_eq, List.map_map] at ha
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 ha
    exact q125c_word (e4_row_facts (e4_rows r hr)).1

theorem q125c_L0 : E4O8.L0P = e4L.map (toPerm 360 9) := by
  obtain ⟨-, -, -, -, -, hpx, hpu, hpv⟩ := e4c_pm
  unfold E4O8.L0P CFSG.ClassicalInvolution.Q3.TL4.E4C.q8Elems e4L e4Q
  simp only [List.map_cons, List.map_nil]
  rw [e4c_pid, e4c_mul (p := pc e4U om0V) (hpu.mul hpv) hpx, e4c_mul hpu hpv, e4c_mul hpu hpx,
    e4c_mul hpv hpx, e4c_x0, e4c_u0, e4c_v0]
  rfl

theorem q125c_K0_iff (x : Equiv.Perm (Fin 360)) : x ∈ E4O8.K0 ↔ x ∈ E4O8.L0P := by
  rw [q125c_K0, q125c_L0]
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := q125_K0_sub hx
    exact List.mem_map_of_mem hy
  · intro hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    exact q125_mem_K0 (List.any_eq_true.2 ⟨y, hy, Nat.beq_refl y⟩)

theorem q125c_u0_sq : E4O8.u0 * E4O8.u0 = mainPerm 0 := by
  unfold E4O8.u0
  rw [← e4c_u0, e4c_u0_sq, e4c_x0]

theorem q125c_tw {k : Nat} (hk : k ∈ [1, 3, 4]) :
    E4O8.wsP.getD k 1 * mainPerm 0 = mainPerm 0 * E4O8.wsP.getD k 1 := by
  have hk' : k < 6300 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  obtain ⟨hp, he⟩ := q125c_wsPk hk'
  obtain ⟨-, -, -, -, -, hpx, -, -⟩ := e4c_pm
  have h := kTw125
  simp only [q125bAnd] at h
  have hc : twK k = true := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl
    exacts [h.1, h.2.1, h.2.2]
  unfold twK at hc
  rw [q125sB] at hc
  rw [he, ← e4c_x0, ← e4c_mul hp hpx, ← e4c_mul hpx hp, Nat.eq_of_beq_eq_true hc]

theorem q125c_three : E4O8.three ^ 3 = 1 ∧ conjSub E4O8.three E4O8.K0 = E4O8.K0 ∧
    E4O8.three * E4O8.u0 ≠ E4O8.u0 * E4O8.three := by
  obtain ⟨-, -, -, -, -, -, hpu, -⟩ := e4c_pm
  have h := kThree125
  unfold threeK at h
  simp only [q125bAnd] at h
  obtain ⟨hpm, h3, hn, hc⟩ := h
  have hpb : permB 360 9 (wO (E4O8.threeW ())) = true := hpm
  have hp := e4c_pp hpb
  have ht : E4O8.three = toPerm 360 9 (wO (E4O8.threeW ())) := by
    unfold E4O8.three E4O8.threeA
    rw [omegaW_eq kThreeW125, e4c_toPerm hpb]
  have hu : E4O8.u0 = toPerm 360 9 e4U := e4c_u0.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [ht, pow_succ, pow_two, mul_assoc, ← e4c_mul hp hp, ← e4c_mul (q := pc _ _) hp (hp.mul hp),
      Nat.eq_of_beq_eq_true h3, e4c_pid]
  · have hN := q125_norm hp hn
    rw [← ht, ← q125c_K0] at hN
    ext x
    rw [mem_conjSub_iff]
    have := (Subgroup.mem_normalizer_iff.1 hN) (E4O8.three⁻¹ * x * E4O8.three)
    rw [this]
    group
  · intro he
    rw [ht, hu, ← e4c_mul hp hpu, ← e4c_mul hpu hp] at he
    have e : pc (wO (E4O8.threeW ())) e4U = pc e4U (wO (E4O8.threeW ())) :=
      toPerm_injective (hp.mul hpu) (hpu.mul hp) he
    rw [e, Nat.beq_refl] at hc
    exact Bool.noConfusion hc

open Certificates in
open CFSG.EvenSmallLie.OmegaEight CFSG.Monster.B.Co2 CFSG.ClassicalInvolution.Q3.TL4.E4O8 in
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4 in
theorem q125_cert :
    (∀ a ∈ [u0A (), v0A (), threeA ()] ++ wsA (), ∃ g ∈ omegaT, Rep 360 a g) ∧
    (u0 * u0 = mainPerm 0 ∧ mainPerm 0 * mainPerm 0 = 1 ∧ mainPerm 0 ≠ 1 ∧
      ∀ x, x ∈ K0 ↔ x ∈ L0P) ∧
    (gen 8 * mainPerm 0 = mainPerm 0 * gen 8 ∧ gen 9 * mainPerm 0 = mainPerm 0 * gen 9 ∧
      (∀ k ∈ [1, 3, 4], wsP.getD k 1 * mainPerm 0 = mainPerm 0 * wsP.getD k 1) ∧
      three ^ 3 = 1 ∧ conjSub three K0 = K0 ∧ three * u0 ≠ u0 * three) ∧
    (∀ {K : Subgroup (Equiv.Perm (Fin 360))} {s : Equiv.Perm (Fin 360)},
      Vtx.AmbientQuatDatum omegaT K s → ∃ g ∈ omegaT, conjSub g K = K0) ∧
    (wsP.length = 6300 ∧ ∀ {g : Equiv.Perm (Fin 360)}, g ∈ omegaT →
      ∃ k < wsP.length, conjSub g K0 = conjSub (wsP.getD k 1) K0) ∧
    (∀ {g : Equiv.Perm (Fin 360)}, g ∈ omegaT →
      Relation.ReflTransGen (Vtx.StarRel omegaT K0) K0 (conjSub g K0)) ∧
    (∀ {g : Equiv.Perm (Fin 360)}, g ∈ omegaT → conjSub g K0 ≠ K0 →
      conjSub g K0 ≤ Subgroup.normalizer (K0 : Set (Equiv.Perm (Fin 360))) →
      ∃ k ∈ [1, 3, 4], conjSub g K0 = conjSub (wsP.getD k 1) K0) ∧
    (conjSub (wsP.getD 1 1) K0 ≠ K0 ∧
      conjSub (wsP.getD 1 1) K0 ≤ Subgroup.normalizer (K0 : Set (Equiv.Perm (Fin 360)))) := by
  obtain ⟨-, hx2, hx1⟩ := e4c_x0_facts
  rw [e4c_x0] at hx2 hx1
  refine ⟨q125c_data, ⟨q125c_u0_sq, hx2, hx1, q125c_K0_iff⟩,
    ⟨q125_gen_comm (Or.inl rfl), q125_gen_comm (Or.inr rfl), fun k hk => q125c_tw hk,
      q125c_three⟩, fun hd => ?_, ⟨?_, fun hg => ?_⟩, fun hg => ?_, fun hg hne hle => ?_, ?_⟩
  · rw [q125c_K0]
    exact q125_ident hd
  · unfold E4O8.wsP E4O8.perms
    rw [List.length_map, q125_wsA_WP.1]
  · obtain ⟨k, hk, he⟩ := q125_member_WP hg
    refine ⟨k, ?_, ?_⟩
    · unfold E4O8.wsP E4O8.perms
      rw [List.length_map, q125_wsA_WP.1]
      exact hk
    · rw [q125c_wsWP hk, q125c_K0]
      exact he
  · rw [q125c_K0]
    exact q125_connected hg
  · rw [q125c_K0] at hne hle ⊢
    obtain ⟨k, hk, he⟩ := q125_twins_WP hg hne hle
    have hk' : k < 6300 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      omega
    exact ⟨k, hk, by rw [q125c_wsWP hk', he]⟩
  · rw [q125c_wsWP (by norm_num), q125c_K0]
    exact q125_edge

end CertificateChecks.KernelO8.Q125

end
