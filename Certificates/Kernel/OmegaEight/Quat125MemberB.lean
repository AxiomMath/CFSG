module

public import Certificates.Kernel.OmegaEight.Quat125Member
public import Certificates.Kernel.OmegaEight.Quat125Nbr

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.Q125

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
open CertificateChecks.KernelO8 CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KC.PCent CFSG.KC.Misc.ArrEnum

theorem q125m_Lt_eq (W i : Nat) : q125Lt W i = W / 16 ^ i % 16 := by
  unfold q125Lt
  change (W >>> (4 * i)) &&& (2 ^ 4 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem q125WP_zero : q125WP 0 = 1 := by
  unfold q125WP
  have h : ∀ i, q125LP (q125Lt 0 i) = 1 := fun i => by
    rw [q125m_Lt_eq, Nat.zero_div, Nat.zero_mod]
    rfl
  simp only [h, List.map_const', List.length_range, List.prod_replicate, one_pow]

theorem q125WP_step (l W : Nat) (hl0 : 0 < l) (hl9 : l < 9) (hW : W < 2 ^ 76) :
    q125WP (l + 16 * W) = toPerm 360 9 (AP.S (l - 1)) * q125WP W := by
  unfold q125WP
  have h0 : q125Lt (l + 16 * W) 0 = l := by
    rw [q125m_Lt_eq]
    omega
  have hs : ∀ i, q125Lt (l + 16 * W) (i + 1) = q125Lt W i := fun i => by
    rw [q125m_Lt_eq, q125m_Lt_eq, pow_succ, mul_comm (16 ^ i) 16, ← Nat.div_div_eq_div_mul]
    congr 2
    omega
  have h19 : q125Lt W 19 = 0 := by
    rw [q125m_Lt_eq, Nat.div_eq_of_lt (by norm_num at hW ⊢; omega)]
  have hl : q125LP l = toPerm 360 9 (AP.S (l - 1)) := by
    unfold q125LP
    rw [if_neg (by omega)]
  have A : ∀ f : Nat → Equiv.Perm (Fin 360), ((List.range 20).map f).prod =
      f 0 * ((List.range 19).map fun i => f (i + 1)).prod := fun f => by
    rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
    rfl
  have B : ∀ g : Nat → Equiv.Perm (Fin 360), ((List.range 20).map g).prod =
      ((List.range 19).map g).prod * g 19 := fun g => by
    rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton]
  have e : q125LP 0 = 1 := rfl
  rw [A, B (fun i => q125LP (q125Lt W i))]
  simp only [h0, hl, hs, h19, e, mul_one]

theorem q125_hM {k : Nat} (hk : k < 6300) :
    ∀ p : Fin 360, p.val < 240 →
      (bitK (MT k) p.val = true ↔ q125Fix ((q125WP (rowW (RT k)))⁻¹ p)) := by
  intro p hp
  rw [q125m_bitK, ((q125_mask q125WP q125WP_zero q125WP_step) _ k hk rfl).2 p]
  unfold q125Fix
  exact ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩

theorem q125_member_WP {g : Equiv.Perm (Fin 360)}
    (hg : g ∈ omegaT) : ∃ k < 6300, conjSub g q125K0 = conjSub (q125WP (rowW (RT k))) q125K0 :=
  q125_member q125WP q125WP_zero q125WP_step hg

theorem q125_wsA_WP : (E4O8.wsA ()).length = 6300 ∧ ∀ k < 6300,
    permOfArr 360 ((E4O8.wsA ()).getD k (idA 360)) = q125WP (rowW (RT k)) :=
  q125_wsA q125WP q125WP_zero q125WP_step

theorem q125_twins_WP {g : Equiv.Perm (Fin 360)} (hg : g ∈ omegaT)
    (hne : conjSub g q125K0 ≠ q125K0)
    (hle : conjSub g q125K0 ≤ Subgroup.normalizer (q125K0 : Set (Equiv.Perm (Fin 360)))) :
    ∃ k ∈ [1, 3, 4], conjSub g q125K0 = conjSub (q125WP (rowW (RT k))) q125K0 := by
  obtain ⟨k, hk, he⟩ := q125_member_WP hg
  rw [he] at hne hle
  by_cases hk0 : k = 0
  · subst hk0
    rw [((q125m_tree (k := 0) (by norm_num)).1 rfl).1, q125WP_zero, conjSub_one] at hne
    exact absurd rfl hne
  by_cases hka : k = 1 ∨ k = 3 ∨ k = 4
  · refine ⟨k, ?_, he⟩
    rcases hka with rfl | rfl | rfl <;> simp
  · push Not at hka
    exact absurd hle (q125_nbr hk hk0 hka.1 hka.2.1 hka.2.2 (q125_hM hk))

end CertificateChecks.KernelO8.Q125

end
