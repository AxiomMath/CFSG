module

public import Certificates.Kernel.StdOdd.Comm7B.Checks
public import Certificates.Kernel.StdOdd.Comm7B.Sound
public import CFSG.Monster.Existence.StdOdd.Cert.Cent7B

public section

namespace CFSG.KD.StdOdd.Comm7B

open CFSG.KC.Misc CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.E6Std CFSG.KD.Misc.E6Std CFSG.KD.StdOdd.Reps
  CFSG.KD.StdOdd.Sylow57 CFSG.Monster.Existence.StdOdd CFSG.Monster.Existence.StdOdd.Cert
  CFSG.LieType.Chevalley.C2E6Std.MatrixModel

theorem card_inf_centralizer_of_conj {G : Type*} [Group G] [Finite G] {p k : ℕ}
    [hp : Fact p.Prime] {x z : G} (hx : orderOf x = p) (hz : orderOf z = p) (hxz : Commute x z)
    (hzx : z ∉ Subgroup.zpowers x)
    (hC : Nat.card (Subgroup.centralizer ({x} : Set G)) = k * (p * p))
    (g : Fin k → G) (hg : ∀ i, g i ∈ Subgroup.centralizer ({x} : Set G))
    (hinj : ∀ i j, g i * z * (g i)⁻¹ = g j * z * (g j)⁻¹ → i = j) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G)) =
      p * p := by
  set C := Subgroup.centralizer ({x} : Set G) with hCdef
  set H := C ⊓ Subgroup.centralizer ({z} : Set G) with hHdef
  have hxH : Subgroup.zpowers x ≤ H := by
    rw [Subgroup.zpowers_le]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl,
      Subgroup.mem_centralizer_singleton_iff.2 hxz.eq⟩
  have hzH : Subgroup.zpowers z ≤ H := by
    rw [Subgroup.zpowers_le]
    exact ⟨Subgroup.mem_centralizer_singleton_iff.2 hxz.eq.symm,
      Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers z = ⊥ := by
    have hd : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers z) ∣ p := by
      rw [← hz, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp.out).1 hd with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have e : Subgroup.zpowers x ⊓ Subgroup.zpowers z = Subgroup.zpowers z :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, Nat.card_zpowers, hz])
      have hm : z ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers z := by
        rw [e]
        exact Subgroup.mem_zpowers z
      exact hzx (Subgroup.mem_inf.1 hm).1
  let f : ↥(Subgroup.zpowers x) × ↥(Subgroup.zpowers z) → ↥H := fun ab =>
    ⟨ab.1 * ab.2, H.mul_mem (hxH ab.1.2) (hzH ab.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have e : (a : G) * b = a' * b' := congrArg Subtype.val hab
    have h1 : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
      calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
        _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [e]
        _ = b' * (b : G)⁻¹ := by group
    have hm : (a' : G)⁻¹ * a ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers z := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ a'.2) a.2, ?_⟩
      rw [h1]
      exact Subgroup.mul_mem _ b'.2 (Subgroup.inv_mem _ b.2)
    rw [hdisj, Subgroup.mem_bot, inv_mul_eq_one] at hm
    have hb : (b : G) = b' := by
      rw [← hm] at e
      exact mul_left_cancel e
    exact Prod.ext (Subtype.ext hm.symm) (Subtype.ext hb)
  have hlow : p * p ≤ Nat.card H := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, hx, hz] at this
  set S := (Subgroup.centralizer ({z} : Set G)).subgroupOf C with hSdef
  have hS : Nat.card S = Nat.card H := by
    rw [← Subgroup.card_map_of_injective C.subtype_injective, Subgroup.subgroupOf_map_subtype,
      hHdef, inf_comm]
  have hq : k ≤ Nat.card (↥C ⧸ S) := by
    let q : Fin k → ↥C ⧸ S := fun i => ((⟨g i, hg i⟩ : ↥C) : ↥C ⧸ S)
    have hqinj : Function.Injective q := by
      intro i j hij
      have hij' := QuotientGroup.eq.1 hij
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hij'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hij'
      apply hinj
      calc g i * z * (g i)⁻¹ = g i * (z * ((g i)⁻¹ * g j)) * (g j)⁻¹ := by group
        _ = g i * ((g i)⁻¹ * g j * z) * (g j)⁻¹ := by rw [hij']
        _ = g j * z * (g j)⁻¹ := by group
    have := Nat.card_le_card_of_injective q hqinj
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup S
  rw [hC, hS] at hcard
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · exfalso
      have hpos : 0 < Nat.card ↥C := Nat.card_pos
      rw [hC, h0, zero_mul] at hpos
      exact lt_irrefl 0 hpos
    · exact h0
  have hle : k * Nat.card H ≤ k * (p * p) := by
    rw [hcard]
    exact Nat.mul_le_mul_right _ hq
  exact le_antisymm (Nat.le_of_mul_le_mul_left hle hk) hlow

theorem exists_card_inf_centralizer_rep7B_K :
    ∃ z ∈ Subgroup.centralizer ({rep7B} : Set Rgrp),
      Nat.card ↥(Subgroup.centralizer ({rep7B} : Set Rgrp) ⊓
        Subgroup.centralizer ({z} : Set Rgrp)) = 49 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Finite Rgrp := rgrp_finite
  set C := Subgroup.centralizer ({rep7B} : Set Rgrp) with hCdef
  have hx : rgrpMat rep7B = toMat (Native.wordMat nativeAB.1 nativeAB.2 repWord7B) :=
    rgrpMat_repOf repWord7B
  have hzM := rgrpMat_rgrpSlp sylow7Prog sylow7Z
  set z := (rgrpSlp sylow7Prog).getD sylow7Z 1 with hzdef
  obtain ⟨hzo, hxz, hzx, -⟩ := sylowFusionCheck_sound (p := 7) (x := rep7B) (y := z) hx hzM
    orderOf_rep7B sylow7
  have hhM : rgrpMat (repOf b7B) = toMat (Native.wordMat nativeAB.1 nativeAB.2 b7B) :=
    rgrpMat_repOf b7B
  have hx4 : rep7B = repOf b7B ^ 4 := by
    apply rgrpMat_injective
    rw [hx, map_pow, hhM, repWord7B, e7B, toMat_wordPow]
  have htC : repOf b7B ^ 7 ∈ C := by
    rw [hCdef, Subgroup.mem_centralizer_singleton_iff, hx4]
    exact (Commute.pow_pow_self (repOf b7B) 7 4).eq
  have hzC : z ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hxz.eq.symm
  have hRh : Rep hB (rgrpMat (repOf b7B)) := by
    rw [hhM]
    exact rep_wordB rep_A rep_B b7B
  have hRt : Rep tB (rgrpMat (repOf b7B ^ 7)) := by
    rw [map_pow]
    exact rep_powB hRh 7
  have ht4 : (repOf b7B ^ 7) ^ 4 = 1 := by
    apply rgrpMat_injective
    rw [map_pow, map_one]
    exact (beq_iff_of_rep (rep_powB hRt 4) rep_oneB).1 ch17105t
  have hRti : Rep (powB tB 3) (rgrpMat (repOf b7B ^ 7)⁻¹) := by
    have e : (repOf b7B ^ 7)⁻¹ = (repOf b7B ^ 7) ^ 3 := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', ht4]
    rw [e, map_pow]
    exact rep_powB hRt 3
  have hRz : Rep z7 (rgrpMat z) := by
    rw [hzM]
    exact rep_vals S7.v0 S7.v1 S7.lines S7.len S7.zLt
  have hRzi : Rep (powB z7 6) (rgrpMat z⁻¹) := by
    have e : z⁻¹ = z ^ 6 := by
      refine inv_eq_of_mul_eq_one_right ?_
      have h7 : z ^ 7 = 1 := by
        rw [← hzo]
        exact pow_orderOf_eq_one z
      rw [← pow_succ']
      exact h7
    rw [e, map_pow]
    exact rep_powB hRz 6
  let P : ℕ → Prop := fun N => ∃ g ∈ C, Rep N (rgrpMat (g * z * g⁻¹))
  have hPz : P z7 := ⟨1, C.one_mem, by rw [one_mul, inv_one, mul_one]; exact hRz⟩
  have hconj : ∀ {a ai : ℕ} {u : Rgrp}, u ∈ C → Rep a (rgrpMat u) → Rep ai (rgrpMat u⁻¹) →
      ∀ N, P N → P (mulB (mulB a N) ai) := by
    rintro a ai u hu ha hai N ⟨g, hg, hN⟩
    refine ⟨u * g, C.mul_mem hu hg, ?_⟩
    have e : u * g * z * (u * g)⁻¹ = u * (g * z * g⁻¹) * u⁻¹ := by group
    rw [e, map_mul, map_mul]
    exact rep_mulB (rep_mulB ha hN) hai
  obtain ⟨L, hLnd, hLlen, hLP⟩ := conjOrbK_sound P hPz (hconj htC hRt hRti)
    (hconj hzC hRz hRzi) ch17105orb
  have hlen : L.length = 24 := by
    rw [hLlen]
    rfl
  have hch : ∀ i : Fin 24, P (L.get (Fin.cast hlen.symm i)) := fun i => hLP _ (List.get_mem _ _)
  choose g hg hgR using hch
  refine ⟨z, hzC, card_inf_centralizer_of_conj (k := 24) orderOf_rep7B hzo hxz hzx ?_ g hg ?_⟩
  · rw [card_centralizer_rep7B]
  · intro i j hij
    have e := (eq_iff_of_rep (hgR i) (hgR j)).2 (by rw [hij])
    have e' := (hLnd.get_inj_iff).1 e
    exact Fin.ext (by simpa using congrArg Fin.val e')

end CFSG.KD.StdOdd.Comm7B

end
