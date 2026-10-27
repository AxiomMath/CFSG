module

public import CFSG.Sporadic.SmallOddCore.GroupFacts
public import Certificates.Kernel.SporSch.PairJ3.CntGroup
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CertificateChecks.KernelSporSch.PJ3C81

open Subgroup CFSG.Sporadic.SmallOddCore

variable {M : Type*} [Group M]

theorem pow_of_orderOf_eq_prime {z : M} {q v m : ℕ} (hq : q.Prime) (hv : 0 < v)
    (hz : orderOf z = q ^ v) (hm : orderOf (z ^ m) = q) :
    ∃ j, 0 < j ∧ j < q ∧ z ^ m = (z ^ (q ^ (v - 1))) ^ j := by
  have hq1 : (z ^ m) ^ q = 1 := by rw [← hm]; exact pow_orderOf_eq_one _
  rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hz] at hq1
  have e : q ^ v = q ^ (v - 1) * q := by rw [← pow_succ, Nat.sub_add_cancel hv]
  rw [e] at hq1
  obtain ⟨j, hj⟩ := Nat.dvd_of_mul_dvd_mul_right hq.pos hq1
  have hw : (z ^ (q ^ (v - 1))) ^ q = 1 := by
    rw [← pow_mul, ← e, ← hz, pow_orderOf_eq_one]
  have hzj : z ^ m = (z ^ (q ^ (v - 1))) ^ (j % q) := by
    rw [hj, pow_mul]
    conv_lhs => rw [← Nat.div_add_mod j q, pow_add, pow_mul, hw, one_pow, one_mul]
  refine ⟨j % q, Nat.pos_of_ne_zero fun h0 => ?_, Nat.mod_lt _ hq.pos, hzj⟩
  rw [h0, pow_zero] at hzj
  rw [hzj, orderOf_one] at hm
  exact hq.one_lt.ne hm

theorem orderOf_w {z : M} {q v : ℕ} (hq : q.Prime) (hv : 0 < v) (hz : orderOf z = q ^ v) :
    orderOf (z ^ (q ^ (v - 1))) = q := by
  have hd : q ^ (v - 1) ∣ orderOf z := by rw [hz]; exact pow_dvd_pow q (Nat.sub_le v 1)
  rw [orderOf_pow_of_dvd (pow_ne_zero _ hq.ne_zero) hd, hz]
  rw [show q ^ v = q ^ (v - 1) * q by rw [← pow_succ, Nat.sub_add_cancel hv]]
  exact Nat.mul_div_cancel_left q (pow_pos hq.pos _)

theorem oddCore_eq_bot_of_cyclic [Finite M] (K : Subgroup M) (W : List (M × M × ℕ × ℕ))
    (hq : ∀ q : ℕ, q.Prime → q ∣ Nat.card K → q ≠ 2 → ∃ e ∈ W, e.2.2.1 = q)
    (hW : ∀ e ∈ W, e.1 ∈ K ∧ e.2.1 ∈ K ∧ e.2.2.1.Prime ∧ 0 < e.2.2.2 ∧
      orderOf e.1 = e.2.2.1 ^ e.2.2.2 ∧ (Nat.card K).factorization e.2.2.1 = e.2.2.2 ∧
      2 ∣ orderOf (e.1 ^ (e.2.2.1 ^ (e.2.2.2 - 1)) *
        (e.2.1 * e.1 ^ (e.2.2.1 ^ (e.2.2.2 - 1)) * e.2.1⁻¹))) :
    CFSG.oddCore ↥K = ⊥ := by
  classical
  apply oddCore_eq_bot_of_witnesses K (W.flatMap fun e =>
    (List.range (e.2.2.1 - 1)).map fun j => (e.1 ^ (e.2.2.1 ^ (e.2.2.2 - 1))) ^ (j + 1))
  · intro y hy hyp hy2
    have hdvd : orderOf y ∣ Nat.card K := by
      rw [← Subgroup.orderOf_mk y hy]
      exact orderOf_dvd_natCard _
    obtain ⟨⟨z, h, q, v⟩, he, hqy⟩ := hq _ hyp hdvd hy2
    obtain ⟨hzK, -, hqp, hv, hz, hfac, -⟩ := hW _ he
    dsimp only at hqy hzK hqp hv hz hfac
    have : Fact q.Prime := ⟨hqp⟩
    set Z : Subgroup K := zpowers ⟨z, hzK⟩
    have hZ : Nat.card Z = q ^ (Nat.card K).factorization q := by
      rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz, hfac]
    obtain ⟨g, hg⟩ := PJ3Group.exists_conj_mem Z hZ (x := ⟨y, hy⟩) (k := 1)
      (by rw [Subgroup.orderOf_mk, pow_one, hqy])
    rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hg
    obtain ⟨m, hm⟩ := hg
    have hm' : z ^ m = (g : M) * y * (g : M)⁻¹ := by
      have := congrArg Subtype.val hm
      simpa using this
    have hord : orderOf (z ^ m) = q := by
      rw [hm', ← MulAut.conj_apply, MulEquiv.orderOf_eq, hqy]
    obtain ⟨j, hj0, hjq, hj⟩ := pow_of_orderOf_eq_prime hqp hv hz hord
    refine ⟨(z ^ (q ^ (v - 1))) ^ j, ?_, (g : M)⁻¹, K.inv_mem g.2, ?_⟩
    · refine List.mem_flatMap.2 ⟨(z, h, q, v), he, List.mem_map.2 ⟨j - 1, ?_, ?_⟩⟩
      · exact List.mem_range.2 (by dsimp only; omega)
      · dsimp only
        rw [Nat.sub_add_cancel hj0]
    · rw [← hj, hm']
      group
  · intro x hx N hNK hNn hxN
    obtain ⟨⟨z, h, q, v⟩, he, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hzK, hhK, hqp, hv, hz, -, hev⟩ := hW _ he
    rw [List.mem_range] at hj
    dsimp only at hzK hhK hqp hv hz hev hj ⊢
    set w := z ^ (q ^ (v - 1))
    have hw := orderOf_w hqp hv hz
    have hcop : (orderOf w).Coprime (j + 1) := by
      rw [hw]
      exact (Nat.Prime.coprime_iff_not_dvd hqp).2 (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
    have hle : zpowers (w ^ (j + 1)) ≤ zpowers w :=
      (zpowers_le).2 (Subgroup.pow_mem _ (mem_zpowers w) _)
    have heq : zpowers (w ^ (j + 1)) = zpowers w := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [Nat.card_zpowers, Nat.card_zpowers, Nat.Coprime.orderOf_pow hcop]
    have hwN : w ∈ N := by
      have : w ∈ zpowers (w ^ (j + 1)) := by rw [heq]; exact mem_zpowers w
      exact (zpowers_le.2 hxN) this
    exact ⟨w * (h * w * h⁻¹), N.mul_mem hwN (hNn h hhK w hwN), hev⟩

theorem mul_le_card_of_orbit {n m : ℕ} (K : Subgroup (Equiv.Perm (Fin n))) (x : Fin n)
    (f : Fin m → Fin n) (hf : Function.Injective f) (hfK : ∀ k, ∃ g ∈ K, g x = f k)
    {w : Equiv.Perm (Fin n)} (hw : w ∈ K) (hwx : w x = x) (hw1 : w ≠ 1) :
    m * 2 ≤ Nat.card K := by
  classical
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer K x)
  rw [MulAction.index_stabilizer] at h1
  have ho : m ≤ (MulAction.orbit K x).ncard := by
    have hsub : Set.range f ⊆ MulAction.orbit K x := by
      rintro _ ⟨k, rfl⟩
      obtain ⟨g, hg, hgx⟩ := hfK k
      exact ⟨⟨g, hg⟩, hgx⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rwa [Set.ncard_range_of_injective hf, Nat.card_eq_fintype_card, Fintype.card_fin] at this
  have hs : 2 ≤ Nat.card (MulAction.stabilizer K x) := by
    have hw' : (⟨w, hw⟩ : K) ∈ MulAction.stabilizer K x := by
      rw [MulAction.mem_stabilizer_iff]
      exact hwx
    have h1 : 1 < Nat.card (MulAction.stabilizer K x) := by
      rw [Subgroup.one_lt_card_iff_ne_bot]
      intro hbot
      have h2 : (⟨w, hw⟩ : K) ∈ (⊥ : Subgroup K) := hbot ▸ hw'
      rw [Subgroup.mem_bot] at h2
      exact hw1 (congrArg Subtype.val h2)
    omega
  rw [← h1, mul_comm m]
  exact Nat.mul_le_mul hs ho

theorem closure_subset_of_mul_left [Finite M] {s : Set M} {T : Set M} (h1 : (1 : M) ∈ T)
    (hmul : ∀ g ∈ s, ∀ y ∈ T, g * y ∈ T) : ∀ x ∈ closure s, x ∈ T := by
  have hpow : ∀ g ∈ s, ∀ k : ℕ, ∀ y ∈ T, g ^ k * y ∈ T := by
    intro g hg k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      rw [pow_succ', mul_assoc]
      exact hmul g hg _ (ih y hy)
  intro x hx
  induction hx using Subgroup.closure_induction_left with
  | one => exact h1
  | mul_left g hg y _ ih => exact hmul g hg y ih
  | inv_mul_cancel g hg y _ ih =>
    have e : g⁻¹ = g ^ (orderOf g - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos g),
        pow_orderOf_eq_one]
    rw [e]
    exact hpow g hg _ y ih

end CertificateChecks.KernelSporSch.PJ3C81

end
