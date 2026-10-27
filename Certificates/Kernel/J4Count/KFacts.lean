
module


public import Certificates.Kernel.J4Count.HOrder
public import CFSG.Sporadic.Schreier.J4SOdd276Base1

public section

namespace CertificateChecks.KernelJ4Count

open CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier CFSG.Sporadic.SmallF2.Native

theorem ρK_injective' : Function.Injective ρK := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro k hk
  rw [MonoidHom.mem_ker, ρK_eq] at hk
  have h1 : Subgroup.inclusion K_le_H k ∈ N.subgroupOf H := by rw [← ker_ρH']; exact hk
  rw [Subgroup.mem_subgroupOf] at h1
  have h2 : (k : J) ∈ K ⊓ N := ⟨k.2, h1⟩
  rw [K_inf_N, Subgroup.mem_bot] at h2
  exact (Subgroup.mem_bot).2 (Subtype.ext h2)

theorem card_K' : Nat.card K = 244823040 := by
  rw [← counting'.2.2, ← Nat.card_congr (MonoidHom.ofInjective ρK_injective').toEquiv]

theorem card_K_eq' : Nat.card K = 2 ^ 10 * 3 ^ 3 * 5 * 7 * 11 * 23 := by
  rw [card_K']
  norm_num

theorem card_H_eq' : Nat.card H = 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 * 23 := by
  rw [card_H']
  norm_num

theorem eq_of_actsBy' {g h : J} (hg : g ∈ K) (hh : h ∈ K) {C : Array ℕ} (h1 : ActsBy g C)
    (h2 : ActsBy h C) : g = h := by
  have e : ρK ⟨g, hg⟩ = ρK ⟨h, hh⟩ := by
    refine MulEquiv.ext fun n => Subtype.ext ?_
    obtain ⟨a, -, ha⟩ := exists_η_eq n.2
    rw [ρK_apply, ρK_apply, ← ha]
    exact (h1 a).trans (h2 a).symm
  exact congrArg Subtype.val (ρK_injective' e)

theorem eq_one_of_actsBy_id' {g : J} (hg : g ∈ K) (h : ActsBy g (idRows 11)) : g = 1 :=
  eq_of_actsBy' hg K.one_mem h actsBy_one

theorem a276_pow' : a276 ^ 11 = 1 := by
  have h := actsBy_pow 11 a276_acts
  rw [a276_check.2.1] at h
  exact eq_one_of_actsBy_id' (K.pow_mem a276_mem_K 11) h

section Q3

theorem q3Elt_zero' : q3Elt 0 = 1 :=
  eq_of_actsBy' (Q3_le_K (q3Elt_spec (by norm_num)).1) K.one_mem (q3Elt_spec (by norm_num)).2
    (q3_zero ▸ actsBy_one)

theorem q3Elt_mul' {k g : ℕ} (hk : k < 27) (hg : g < 2) :
    q3Elt k * q3gen g = q3Elt (q3Edges[k]!)[g]! := by
  obtain ⟨he, hcols⟩ := (q3_all k hk).2.2.2 g hg
  have h1 := actsBy_mul (q3Elt_spec hk).2 (q3gen_acts hg)
  rw [← hcols] at h1
  exact eq_of_actsBy' (K.mul_mem (Q3_le_K (q3Elt_spec hk).1) (q3gen_mem_K g))
    (Q3_le_K (q3Elt_spec he).1) h1 (q3Elt_spec he).2

theorem mem_Q3_iff' {g : J} : g ∈ Q3 ↔ ∃ k < 27, q3Elt k = g := by
  constructor
  · intro hg
    have hg' : g ∈ Submonoid.closure (Set.range fun i : Fin 2 => q3gen i) := by
      rw [← Subgroup.closure_toSubmonoid_of_finite]
      exact hg
    clear hg
    induction hg' using Submonoid.closure_induction_right with
    | one => exact ⟨0, by norm_num, q3Elt_zero'⟩
    | mul_right g _ s hs ih =>
      obtain ⟨i, rfl⟩ := hs
      obtain ⟨k, hk, rfl⟩ := ih
      beta_reduce
      exact ⟨_, ((q3_all k hk).2.2.2 i i.isLt).1, (q3Elt_mul' hk i.isLt).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact (q3Elt_spec hk).1

theorem card_Q3' : Nat.card Q3 = 27 := by
  have hf : Function.Injective fun k : Fin 27 => (⟨q3Elt k, (q3Elt_spec k.isLt).1⟩ : Q3) := by
    intro k k' h
    have h' := Subtype.ext_iff.1 h
    dsimp only at h'
    exact Fin.ext (q3Elt_injOn k.isLt k'.isLt h')
  have hs : Function.Surjective fun k : Fin 27 => (⟨q3Elt k, (q3Elt_spec k.isLt).1⟩ : Q3) := by
    rintro ⟨g, hg⟩
    obtain ⟨k, hk, rfl⟩ := mem_Q3_iff'.1 hg
    exact ⟨⟨k, hk⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hf, hs⟩), Nat.card_fin]

theorem card_Q3_sylow' : Nat.card Q3 = 3 ^ (Nat.card H).factorization 3 := by
  rw [card_Q3', card_H_eq']
  have h2 : Nat.Prime 2 := Nat.prime_two
  have h3 : Nat.Prime 3 := Nat.prime_three
  have h5 : Nat.Prime 5 := by norm_num
  have h7 : Nat.Prime 7 := by norm_num
  have h11 : Nat.Prime 11 := by norm_num
  have h23 : Nat.Prime 23 := by norm_num
  repeat rw [Nat.factorization_mul (by positivity) (by positivity)]
  simp only [Finsupp.add_apply, Nat.Prime.factorization_pow h2, Nat.Prime.factorization_pow h3,
    Nat.Prime.factorization h5, Nat.Prime.factorization h7, Nat.Prime.factorization h11,
    Nat.Prime.factorization h23, Finsupp.single_apply]
  norm_num

end Q3

end CertificateChecks.KernelJ4Count

end
