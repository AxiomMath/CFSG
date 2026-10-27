module

public import Certificates.Kernel.Fi22Twist.SrchCent

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.Monster.B.Fischer


theorem card_quot {j : ℕ} (hj : j < 5) :
    Nat.card (cSub j ⧸ (uSub j).subgroupOf (cSub j)) = [2, 4, 2, 2, 2][j]! := by
  have h1 := Subgroup.card_mul_index ((uSub j).subgroupOf (cSub j))
  have h2 : Nat.card ((uSub j).subgroupOf (cSub j)) = Nat.card (uSub j) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (uSub_le_cSub hj)).toEquiv
  rw [h2, card_cSub_mul hj, Nat.mul_comm] at h1
  have hpos : 0 < Nat.card (uSub j) := by
    rw [card_uSub hj]
    exact Nat.pow_pos (by norm_num)
  rw [← Subgroup.index]
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem mem_uSub_of_pow {j : ℕ} (hj : j < 5) {a : Equiv.Perm (Fin 3510)} (ha : a ∈ cSub j)
    {m : ℕ} (hm : a ^ 3 ^ m = 1) : a ∈ uSub j := by
  have hN := uSub_normal hj
  let x : cSub j := ⟨a, ha⟩
  have hx : x ^ 3 ^ m = 1 := Subtype.ext (by simp [x, hm])
  have hq : (x : cSub j ⧸ (uSub j).subgroupOf (cSub j)) ^ 3 ^ m = 1 := by
    rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
  have d1 := orderOf_dvd_of_pow_eq_one hq
  have d2 := orderOf_dvd_natCard (x : cSub j ⧸ (uSub j).subgroupOf (cSub j))
  rw [card_quot hj] at d2
  have hc : Nat.Coprime (3 ^ m) [2, 4, 2, 2, 2][j]! := by
    refine Nat.Coprime.pow_left m ?_
    interval_cases j <;> decide
  have h1 := (Nat.Coprime.coprime_dvd_left d1 hc).eq_one_of_dvd d2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_subgroupOf.1 h1

theorem cent_closed {j : ℕ} (hj : j < 5) :
    ∀ a ∈ fi22P ⊓ Subgroup.centralizer (dSub j : Set (Equiv.Perm (Fin 3510))),
    ∀ b ∈ fi22P ⊓ Subgroup.centralizer (dSub j : Set (Equiv.Perm (Fin 3510))),
      (∃ m, a ^ 3 ^ m = 1) → (∃ m, b ^ 3 ^ m = 1) → ∃ m, (a * b) ^ 3 ^ m = 1 := by
  rw [cent_eq_cSub hj]
  rintro a ha b hb ⟨m, hm⟩ ⟨m', hm'⟩
  have hab : a * b ∈ uSub j := mul_mem (mem_uSub_of_pow hj ha hm) (mem_uSub_of_pow hj hb hm')
  refine ⟨[4, 5, 5, 6, 5][j]!, ?_⟩
  have h := pow_card_eq_one' (G := uSub j) (x := ⟨a * b, hab⟩)
  rw [card_uSub hj] at h
  exact congrArg Subtype.val h

end CertificateChecks.KernelFi22Twist

end
