module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.KD.StdOdd.Cent7

theorem inv_of_conj {G : Type*} [Group G] {N : Subgroup G} [hN : N.Normal] {t u : G}
    (ht : ∀ x ∈ N, t * x * t⁻¹ = x⁻¹) (hu : IsConj t u) : ∀ x ∈ N, u * x * u⁻¹ = x⁻¹ := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hu
  intro x hx
  have hy : c⁻¹ * x * c⁻¹⁻¹ ∈ N := hN.conj_mem x hx c⁻¹
  have e := ht _ hy
  calc c * t * c⁻¹ * x * (c * t * c⁻¹)⁻¹ = c * (t * (c⁻¹ * x * c⁻¹⁻¹) * t⁻¹) * c⁻¹ := by group
    _ = c * (c⁻¹ * x * c⁻¹⁻¹)⁻¹ * c⁻¹ := by rw [e]
    _ = x⁻¹ := by group

theorem inv_of_fixedPointFree {G : Type*} [Group G] {N : Subgroup G} [hN : N.Normal] [Finite N]
    {t : G} (ht2 : t ^ 2 = 1) (hfree : ∀ x ∈ N, t * x = x * t → x = 1) :
    ∀ x ∈ N, t * x * t⁻¹ = x⁻¹ := by
  have htt : t * t = 1 := by rw [← pow_two, ht2]
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  let f : N → N := fun n => ⟨(n : G)⁻¹ * (t * n * t⁻¹),
    N.mul_mem (N.inv_mem n.2) (hN.conj_mem _ n.2 t)⟩
  have hf : Function.Injective f := by
    rintro ⟨n, hnN⟩ ⟨m, hmN⟩ e
    have e' : n⁻¹ * (t * n * t⁻¹) = m⁻¹ * (t * m * t⁻¹) := congrArg Subtype.val e
    have hc : t * (m * n⁻¹) = m * n⁻¹ * t := by
      calc t * (m * n⁻¹) = m * (m⁻¹ * (t * m * t⁻¹)) * t * n⁻¹ := by group
        _ = m * (n⁻¹ * (t * n * t⁻¹)) * t * n⁻¹ := by rw [e']
        _ = m * n⁻¹ * t := by group
    have h1 := hfree _ (N.mul_mem hmN (N.inv_mem hnN)) hc
    exact Subtype.ext (mul_inv_eq_one.1 h1).symm
  intro x hx
  obtain ⟨⟨n, hnN⟩, hn⟩ := (Finite.injective_iff_surjective.1 hf) ⟨x, hx⟩
  have ex : x = n⁻¹ * (t * n * t⁻¹) := (congrArg Subtype.val hn).symm
  rw [ex, htinv]
  calc t * (n⁻¹ * (t * n * t)) * t = t * n⁻¹ * t * n * (t * t) := by group
    _ = t * n⁻¹ * t * n := by rw [htt, mul_one]
    _ = t * n⁻¹ * t⁻¹ * n := by rw [htinv]
    _ = (n⁻¹ * (t * n * t⁻¹))⁻¹ := by group
    _ = (n⁻¹ * (t * n * t))⁻¹ := by rw [htinv]

theorem invClass_core {G : Type*} [Group G] [Finite G] {s t t₁ t₂ : G} {n a : ℕ}
    {Q : Subgroup G} (hs : ∀ g : G, s * g = g * s) (hs7 : orderOf s = 7) (ht2 : t ^ 2 = 1)
    (ht1 : t ≠ 1) (hn : n ≤ (conjugatesOf t).ncard) (hQt : Q ≤ Subgroup.centralizer {t})
    (hQ : Nat.card Q = 2 ^ a) (hG : Nat.card G = 2 ^ a * (7 * n)) (hodd : Odd n)
    (hinv : ∀ q ∈ Q, q ^ 2 = 1 → q ≠ 1 → IsConj t q) (h₁ : IsConj t t₁) (h₂ : IsConj t t₂)
    (h7 : orderOf (t * t₁ * t₂) = 7) :
    (∀ c : G, orderOf c ≠ 6) ∧
      ∀ N : Subgroup G, N.Normal → Nat.Coprime 7 (Nat.card N) → N = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := Subgroup.centralizer ({t} : Set G) with hD
  have hcop : Nat.Coprime (2 ^ a) 7 := Nat.Coprime.pow_left a (by norm_num)
  have hDle : Nat.card D ≤ 2 ^ a * 7 := by
    have h1 := D.card_mul_index
    rw [hD, Subgroup.index_centralizer_eq_ncard, hG] at h1
    have hn0 : 0 < n := hodd.pos
    have h2 : Nat.card D * n ≤ 2 ^ a * 7 * n := by
      calc Nat.card D * n ≤ Nat.card D * (conjugatesOf t).ncard := Nat.mul_le_mul_left _ hn
        _ = 2 ^ a * (7 * n) := h1
        _ = 2 ^ a * 7 * n := by ring
    exact Nat.le_of_mul_le_mul_right h2 hn0
  have hsD : s ∈ D := Subgroup.mem_centralizer_singleton_iff.2 (hs t)
  have hDdvd : 2 ^ a * 7 ∣ Nat.card D := by
    refine hcop.mul_dvd_of_dvd_of_dvd ?_ ?_
    · rw [← hQ]
      exact Subgroup.card_dvd_of_le hQt
    · rw [← hs7]
      exact Subgroup.orderOf_dvd_natCard D hsD
  have hDcard : Nat.card D = 2 ^ a * 7 :=
    le_antisymm hDle (Nat.le_of_dvd Nat.card_pos hDdvd)
  have hD3 : ∀ x ∈ D, orderOf x ≠ 3 := by
    intro x hx h3
    have h := Subgroup.orderOf_dvd_natCard D hx
    rw [h3, hDcard] at h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
      omega
    · omega
  have hQp : IsPGroup 2 Q := IsPGroup.of_card hQ
  have hQidx : ¬ 2 ∣ Q.index := by
    have h1 := Q.card_mul_index
    rw [hQ, hG] at h1
    have h2 : Q.index = 7 * n := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [h2]
    intro h
    have h7n : Odd (7 * n) := (by decide : Odd 7).mul hodd
    exact (Nat.not_even_iff_odd.2 h7n) (even_iff_two_dvd.2 h)
  let P : Sylow 2 G := hQp.toSylow hQidx
  have hall : ∀ u : G, u ^ 2 = 1 → u ≠ 1 → IsConj t u := by
    intro u hu2 hu1
    have ho : orderOf u = 2 := orderOf_eq_prime hu2 hu1
    have hup : IsPGroup 2 (Subgroup.zpowers u) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ho, pow_one])
    obtain ⟨P', hP'⟩ := hup.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P P'
    have hu : u ∈ ((g • P : Sylow 2 G) : Subgroup G) := by
      rw [hg]
      exact hP' (Subgroup.mem_zpowers u)
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hu
    obtain ⟨q, hq, rfl⟩ := hu
    have hqQ : q ∈ Q := by
      have e : ((P : Subgroup G)) = Q := IsPGroup.toSylow_coe hQp hQidx
      rw [← e]
      exact hq
    rw [MulAut.smul_def, MulAut.conj_apply] at hu2 hu1 ⊢
    have hq2 : q ^ 2 = 1 := by
      have : g * q ^ 2 * g⁻¹ = 1 := by rw [← conj_pow, hu2]
      rwa [mul_inv_eq_one, mul_eq_left] at this
    have hq1 : q ≠ 1 := by
      rintro rfl
      exact hu1 (by group)
    exact (hinv q hqQ hq2 hq1).trans (isConj_iff.2 ⟨g, rfl⟩)
  refine ⟨fun r hr6 => ?_, fun N hN h7N => ?_⟩
  ·
    have ho3 : orderOf (r ^ 3) = 2 := by
      rw [orderOf_pow' r (by norm_num), hr6]
      rfl
    have hr3 : r ^ 3 ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ho3
      omega
    obtain ⟨c, hc⟩ := isConj_iff.1 (hall (r ^ 3) (by rw [← ho3]; exact pow_orderOf_eq_one _) hr3)
    have ho2 : orderOf (r ^ 2) = 3 := by
      rw [orderOf_pow' r (by norm_num), hr6]
      rfl
    have hv : c⁻¹ * r ^ 2 * c ∈ D := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm : r ^ 3 * r ^ 2 = r ^ 2 * r ^ 3 := by rw [← pow_add, ← pow_add, add_comm]
      rw [← hc] at hcomm
      obtain ⟨y, hy⟩ : ∃ y, y = r ^ 2 := ⟨_, rfl⟩
      rw [← hy] at hcomm ⊢
      refine (?_ : t * (c⁻¹ * y * c) = c⁻¹ * y * c * t).symm
      calc t * (c⁻¹ * y * c) = c⁻¹ * ((c * t * c⁻¹) * y) * c := by group
        _ = c⁻¹ * (y * (c * t * c⁻¹)) * c := by rw [hcomm]
        _ = c⁻¹ * y * c * t := by group
    refine hD3 _ hv ?_
    have e := MulEquiv.orderOf_eq (MulAut.conj c⁻¹) (r ^ 2)
    rw [MulAut.conj_apply, inv_inv] at e
    rw [e, ho2]
  ·
    have hconjN : ∀ u, IsConj t u → t ∈ N → u ∈ N := by
      intro u hu htN
      obtain ⟨c, rfl⟩ := isConj_iff.1 hu
      exact hN.conj_mem t htN c
    by_cases hev : 2 ∣ Nat.card N
    · exfalso
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 hev
      have hu2 : (u : G) ^ 2 = 1 := by
        have := congrArg Subtype.val (pow_orderOf_eq_one u)
        rw [hu] at this
        simpa using this
      have hu1 : (u : G) ≠ 1 := by
        intro h
        have : u = 1 := Subtype.ext h
        rw [this, orderOf_one] at hu
        omega
      obtain ⟨c, hc⟩ := isConj_iff.1 (hall u hu2 hu1)
      have htN : t ∈ N := by
        have := hN.conj_mem (u : G) u.2 c⁻¹
        rwa [← hc, inv_inv, show c⁻¹ * (c * t * c⁻¹) * c = t by group] at this
      have hw : t * t₁ * t₂ ∈ N :=
        N.mul_mem (N.mul_mem htN (hconjN _ h₁ htN)) (hconjN _ h₂ htN)
      have h7d := Subgroup.orderOf_dvd_natCard N hw
      rw [h7] at h7d
      have := Nat.Coprime.eq_one_of_dvd h7N h7d
      omega
    · have hfree : ∀ x ∈ N, t * x = x * t → x = 1 := by
        intro x hx hxt
        have hxD : x ∈ N ⊓ D := ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 hxt.symm⟩
        have hcard : Nat.card (N ⊓ D : Subgroup G) = 1 := by
          have h1 : Nat.card (N ⊓ D : Subgroup G) ∣ Nat.card N :=
            Subgroup.card_dvd_of_le inf_le_left
          have h2 : Nat.card (N ⊓ D : Subgroup G) ∣ 2 ^ a * 7 := by
            rw [← hDcard]
            exact Subgroup.card_dvd_of_le inf_le_right
          have hc : Nat.Coprime (Nat.card N) (2 ^ a * 7) := by
            refine Nat.Coprime.mul_right ?_ h7N.symm
            refine Nat.Coprime.pow_right a ?_
            exact (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hev))
          have hg := Nat.dvd_gcd h1 h2
          rw [hc.gcd_eq_one] at hg
          exact Nat.dvd_one.1 hg
        have := Subgroup.card_eq_one.1 hcard
        rw [this] at hxD
        exact hxD
      have ht := inv_of_fixedPointFree ht2 hfree
      have hw : ∀ x ∈ N, (t * t₁ * t₂) * x * (t * t₁ * t₂)⁻¹ = x⁻¹ := by
        intro x hx
        have e1 := inv_of_conj ht h₁
        have e2 := inv_of_conj ht h₂
        have hx2 : t₂ * x * t₂⁻¹ ∈ N := hN.conj_mem x hx t₂
        have hx1 : t₁ * (t₂ * x * t₂⁻¹) * t₁⁻¹ ∈ N := hN.conj_mem _ hx2 t₁
        calc (t * t₁ * t₂) * x * (t * t₁ * t₂)⁻¹
            = t * (t₁ * (t₂ * x * t₂⁻¹) * t₁⁻¹) * t⁻¹ := by group
          _ = x⁻¹ := by rw [ht _ hx1, e1 _ hx2, e2 _ hx, inv_inv]
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      set w := t * t₁ * t₂
      have hw7 : w ^ 7 = 1 := by rw [← h7]; exact pow_orderOf_eq_one w
      have hw2 : Commute (w * w) x := by
        have e := hw _ (N.inv_mem hx)
        have e2 : w * w * x * (w * w)⁻¹ = x := by
          calc w * w * x * (w * w)⁻¹ = w * (w * x * w⁻¹) * w⁻¹ := by group
            _ = x := by rw [hw x hx, e, inv_inv]
        exact mul_inv_eq_iff_eq_mul.1 e2
      have hw8 : Commute ((w * w) ^ 4) x := hw2.pow_left 4
      have hw8' : (w * w) ^ 4 = w := by
        rw [← pow_two, ← pow_mul, show 2 * 4 = 7 + 1 by rfl, pow_succ, hw7, one_mul]
      rw [hw8'] at hw8
      have hxx : x⁻¹ = x := by
        rw [← hw x hx, hw8.eq, mul_inv_cancel_right]
      have hx2 : x ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 1 [← hxx]
        exact inv_mul_cancel x
      have hd := orderOf_dvd_of_pow_eq_one hx2
      have hdN : orderOf x ∣ Nat.card N := by
        have := Subgroup.orderOf_dvd_natCard N hx
        exact this
      rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
      · exact orderOf_eq_one_iff.1 h
      · rw [h] at hdN
        exact absurd hdN hev

end CFSG.KD.StdOdd.Cent7

end
