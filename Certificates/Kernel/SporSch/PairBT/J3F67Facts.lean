module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CentralizerCard
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67SporAbs
public import CFSG.CGT.Timmesfeld75.A6Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J3CentralizerA6

public section

namespace CertificateChecks.KernelSporSch.J3F67

open Subgroup CFSG.AGLEmbeddingD2.Wilson.NormalizerAction CFSG.Sporadic.Schreier
open scoped commutatorElement

theorem perm_six_no_order_fifteen :
    ∀ σ : Equiv.Perm (Fin 6), σ ^ 15 = 1 → σ ^ 3 = 1 ∨ σ ^ 5 = 1 := by
  decide +kernel

theorem A6_no_comm {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 6)) {x y : K}
    (hx : x ^ 3 = 1) (hx1 : x ≠ 1) (hy : y ^ 5 = 1) (hy1 : y ≠ 1) (hxy : x * y = y * x) :
    False := by
  have hc : Commute x y := hxy
  have key : ∀ k : ℕ, ((e (x * y) : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) ^ k = 1 ↔
      (x * y) ^ k = 1 := by
    intro k
    rw [← Subgroup.coe_pow, ← map_pow, OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff]
  have hx' : orderOf x = 3 := orderOf_eq_prime hx hx1
  have hy' : orderOf y = 5 := orderOf_eq_prime hy hy1
  have h15 : (x * y) ^ 15 = 1 := by
    rw [hc.mul_pow, show (15 : ℕ) = 3 * 5 from rfl, pow_mul, hx, one_pow, one_mul,
      show (3 * 5 : ℕ) = 5 * 3 from rfl, pow_mul, hy, one_pow]
  rcases perm_six_no_order_fifteen _ ((key 15).2 h15) with h | h
  · rw [key, hc.mul_pow, hx, one_mul] at h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hy'] at this
    omega
  · rw [key, hc.mul_pow, hy, mul_one] at h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hx'] at this
    omega


set_option linter.unusedSectionVars false

theorem no_triple_five {A B Y : Equiv.Perm (Fin 6156)} (hA : A ∈ j3P) (hB : B ∈ j3P)
    (hY : Y ∈ j3P) (hA3 : A ^ 3 = 1) (hB3 : B ^ 3 = 1) (hA1 : A ≠ 1) (hBA : B ∉ zpowers A)
    (hY5 : Y ^ 5 = 1) (hY1 : Y ≠ 1) (hAB : A * B = B * A) (hAY : A * Y = Y * A)
    (hBY : B * Y = Y * B) : False := by
  set C : Subgroup (Equiv.Perm (Fin 6156)) := centralizer ({A} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P
    with hCdef
  have hoA : orderOf A = 3 := orderOf_eq_prime hA3 hA1
  have memC : ∀ {Z : Equiv.Perm (Fin 6156)}, Z ∈ j3P → A * Z = Z * A → Z ∈ C := fun hZ h =>
    ⟨mem_centralizer_singleton_iff.2 h.symm, hZ⟩
  have hAC : A ∈ C := memC hA rfl
  have hBC : B ∈ C := memC hB hAB
  have hYC : Y ∈ C := memC hY hAY
  have h5 : 5 ∣ Nat.card C := by
    have ho : orderOf (⟨Y, hYC⟩ : C) = 5 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime hY5 hY1
    rw [← ho]
    exact orderOf_dvd_natCard _
  have hcard : Nat.card C = 1080 := card_centralizer_j3P_of_five_dvd hA hoA h5
  obtain ⟨D, hDC, hcomm, -, ⟨e⟩⟩ := exists_A6_in_centralizer_j3P hA hoA h5
  have hDcard : Nat.card D = 360 := by
    rw [Nat.card_congr e.toEquiv, CFSG.CGT.Timmesfeld75.card_alternatingGroup_six]
  set D' : Subgroup C := D.subgroupOf C with hD'
  have hD'n : D'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hk : ⁅(g : Equiv.Perm (Fin 6156)), (n : Equiv.Perm (Fin 6156))⁆ ∈ D :=
      hcomm (Subgroup.commutator_mem_commutator g.2 n.2)
    have he : ((g * n * g⁻¹ : C) : Equiv.Perm (Fin 6156)) =
        ⁅(g : Equiv.Perm (Fin 6156)), (n : Equiv.Perm (Fin 6156))⁆ * n := by
      simp [commutatorElement_def]
    rw [he]
    exact D.mul_mem hk hn
  have hQ : Nat.card (C ⧸ D') = 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup D'
    have h2 : Nat.card D' = 360 := by
      rw [hD', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv, hDcard]
    rw [hcard, h2] at h1
    omega
  let q : C →* C ⧸ D' := QuotientGroup.mk' D'
  have hq : ∀ z : C, q z = 1 → (z : Equiv.Perm (Fin 6156)) ∈ D := fun z hz => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hz
    exact hz
  have hpow3 : ∀ u : C ⧸ D', u ^ 3 = 1 := fun u => by
    rw [← hQ]
    exact pow_card_eq_one'
  have hYD : Y ∈ D := by
    refine hq ⟨Y, hYC⟩ ?_
    have h6 : (⟨Y, hYC⟩ : C) = (⟨Y, hYC⟩ : C) ^ 6 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow]
      rw [show (6 : ℕ) = 5 + 1 from rfl, pow_succ, hY5, one_mul]
    rw [h6, map_pow, show (6 : ℕ) = 3 * 2 from rfl, pow_mul, hpow3, one_pow]
  have hX : ∃ X : Equiv.Perm (Fin 6156), X ∈ D ∧ X ^ 3 = 1 ∧ X ≠ 1 ∧ X * Y = Y * X := by
    have hcAB : Commute A B := hAB
    by_cases ha : q ⟨A, hAC⟩ = 1
    · exact ⟨A, hq _ ha, hA3, hA1, hAY⟩
    · have hprime : (Nat.card (C ⧸ D')).Prime := by rw [hQ]; norm_num
      have htop : zpowers (q ⟨A, hAC⟩) = ⊤ := by
        have := Fact.mk hprime
        rcases Subgroup.eq_bot_or_eq_top_of_prime_card (zpowers (q ⟨A, hAC⟩)) with h | h
        · exact absurd (zpowers_eq_bot.1 h) ha
        · exact h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (htop ▸ Subgroup.mem_top (q ⟨B, hBC⟩))
      refine ⟨B * A ^ (-k), ?_, ?_, ?_, ?_⟩
      · have : q (⟨B, hBC⟩ * (⟨A, hAC⟩ : C) ^ (-k)) = 1 := by
          rw [map_mul, map_zpow, ← hk, ← zpow_add, add_neg_cancel, zpow_zero]
        exact hq _ this
      · rw [(hcAB.symm.zpow_right (-k)).mul_pow, hB3, one_mul, ← zpow_natCast,
          ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hA3, one_zpow]
      · intro h1
        apply hBA
        rw [Subgroup.mem_zpowers_iff]
        exact ⟨k, by rw [mul_eq_one_iff_eq_inv.1 h1, zpow_neg, inv_inv]⟩
      · have hcAY : Commute A Y := hAY
        have hcBY : Commute B Y := hBY
        exact (hcBY.mul_left (hcAY.zpow_left (-k)))
  obtain ⟨X, hXD, hX3, hX1, hXY⟩ := hX
  refine A6_no_comm e (x := ⟨X, hXD⟩) (y := ⟨Y, hYD⟩) ?_ ?_ ?_ ?_ ?_
  · exact Subtype.ext (by simpa using hX3)
  · exact fun h => hX1 (by simpa using congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using hY5)
  · exact fun h => hY1 (by simpa using congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using hXY)

theorem triples_j3P :
    ∀ (r s : ℕ) (a b y : ↥j3P), r.Prime → s.Prime → Odd r → Odd s → r ≠ s →
      a ^ r = 1 → b ^ r = 1 → y ^ s = 1 → a ≠ 1 → b ∉ Subgroup.zpowers a → y ≠ 1 →
        a * b = b * a → a * y = y * a → b * y = y * b → False := by
  intro r s a b y hr hs hro hso hrs ha hb hy ha1 hb1 hy1 hab hay hby
  have hG : Nat.card j3P = 50232960 := card_j3P
  have hfac : Nat.primeFactorsList 50232960 =
      [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 5, 17, 19] := by
    norm_num
  have hmem : ∀ q : ℕ, q.Prime → q ∣ 50232960 → q = 2 ∨ q = 3 ∨ q = 5 ∨ q = 17 ∨ q = 19 := by
    intro q hq hd
    have := (Nat.mem_primeFactorsList (by norm_num : (50232960 : ℕ) ≠ 0)).2 ⟨hq, hd⟩
    rw [hfac] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega
  have hr2 : r ^ 2 ∣ 50232960 := by
    rw [← hG]
    exact (CFSG.GH74.GLS.Stage2.Bender.Thm1.sq_dvd_card_closure_pair hr ha hb hab ha1 hb1).trans
      (Subgroup.card_subgroup_dvd_card _)
  have hr3 : r = 3 := by
    rcases hmem r hr ((dvd_pow_self r two_ne_zero).trans hr2) with rfl | rfl | rfl | rfl | rfl
    · exact absurd hro (by decide)
    · rfl
    all_goals norm_num at hr2
  subst hr3
  have hv : ∀ {u : ↥j3P} {k : ℕ}, u ^ k = 1 → (u : Equiv.Perm (Fin 6156)) ^ k = 1 := fun h => by
    simpa using congrArg Subtype.val h
  have hv1 : ∀ {u : ↥j3P}, u ≠ 1 → (u : Equiv.Perm (Fin 6156)) ≠ 1 := fun h h' =>
    h (Subtype.ext (by simpa using h'))
  have hvc : ∀ {u v : ↥j3P}, u * v = v * u →
      (u : Equiv.Perm (Fin 6156)) * v = v * u := fun h => by simpa using congrArg Subtype.val h
  have hbA : (b : Equiv.Perm (Fin 6156)) ∉ zpowers (a : Equiv.Perm (Fin 6156)) := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    exact hb1 (Subgroup.mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩)
  have hoA : orderOf (a : Equiv.Perm (Fin 6156)) = 3 := orderOf_eq_prime (hv ha) (hv1 ha1)
  have hsC : s ∣ Nat.card (centralizer ({(a : Equiv.Perm (Fin 6156))} :
      Set (Equiv.Perm (Fin 6156))) ⊓ j3P : Subgroup (Equiv.Perm (Fin 6156))) := by
    have := Fact.mk hs
    set C : Subgroup (Equiv.Perm (Fin 6156)) := centralizer ({(a : Equiv.Perm (Fin 6156))} :
        Set (Equiv.Perm (Fin 6156))) ⊓ j3P with hC
    have hYC : (y : Equiv.Perm (Fin 6156)) ∈ C :=
      ⟨mem_centralizer_singleton_iff.2 (hvc hay).symm, y.2⟩
    have ho : orderOf (⟨_, hYC⟩ : C) = s := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (hv hy) (hv1 hy1)
    rw [← ho]
    exact orderOf_dvd_natCard _
  have hsG : s ∣ 50232960 := by
    rw [← hG]
    have := Fact.mk hs
    rw [← orderOf_eq_prime hy hy1]
    exact orderOf_dvd_natCard _
  rcases hmem s hs hsG with rfl | rfl | rfl | rfl | rfl
  · exact absurd hso (by decide)
  · exact hrs rfl
  · exact no_triple_five a.2 b.2 y.2 (hv ha) (hv hb) (hv1 ha1) hbA (hv hy) (hv1 hy1) (hvc hab)
      (hvc hay) (hvc hby)
  all_goals
    rcases card_centralizer_j3P_dichotomy a.2 hoA with h | h <;> rw [h] at hsC <;> norm_num at hsC

end CertificateChecks.KernelSporSch.J3F67

end
