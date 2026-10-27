
module

public import Certificates.Kernel.Parrott946.Glue17o

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups CertificateChecks.KernelA45 Subgroup
  CFSG.Sporadic.SmallOddCore CFSG.KC.SylowReps
open CFSG.Sporadic.Schreier (tab_eq)

local notation "P45" => Equiv.Perm (Fin 45)

abbrev pw5 : List P45 := [1, b5, b5 * b5, b5 * b5 * b5, b5 * b5 * b5 * b5]

theorem mem_pw5 {x : P45} : x ∈ pw5 ↔ ∃ k < 5, x = b5 ^ k := by
  constructor
  · intro h
    simp only [pw5, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h
    · exact ⟨0, by norm_num, by rw [h, pow_zero]⟩
    · exact ⟨1, by norm_num, by rw [h, pow_one]⟩
    · exact ⟨2, by norm_num, by rw [h, sq]⟩
    · exact ⟨3, by norm_num, by rw [h, pow_succ, sq]⟩
    · exact ⟨4, by norm_num, by rw [h, pow_succ, pow_succ, sq]⟩
  · rintro ⟨k, hk, rfl⟩
    interval_cases k <;> simp [pw5, pow_succ]

theorem pow_mem_pw5 (n : ℕ) : b5 ^ n ∈ pw5 :=
  mem_pw5.2 ⟨n % 5, Nat.mod_lt _ (by norm_num), by rw [← orderOf_b5, pow_mod_orderOf]⟩

theorem b5Norm_eq :
    b5NormalizerCount () = ((elemsT QA45).filter fun c => decide (c * b5 * c⁻¹ ∈ pw5)).length := by
  simp [b5NormalizerCount, tab_eq, tabList_eq]

theorem b5Norm_card :
    b5NormalizerCount () = Nat.card {g : A // (g : P45) * b5 * (g : P45)⁻¹ ∈ pw5} := by
  rw [b5Norm_eq]
  exact (card_filter QA45 QA45_ok (fun g => g * b5 * g⁻¹ ∈ pw5)).symm

noncomputable abbrev w5 : P45 := wv17 11

theorem w5_memA : w5 ∈ A := (prep_wE (k := 11) (by norm_num)).2

theorem w5_conj (i : ℕ) : w5 ^ i * b5 * (w5 ^ i)⁻¹ = b5 ^ (2 ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    have hw : w5 * b5 * w5⁻¹ = b5 ^ 2 := by
      rw [b5_facts.2.2.2.1, sq]
      group
    calc w5 ^ (i + 1) * b5 * (w5 ^ (i + 1))⁻¹ = w5 * (w5 ^ i * b5 * (w5 ^ i)⁻¹) * w5⁻¹ := by
          group
      _ = (w5 * b5 * w5⁻¹) ^ (2 ^ i) := by rw [ih, conj_pow]
      _ = b5 ^ (2 ^ (i + 1)) := by rw [hw, ← pow_mul, pow_succ, mul_comm]

theorem conj_wx {i : ℕ} {x : P45} (hx : x * b5 = b5 * x) :
    w5 ^ i * x * b5 * (w5 ^ i * x)⁻¹ = b5 ^ (2 ^ i) := by
  rw [← w5_conj i]
  calc w5 ^ i * x * b5 * (w5 ^ i * x)⁻¹ = w5 ^ i * (x * b5) * x⁻¹ * (w5 ^ i)⁻¹ := by group
    _ = w5 ^ i * b5 * (w5 ^ i)⁻¹ := by rw [hx]; group

theorem two_pow_inj : ∀ i j : Fin 4, 2 ^ (i : ℕ) % 5 = 2 ^ (j : ℕ) % 5 → i = j := by decide

theorem two_pow_surj : ∀ k < 5, k ≠ 0 → ∃ i : Fin 4, 2 ^ (i : ℕ) % 5 = k := by decide

theorem card_normB :
    Nat.card {g : A // (g : P45) * b5 * (g : P45)⁻¹ ∈ pw5} = 4 * Nat.card CB := by
  let F : Fin 4 × CB → {g : A // (g : P45) * b5 * (g : P45)⁻¹ ∈ pw5} := fun p =>
    ⟨⟨w5 ^ (p.1 : ℕ) * p.2, A.mul_mem (A.pow_mem w5_memA _) (mem_CB.1 p.2.2).1⟩, by
      change w5 ^ (p.1 : ℕ) * p.2 * b5 * (w5 ^ (p.1 : ℕ) * p.2)⁻¹ ∈ pw5
      rw [conj_wx (mem_CB.1 p.2.2).2]
      exact pow_mem_pw5 _⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, x⟩ ⟨j, y⟩ e
      have e' : w5 ^ (i : ℕ) * (x : P45) = w5 ^ (j : ℕ) * y :=
        congrArg (fun g : {g : A // (g : P45) * b5 * (g : P45)⁻¹ ∈ pw5} => ((g : A) : P45)) e
      have hc : b5 ^ (2 ^ (i : ℕ)) = b5 ^ (2 ^ (j : ℕ)) := by
        rw [← conj_wx (mem_CB.1 x.2).2, ← conj_wx (mem_CB.1 y.2).2, e']
      rw [pow_eq_pow_iff_modEq, orderOf_b5] at hc
      have hij := two_pow_inj i j hc
      subst hij
      have hxy : (x : P45) = y := mul_left_cancel e'
      rw [Subtype.ext hxy]
    · rintro ⟨c, hc⟩
      obtain ⟨k, hk, hck⟩ := mem_pw5.1 hc
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hck
        apply b5_ne_one
        calc b5 = (c : P45)⁻¹ * ((c : P45) * b5 * (c : P45)⁻¹) * c := by group
          _ = 1 := by rw [hck]; group
      obtain ⟨i, hi⟩ := two_pow_surj k hk hk0
      have hcw : (c : P45) * b5 * (c : P45)⁻¹ = w5 ^ (i : ℕ) * b5 * (w5 ^ (i : ℕ))⁻¹ := by
        rw [hck, w5_conj, ← hi, ← orderOf_b5, pow_mod_orderOf]
      have hxB : (w5 ^ (i : ℕ))⁻¹ * c ∈ CB := by
        refine mem_CB.2 ⟨A.mul_mem (A.inv_mem (A.pow_mem w5_memA _)) c.2, ?_⟩
        calc (w5 ^ (i : ℕ))⁻¹ * c * b5
            = (w5 ^ (i : ℕ))⁻¹ * ((c : P45) * b5 * (c : P45)⁻¹) * c := by group
          _ = (w5 ^ (i : ℕ))⁻¹ * (w5 ^ (i : ℕ) * b5 * (w5 ^ (i : ℕ))⁻¹) * c := by rw [hcw]
          _ = b5 * ((w5 ^ (i : ℕ))⁻¹ * c) := by group
      refine ⟨⟨i, ⟨_, hxB⟩⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      change w5 ^ (i : ℕ) * ((w5 ^ (i : ℕ))⁻¹ * c) = c
      group
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 4),
    Fintype.card_fin]

theorem mem_normalizer_zpowers {G : Type*} [Group G] [Finite G] {x g : G}
    (h : g * x * g⁻¹ ∈ zpowers x) : g ∈ normalizer (zpowers x : Set G) := by
  have hc : ∀ y ∈ zpowers x, g * y * g⁻¹ ∈ zpowers x := by
    rintro _ ⟨m, rfl⟩
    change g * x ^ m * g⁻¹ ∈ zpowers x
    rw [← conj_zpow]
    exact (zpowers x).zpow_mem h m
  rw [mem_normalizer_iff]
  intro y
  refine ⟨hc y, fun hy => ?_⟩
  let φ : zpowers x → zpowers x := fun z => ⟨g * z * g⁻¹, hc z z.2⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    have e := congrArg Subtype.val hab
    simpa [φ] using e
  obtain ⟨z, hz⟩ := Finite.surjective_of_injective hφ ⟨_, hy⟩
  have e := congrArg Subtype.val hz
  simp only [φ, mul_left_inj, mul_right_inj] at e
  exact e ▸ z.2

theorem arith_b5 : ∀ a ≤ 7, ∀ n : ℕ, 4 * (5 * 2 ^ a) * n = 51840 → n % 5 = 1 →
    5 * 2 ^ a ≠ 160 → 5 * 2 ^ a = 10 := by
  intro a ha
  interval_cases a <;> intro n h1 h2 h3 <;> simp only [pow_succ, pow_zero] at h1 h3 ⊢ <;> omega

theorem card_CB : Nat.card CB = 10 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let bA : A := ⟨b5, b5_memA⟩
  have hord : orderOf bA = 5 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_b5
  have hcard : Nat.card (zpowers bA) = 5 ^ (Nat.card A).factorization 5 := by
    have e : (51840 : ℕ) = 5 ^ 1 * 10368 := by norm_num
    rw [Nat.card_zpowers, hord, card_A, e, pow_factorization_eq (by norm_num) (by norm_num),
      pow_one]
  let S : Sylow 5 A := Sylow.ofCard _ hcard
  have hS : ((S : Subgroup A) : Set A) = (zpowers bA : Set A) := by
    rw [Sylow.coe_ofCard]
  have hmem : ∀ g : A, g ∈ normalizer ((S : Subgroup A) : Set A) ↔
      (g : P45) * b5 * (g : P45)⁻¹ ∈ pw5 := by
    intro g
    rw [hS]
    constructor
    · intro hg
      have h1 := ((mem_normalizer_iff.1 hg) bA).1 (mem_zpowers bA)
      obtain ⟨m, hm⟩ := mem_zpowers_iff.1 h1
      have e : (b5 : P45) ^ m = (g : P45) * b5 * (g : P45)⁻¹ := by
        have := congrArg Subtype.val hm
        simpa [bA] using this
      have hp : (b5 : P45) ^ m ∈ Submonoid.powers b5 :=
        (isOfFinOrder_of_finite b5).mem_powers_iff_mem_zpowers.2 (zpow_mem (mem_zpowers b5) m)
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 hp
      rw [← e, ← hn]
      exact pow_mem_pw5 n
    · intro hg
      obtain ⟨k, -, hk⟩ := mem_pw5.1 hg
      refine mem_normalizer_zpowers ⟨k, ?_⟩
      apply Subtype.ext
      simp only [zpow_natCast, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hk.symm
  have hN : Nat.card (normalizer ((S : Subgroup A) : Set A)) = 4 * Nat.card CB := by
    rw [← card_normB]
    exact Nat.card_congr (Equiv.subtypeEquivRight hmem)
  have hmod : (normalizer ((S : Subgroup A) : Set A)).index % 5 = 1 := by
    have h := card_sylow_modEq_one 5 A
    rw [Sylow.card_eq_index_normalizer S] at h
    exact h
  have hmul := card_mul_index (normalizer ((S : Subgroup A) : Set A))
  rw [hN, card_A] at hmul
  obtain ⟨a, ha, hCB⟩ := card_CB_form
  have h5 := not_a5
  rw [hCB] at hmul h5 ⊢
  exact arith_b5 a ha _ hmul hmod h5

theorem b5_centralizer : commCount b5 = 10 := by
  rw [commCount_eq, filter_cent]
  exact card_CB

theorem b5_normalizer : b5NormalizerCount () = 40 := by
  rw [b5Norm_card, card_normB, card_CB]

end CertificateChecks.Parrott946

end
