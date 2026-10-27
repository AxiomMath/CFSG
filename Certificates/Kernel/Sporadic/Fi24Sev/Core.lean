module

public import Certificates.Kernel.Sporadic.Fi24Sev.SevenB
public import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.KD.Fi24Sev.Core

open CFSG.Open

section Generic

variable {G : Type*} [Group G]

theorem conj_pow_mem {P : Subgroup G} {g : G} (hP : ∀ k ∈ P, g * k * g⁻¹ ∈ P) :
    ∀ n : ℕ, ∀ k ∈ P, g ^ n * k * (g ^ n)⁻¹ ∈ P := by
  intro n
  induction n with
  | zero => intro k hk; simpa using hk
  | succ n ih =>
    intro k hk
    have h := hP _ (ih k hk)
    rw [pow_succ']
    convert h using 1
    simp only [mul_inv_rev, mul_assoc]

theorem conj_eq_of_mul_eq {a b c : G} (h : a * b = c * a) : a * b * a⁻¹ = c := by
  rw [h, mul_inv_cancel_right]

theorem exists_inv_mod_seven : ∀ d : ℕ, 0 < d → d < 7 → ∃ e : ℕ, d * e % 7 = 1 := by
  intro d h0 h7
  interval_cases d
  exacts [⟨1, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨6, rfl⟩]

theorem commute_of_pow_commute {x k : G} (hx : x ^ 7 = 1) {d : ℕ} (h0 : 0 < d) (h7 : d < 7)
    (h : x ^ d * k = k * x ^ d) : x * k = k * x := by
  obtain ⟨e, he⟩ := exists_inv_mod_seven d h0 h7
  have hc : Commute ((x ^ d) ^ e) k := (show Commute (x ^ d) k from h).pow_left e
  rw [← pow_mul, pow_eq_pow_mod _ hx, he, pow_one] at hc
  exact hc.eq

theorem commute_of_conj_eq {x k : G} (hx : x ^ 7 = 1) {i j : ℕ} (hij : i < j) (hj : j < 7)
    (h : x ^ i * k * (x ^ i)⁻¹ = x ^ j * k * (x ^ j)⁻¹) : x * k = k * x := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  refine commute_of_pow_commute hx (d := d) (by omega) (by omega) ?_
  rw [pow_add] at h
  have h2 : k = x ^ d * k * (x ^ d)⁻¹ := by
    calc k = (x ^ i)⁻¹ * (x ^ i * k * (x ^ i)⁻¹) * x ^ i := by group
      _ = (x ^ i)⁻¹ * (x ^ i * x ^ d * k * (x ^ i * x ^ d)⁻¹) * x ^ i := by rw [h]
      _ = x ^ d * k * (x ^ d)⁻¹ := by group
  calc x ^ d * k = x ^ d * k * (x ^ d)⁻¹ * x ^ d := by group
    _ = k * x ^ d := by rw [← h2]

theorem commute_of_card_lt [Finite G] {K : Subgroup G} {x : G} (hx : x ^ 7 = 1)
    (hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hcard : Nat.card K < 7) : ∀ k ∈ K, x * k = k * x := by
  intro k hk
  let f : Fin 7 → K := fun i => ⟨x ^ (i : ℕ) * k * (x ^ (i : ℕ))⁻¹, conj_pow_mem hxK i k hk⟩
  have hf : ¬ Function.Injective f := fun hf => by
    have := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  simp only [Function.Injective, not_forall, exists_prop] at hf
  obtain ⟨i, j, hij, hne⟩ := hf
  have hv : x ^ (i : ℕ) * k * (x ^ (i : ℕ))⁻¹ = x ^ (j : ℕ) * k * (x ^ (j : ℕ))⁻¹ :=
    congrArg Subtype.val hij
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : (i : ℕ) ≠ j) with h | h
  · exact commute_of_conj_eq hx h j.2 hv
  · exact commute_of_conj_eq hx h i.2 hv.symm

theorem card_mul_index_subgroupOf {H K : Subgroup G} (hKH : K ≤ H) :
    Nat.card K * (K.subgroupOf H).index = Nat.card H := by
  rw [← (K.subgroupOf H).card_mul_index, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]

theorem mem_of_coprime_index [Finite G] {H K : Subgroup G} (hKH : K ≤ H)
    (hn : (K.subgroupOf H).Normal) {u : G} (hu : u ∈ H) {m : ℕ} (hum : u ^ m = 1)
    (hcop : Nat.Coprime m (K.subgroupOf H).index) : u ∈ K := by
  have : (K.subgroupOf H).Normal := hn
  have h1 : (⟨u, hu⟩ : H) ^ m = 1 := Subtype.ext (by simp [hum])
  have h2 : orderOf ((⟨u, hu⟩ : H) : H ⧸ K.subgroupOf H) ∣ m := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]
  have h3 : orderOf ((⟨u, hu⟩ : H) : H ⧸ K.subgroupOf H) ∣ (K.subgroupOf H).index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have h4 : orderOf ((⟨u, hu⟩ : H) : H ⧸ K.subgroupOf H) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h3
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
  exact Subgroup.mem_subgroupOf.1 h4

theorem card_mod_seven [Finite G] {P : Subgroup G} {c : G} (hc : c ^ 7 = 1)
    (hcP : ∀ k ∈ P, c * k * c⁻¹ ∈ P) (hfix : ∀ k ∈ P, k * c = c * k → k = 1) :
    Nat.card P % 7 = 1 := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fintype P := Fintype.ofFinite _
  let f : Function.End P := fun k => ⟨c * k * c⁻¹, hcP k k.2⟩
  have hpow : ∀ (n : ℕ) (k : P), ((f ^ n) k : G) = c ^ n * k * (c ^ n)⁻¹ := by
    intro n
    induction n with
    | zero =>
      intro k
      rw [pow_zero, pow_zero, inv_one, one_mul, mul_one]
      rfl
    | succ n ih =>
      intro k
      rw [pow_succ']
      change c * ((f ^ n) k : G) * c⁻¹ = _
      rw [ih, pow_succ']
      simp only [mul_inv_rev, mul_assoc]
  have hf : f ^ 7 ^ 1 = 1 := by
    rw [pow_one]
    refine funext fun k => Subtype.ext ?_
    rw [hpow, hc, inv_one, one_mul, mul_one]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 7) (n := 1) hf
  have hfp : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, ?_⟩, fun ⟨k, hk⟩ => ?_⟩
    · change f 1 = 1
      apply Subtype.ext
      change c * 1 * c⁻¹ = 1
      group
    · have hk' : c * (k : G) * c⁻¹ = k := congrArg Subtype.val (hk : f k = k)
      have hkc : (k : G) * c = c * k := by
        calc (k : G) * c = c * k * c⁻¹ * c := by rw [hk']
          _ = c * k := by group
      exact Subtype.ext (Subtype.ext (hfix k k.2 hkc))
  rw [hfp] at hmod
  rw [Nat.card_eq_fintype_card]
  exact hmod

theorem factorization_pow_mul' {q : ℕ} (hq : q.Prime) (a m : ℕ) (hm : ¬ q ∣ m) :
    (q ^ a * m).factorization q = a := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero q)
  rw [Nat.factorization_mul (pow_ne_zero a hq.ne_zero) hm0, Finsupp.add_apply,
    hq.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm,
    add_zero]

theorem exists_conj_inv_sylow [Finite G] {K : Subgroup G} {c : G} (hc : c ^ 7 = 1)
    (hcK : ∀ k ∈ K, c * k * c⁻¹ ∈ K) {q : ℕ} [hq : Fact q.Prime] {a m : ℕ}
    (hK : Nat.card K = q ^ a * m) (hm : ¬ q ∣ m) (hlt : ∀ n, n ∣ m → n % q = 1 → n < 7) :
    ∃ P : Subgroup G, P ≤ K ∧ Nat.card P = q ^ a ∧ ∀ k ∈ P, c * k * c⁻¹ ∈ P := by
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow q K))
  have hfa : (Nat.card K).factorization q = a := by rw [hK, factorization_pow_mul' hq.out a m hm]
  have hS : Nat.card (S : Subgroup K) = q ^ a := by rw [S.card_eq_multiplicity, hfa]
  have hidx : (S : Subgroup K).index = m := by
    have := (S : Subgroup K).card_mul_index
    rw [hS, hK] at this
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hq.out.pos a) this
  have hn : Nat.card (Sylow q K) < 7 := by
    have h1 := card_sylow_modEq_one (p := q) (G := K)
    have h2 := S.card_dvd_index
    rw [hidx] at h2
    refine hlt _ h2 ?_
    rw [h1]
    exact Nat.mod_eq_of_lt hq.out.one_lt
  set P0 : Subgroup G := (S : Subgroup K).map K.subtype with hP0
  have hP0K : P0 ≤ K := Subgroup.map_subtype_le _
  have hP0c : Nat.card P0 = q ^ a := by
    rw [hP0, Subgroup.card_map_of_injective K.subtype_injective, hS]
  let Pi : ℕ → Subgroup G := fun i => P0.map (MulAut.conj (c ^ i)).toMonoidHom
  have hPiK : ∀ i, Pi i ≤ K := by
    intro i z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
    exact conj_pow_mem hcK i w (hP0K hw)
  have hPic : ∀ i, Nat.card (Pi i) = q ^ a := fun i => by
    rw [Subgroup.card_map_of_injective (MulAut.conj (c ^ i)).injective, hP0c]
  have hsub : ∀ i, Nat.card ((Pi i).subgroupOf K) = q ^ (Nat.card K).factorization q :=
    fun i => by
      rw [hfa, ← hPic i]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hPiK i)).toEquiv
  let F : Fin 7 → Sylow q K := fun i => Sylow.ofCard ((Pi i).subgroupOf K) (hsub i)
  have hF : ¬ Function.Injective F := fun hf => by
    have := Nat.card_le_card_of_injective F hf
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  simp only [Function.Injective, not_forall, exists_prop] at hF
  obtain ⟨i, j, hij, hne⟩ := hF
  have hPij : Pi i = Pi j := by
    have h := congrArg (fun S : Sylow q K => (S : Subgroup K)) hij
    simp only [F, Sylow.coe_ofCard] at h
    rw [Subgroup.subgroupOf_inj, inf_of_le_left (hPiK i), inf_of_le_left (hPiK j)] at h
    exact h
  have key : ∀ a b : ℕ, a < b → b < 7 → Pi a = Pi b → ∀ k ∈ Pi a, c * k * c⁻¹ ∈ Pi a := by
    intro a b hab hb he
    obtain ⟨d, rfl⟩ : ∃ d, b = a + d := ⟨b - a, by omega⟩
    have hd : ∀ k ∈ Pi a, c ^ d * k * (c ^ d)⁻¹ ∈ Pi a := by
      intro k hk
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hk
      rw [he]
      refine Subgroup.mem_map.2 ⟨z, hz, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, pow_add]
      group
    obtain ⟨e, he'⟩ := exists_inv_mod_seven d (by omega) (by omega)
    intro k hk
    have := conj_pow_mem hd e k hk
    rwa [← pow_mul, pow_eq_pow_mod _ hc, he', pow_one] at this
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h) : (i : ℕ) ≠ j) with h | h
  · exact ⟨Pi i, hPiK i, hPic i, key i j h j.2 hPij⟩
  · exact ⟨Pi j, hPiK j, hPic j, key j i h i.2 hPij.symm⟩

theorem coprime_card_core [Finite G] (H : Subgroup G) :
    Nat.Coprime (Nat.card (GLAPPrimeCoreOf 7 H)) 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [GLAPPrimeCoreOf, Subgroup.card_map_of_injective H.subtype_injective]
  exact (pPrimeCore_coprime_card (p := 7) (G := ↥H)).symm

theorem core_eq_bot_2058 [Finite G] {H : Subgroup G} {x u2 u3 : G} (hcard : Nat.card H = 2058)
    (hxH : x ∈ H) (hx : x ^ 7 = 1) (hx1 : x ≠ 1) (hu2H : u2 ∈ H) (hu2 : u2 ^ 2 = 1)
    (hu2x : u2 * x = x ^ 6 * u2) (hu3H : u3 ∈ H) (hu3 : u3 ^ 3 = 1)
    (hu3x : u3 * x = x ^ 4 * u3) : GLAPPrimeCoreOf 7 H = ⊥ := by
  set K := GLAPPrimeCoreOf 7 H with hKdef
  have hKH : K ≤ H := Subgroup.map_subtype_le _
  have hKn : (K.subgroupOf H).Normal := gLAPPrimeCoreOf_normal 7 H
  have hconj : ∀ g ∈ H, ∀ k ∈ K, g * k * g⁻¹ ∈ K := fun g hg k hk =>
    (Subgroup.normal_subgroupOf_iff hKH).1 hKn k g hk hg
  have hcop := coprime_card_core H
  have hdvd : Nat.card K ∣ 6 := by
    refine (Nat.Coprime.pow_right 3 hcop).dvd_of_dvd_mul_left ?_
    rw [show (7 : ℕ) ^ 3 * 6 = 2058 by norm_num, ← hcard]
    exact Subgroup.card_dvd_of_le hKH
  have hxK := commute_of_card_lt hx (hconj x hxH)
    (by have := Nat.le_of_dvd (by norm_num) hdvd; omega)
  have hno : ∀ m : ℕ, Nat.Coprime m 7 → x ^ m = 1 → False := fun m hm h =>
    hx1 (orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one h) hm)
      (orderOf_dvd_of_pow_eq_one hx)))
  have hidx := card_mul_index_subgroupOf hKH
  rw [hcard] at hidx
  have h2 : 2 ∣ Nat.card K → False := fun h2 => by
    have hu : u2 ∈ K := mem_of_coprime_index hKH hKn hu2H hu2 (by
      obtain ⟨t, ht⟩ := h2
      rw [ht] at hidx
      have h3 : t ≤ 3 := by
        have := Nat.le_of_dvd (by norm_num) hdvd
        omega
      interval_cases t <;>
        first
        | omega
        | (have : (K.subgroupOf H).index = 1029 := by omega
           rw [this]; decide)
        | (have : (K.subgroupOf H).index = 343 := by omega
           rw [this]; decide))
    have e : x * u2 = x ^ 6 * u2 := by rw [hxK u2 hu, hu2x]
    have e2 : x * 1 = x * x ^ 5 := by
      rw [mul_one, ← pow_succ']
      exact mul_right_cancel e
    exact hno 5 (by decide) (mul_left_cancel e2).symm
  have h3 : 3 ∣ Nat.card K → False := fun h3 => by
    have hu : u3 ∈ K := mem_of_coprime_index hKH hKn hu3H hu3 (by
      obtain ⟨t, ht⟩ := h3
      rw [ht] at hidx
      have h3 : t ≤ 2 := by
        have := Nat.le_of_dvd (by norm_num) hdvd
        omega
      interval_cases t <;>
        first
        | omega
        | (have : (K.subgroupOf H).index = 686 := by omega
           rw [this]; decide)
        | (have : (K.subgroupOf H).index = 343 := by omega
           rw [this]; decide))
    have e : x * u3 = x ^ 4 * u3 := by rw [hxK u3 hu, hu3x]
    have e2 : x * 1 = x * x ^ 3 := by
      rw [mul_one, ← pow_succ']
      exact mul_right_cancel e
    exact hno 3 (by decide) (mul_left_cancel e2).symm
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have hpos : 0 < Nat.card K := Nat.card_pos
  obtain ⟨d, hd⟩ : ∃ d, Nat.card K = d := ⟨_, rfl⟩
  rw [hd] at hle hpos hdvd h2 h3
  interval_cases d
  · exact Subgroup.eq_bot_of_card_eq K hd
  · exact (h2 (dvd_refl 2)).elim
  · exact (h3 (dvd_refl 3)).elim
  · exact absurd hdvd (by decide)
  · exact absurd hdvd (by decide)
  · exact (h2 (by norm_num)).elim

def reach (H : Subgroup G) (y c : G) (m k : ℕ) : Prop := ∃ g ∈ H, g * y * g⁻¹ = y ^ m * c ^ k

theorem pow_seven_of_mem_cent [Finite G] {x y c u2 u3 : G} (hy : y ^ 7 = 1) (hc : c ^ 7 = 1)
    (hcy : c * y = y * c)
    (hinj : ∀ j k j' k' : ℕ, j < 7 → k < 7 → j' < 7 → k' < 7 → y ^ j * c ^ k = y ^ j' * c ^ k' →
      j = j' ∧ k = k')
    (hcard : Nat.card (Subgroup.centralizer ({c} : Set G)) = 2058)
    (hxc : x * c = c * x) (hxy : x * y * x⁻¹ = y * c)
    (hu2c : u2 * c = c * u2) (hu2y : u2 * y * u2⁻¹ = y ^ 6 * c ^ 6)
    (hu3c : u3 * c = c * u3) (hu3y : u3 * y * u3⁻¹ = y ^ 2 * c ^ 4) :
    ∀ d : G, d * c = c * d → d * y = y * d → d ^ 7 = 1 := by
  set H := Subgroup.centralizer ({c} : Set G) with hH
  have memH : ∀ g : G, g * c = c * g → g ∈ H := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 hg
  have hconjform : ∀ g ∈ H, ∀ m k : ℕ, g * (y ^ m * c ^ k) * g⁻¹ = (g * y * g⁻¹) ^ m * c ^ k := by
    intro g hg m k
    have hgc : g * c * g⁻¹ = c := by
      rw [Subgroup.mem_centralizer_singleton_iff.1 hg]
      group
    have := map_mul (MulAut.conj g) (y ^ m) (c ^ k)
    simp only [map_pow, MulAut.conj_apply] at this
    rw [this, hgc]
  have step : ∀ h ∈ H, ∀ a b : ℕ, h * y * h⁻¹ = y ^ a * c ^ b → ∀ m k, reach H y c m k →
      reach H y c (a * m % 7) ((b * m + k) % 7) := by
    rintro h hh a b hab m k ⟨g, hg, hgy⟩
    refine ⟨h * g, H.mul_mem hh hg, ?_⟩
    have hcom : Commute (y ^ a) (c ^ b) := (show Commute c y from hcy).symm.pow_pow a b
    calc h * g * y * (h * g)⁻¹ = h * (g * y * g⁻¹) * h⁻¹ := by group
      _ = (y ^ a * c ^ b) ^ m * c ^ k := by rw [hgy, hconjform h hh, hab]
      _ = y ^ (a * m) * c ^ (b * m + k) := by
        rw [hcom.mul_pow, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
      _ = y ^ (a * m % 7) * c ^ ((b * m + k) % 7) := by
        rw [← pow_eq_pow_mod _ hy, ← pow_eq_pow_mod _ hc]
  have hxH := memH x hxc
  have hx1 : x * y * x⁻¹ = y ^ 1 * c ^ 1 := by rw [hxy, pow_one, pow_one]
  have hP10 : reach H y c 1 0 := ⟨1, H.one_mem, by simp⟩
  have hexists : ∀ m < 7, 0 < m → ∀ k0 < 7, ∀ k < 7, ∃ t < 7, (t * m + k0) % 7 = k := by
    decide +kernel
  have full : ∀ m k0, 0 < m → m < 7 → k0 < 7 → reach H y c m k0 → ∀ k < 7, reach H y c m k := by
    intro m k0 hm0 hm hk0 hP k hk
    have hit : ∀ t : ℕ, reach H y c m ((t * m + k0) % 7) := by
      intro t
      induction t with
      | zero => simpa [Nat.mod_eq_of_lt hk0] using hP
      | succ t ih =>
        have := step x hxH 1 1 hx1 m _ ih
        have e1 : 1 * m % 7 = m := by omega
        have e2 : (1 * m + (t * m + k0) % 7) % 7 = ((t + 1) * m + k0) % 7 := by
          simp only [add_mul, one_mul]
          generalize t * m = s
          omega
        rwa [e1, e2] at this
    obtain ⟨t, -, ht⟩ := hexists m hm hm0 k0 hk0 k hk
    rw [← ht]
    exact hit t
  have hu2H := memH u2 hu2c
  have hu3H := memH u3 hu3c
  have r1 := full 1 0 (by norm_num) (by norm_num) (by norm_num) hP10
  have r2 := full 2 4 (by norm_num) (by norm_num) (by norm_num) (step u3 hu3H 2 4 hu3y 1 0 hP10)
  have r4 := full 4 1 (by norm_num) (by norm_num) (by norm_num)
    (step u3 hu3H 2 4 hu3y 2 0 (r2 0 (by norm_num)))
  have r6 := full 6 6 (by norm_num) (by norm_num) (by norm_num) (step u2 hu2H 6 6 hu2y 1 0 hP10)
  have r5 := full 5 5 (by norm_num) (by norm_num) (by norm_num)
    (step u2 hu2H 6 6 hu2y 2 0 (r2 0 (by norm_num)))
  have r3 := full 3 3 (by norm_num) (by norm_num) (by norm_num)
    (step u2 hu2H 6 6 hu2y 4 0 (r4 0 (by norm_num)))
  have hall : ∀ m : Fin 6, ∀ k : Fin 7, ∃ g ∈ H, g * y * g⁻¹ = y ^ ((m : ℕ) + 1) * c ^ (k : ℕ) := by
    intro m k
    have hm := m.2
    obtain ⟨m, hm'⟩ := m
    change reach H y c (m + 1) k
    interval_cases m
    exacts [r1 k k.2, r2 k k.2, r3 k k.2, r4 k k.2, r5 k k.2, r6 k k.2]
  choose g hgH hgy using hall
  set D := H ⊓ Subgroup.centralizer ({y} : Set G) with hD
  have hdy : ∀ e ∈ D, e * y * e⁻¹ = y := fun e he => by
    rw [Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 he).2]
    group
  let F : Fin 6 × Fin 7 × D → H := fun p =>
    ⟨g p.1 p.2.1 * p.2.2, H.mul_mem (hgH _ _) (Subgroup.mem_inf.1 p.2.2.2).1⟩
  have hFinj : Function.Injective F := by
    rintro ⟨m, k, d⟩ ⟨m', k', d'⟩ he
    have he' : g m k * (d : G) = g m' k' * d' := congrArg Subtype.val he
    have hmem : (d' : G) * (d : G)⁻¹ ∈ D := D.mul_mem d'.2 (D.inv_mem d.2)
    have e2 : g m k = g m' k' * (d' * (d : G)⁻¹) := by
      rw [← mul_assoc, ← he']
      group
    have hconj : g m k * y * (g m k)⁻¹ = g m' k' * y * (g m' k')⁻¹ := by
      calc g m k * y * (g m k)⁻¹
          = g m' k' * ((d' * (d : G)⁻¹) * y * (d' * (d : G)⁻¹)⁻¹) * (g m' k')⁻¹ := by
            rw [e2]
            group
        _ = g m' k' * y * (g m' k')⁻¹ := by rw [hdy _ hmem]
    rw [hgy, hgy] at hconj
    obtain ⟨h1, h2⟩ := hinj _ _ _ _ (by omega) k.2 (by omega) k'.2 hconj
    have hm : m = m' := Fin.ext (by omega)
    have hk : k = k' := Fin.ext h2
    subst hm hk
    have : (d : G) = d' := mul_left_cancel he'
    rw [Subtype.ext this]
  have hDle : Nat.card D ≤ 49 := by
    have := Nat.card_le_card_of_injective F hFinj
    rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 6),
      Nat.card_eq_fintype_card (α := Fin 7), Fintype.card_fin, Fintype.card_fin, hcard] at this
    omega
  have hEmem : ∀ j k : ℕ, y ^ j * c ^ k ∈ D := fun j k => by
    have hyc : Commute y c := (show Commute c y from hcy).symm
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · exact ((hyc.pow_left j).mul_left (Commute.refl c |>.pow_left k)).eq
    · exact (((Commute.refl y).pow_left j).mul_left (hyc.symm.pow_left k)).eq
  let E : Fin 7 × Fin 7 → D := fun p => ⟨y ^ (p.1 : ℕ) * c ^ (p.2 : ℕ), hEmem _ _⟩
  have hEinj : Function.Injective E := by
    rintro ⟨j, k⟩ ⟨j', k'⟩ he
    obtain ⟨h1, h2⟩ := hinj _ _ _ _ j.2 k.2 j'.2 k'.2 (congrArg Subtype.val he)
    rw [Fin.ext h1, Fin.ext h2]
  have hEbij := hEinj.bijective_of_nat_card_le (by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 7), Fintype.card_fin]
    omega)
  intro d hdc hdy'
  obtain ⟨⟨j, k⟩, hjk⟩ := hEbij.2 ⟨d, Subgroup.mem_inf.2 ⟨memH d hdc,
    Subgroup.mem_centralizer_singleton_iff.2 hdy'⟩⟩
  have hd : y ^ (j : ℕ) * c ^ (k : ℕ) = d := congrArg Subtype.val hjk
  rw [← hd, ((show Commute c y from hcy).symm.pow_pow (j : ℕ) (k : ℕ)).mul_pow, ← pow_mul,
    ← pow_mul, mul_comm (j : ℕ) 7, mul_comm (k : ℕ) 7, pow_mul, pow_mul, hy, hc, one_pow, one_pow,
    one_mul]

theorem core_eq_bot_17640 [Finite G] {H : Subgroup G} {c u : G} (hcH : c ∈ H) (hc : c ^ 7 = 1)
    (hcard : Nat.card H = 17640)
    (hfix : ∀ k ∈ GLAPPrimeCoreOf 7 H, k * c = c * k → k = 1)
    (huH : u ∈ H) (hu4 : u ^ 4 = 1) (hu2 : u ^ 2 ≠ 1) : GLAPPrimeCoreOf 7 H = ⊥ := by
  set K := GLAPPrimeCoreOf 7 H with hKdef
  have hKH : K ≤ H := Subgroup.map_subtype_le _
  have hKn : (K.subgroupOf H).Normal := gLAPPrimeCoreOf_normal 7 H
  have hcK : ∀ k ∈ K, c * k * c⁻¹ ∈ K := fun k hk =>
    (Subgroup.normal_subgroupOf_iff hKH).1 hKn k c hk hcH
  have hcop := coprime_card_core H
  have hmod := card_mod_seven hc hcK hfix
  have hdvd : Nat.card K ∣ 360 := by
    refine (Nat.Coprime.pow_right 2 hcop).dvd_of_dvd_mul_left ?_
    rw [show (7 : ℕ) ^ 2 * 360 = 17640 by norm_num, ← hcard]
    exact Subgroup.card_dvd_of_le hKH
  have hcases : ∀ d < 361, d ∣ 360 → d % 7 = 1 →
      d = 1 ∨ d = 8 ∨ d = 15 ∨ d = 36 ∨ d = 120 := by decide +kernel
  have hidx := card_mul_index_subgroupOf hKH
  rw [hcard] at hidx
  rcases hcases _ (Nat.lt_succ_of_le (Nat.le_of_dvd (by norm_num) hdvd)) hdvd hmod with
    h | h | h | h | h
  · exact Subgroup.eq_bot_of_card_eq K h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    rw [h] at hidx
    have huK : u ∈ K := mem_of_coprime_index hKH hKn huH hu4 (by
      have : (K.subgroupOf H).index = 2205 := by omega
      rw [this]
      decide)
    have hu1 : u ≠ 1 := fun h1 => hu2 (by rw [h1, one_pow])
    let F : Option (Fin 7) → K := fun o => match o with
      | none => 1
      | some i => ⟨c ^ (i : ℕ) * u * (c ^ (i : ℕ))⁻¹, conj_pow_mem hcK i u huK⟩
    have hne1 : ∀ i : ℕ, c ^ i * u * (c ^ i)⁻¹ ≠ 1 := fun i h1 => hu1 (by
      calc u = (c ^ i)⁻¹ * (c ^ i * u * (c ^ i)⁻¹) * c ^ i := by group
        _ = 1 := by rw [h1]; group)
    have hFinj : Function.Injective F := by
      rintro (_ | i) (_ | j) hij
      · rfl
      · exact absurd (congrArg Subtype.val hij).symm (hne1 j)
      · exact absurd (congrArg Subtype.val hij) (hne1 i)
      · have hv : c ^ (i : ℕ) * u * (c ^ (i : ℕ))⁻¹ = c ^ (j : ℕ) * u * (c ^ (j : ℕ))⁻¹ :=
          congrArg Subtype.val hij
        by_contra hne
        have hne' : (i : ℕ) ≠ j := fun h => hne (by rw [Fin.ext h])
        have hcu : c * u = u * c := by
          rcases lt_or_gt_of_ne hne' with h | h
          · exact commute_of_conj_eq hc h j.2 hv
          · exact commute_of_conj_eq hc h i.2 hv.symm
        exact hu1 (hfix u huK hcu.symm)
    have hbij := hFinj.bijective_of_nat_card_le (by
      rw [h, Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin])
    obtain ⟨o, ho⟩ := hbij.2 ⟨u ^ 2, K.pow_mem huK 2⟩
    rcases o with _ | i
    · exact hu2 (congrArg Subtype.val ho).symm
    · have hv : c ^ (i : ℕ) * u * (c ^ (i : ℕ))⁻¹ = u ^ 2 := congrArg Subtype.val ho
      have ho1 : orderOf u = 2 ^ (1 + 1) :=
        orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hu2) (by simpa using hu4)
      have ho2 : orderOf (u ^ 2) = 2 :=
        orderOf_eq_prime (by rw [← pow_mul]; exact hu4) hu2
      have hoc : orderOf (c ^ (i : ℕ) * u * (c ^ (i : ℕ))⁻¹) = orderOf u := by
        exact orderOf_injective (MulAut.conj (c ^ (i : ℕ))).toMonoidHom
          (MulAut.conj (c ^ (i : ℕ))).injective u
      rw [hv, ho2, ho1] at hoc
      norm_num at hoc
  all_goals exfalso
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨P, hPK, hPc, hPinv⟩ := exists_conj_inv_sylow (q := 5) (a := 1) (m := 3) hc hcK
      (by rw [h]; norm_num) (by norm_num) (fun n hn _ => by have := Nat.le_of_dvd (by norm_num) hn; omega)
    have := card_mod_seven hc hPinv (fun k hk => hfix k (hPK hk))
    rw [hPc] at this
    norm_num at this
  · have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨P, hPK, hPc, hPinv⟩ := exists_conj_inv_sylow (q := 3) (a := 2) (m := 4) hc hcK
      (by rw [h]; norm_num) (by norm_num) (fun n hn _ => by have := Nat.le_of_dvd (by norm_num) hn; omega)
    have := card_mod_seven hc hPinv (fun k hk => hfix k (hPK hk))
    rw [hPc] at this
    norm_num at this
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨P, hPK, hPc, hPinv⟩ := exists_conj_inv_sylow (q := 5) (a := 1) (m := 24) hc hcK
      (by rw [h]; norm_num) (by norm_num) (fun n hn h5 => by
        have := Nat.le_of_dvd (by norm_num) hn
        interval_cases n <;> omega)
    have := card_mod_seven hc hPinv (fun k hk => hfix k (hPK hk))
    rw [hPc] at this
    norm_num at this

theorem core_y_of [Finite G] {x y c u4 u2 u3 : G} (hx7 : x ^ 7 = 1) (hy7 : y ^ 7 = 1)
    (hc : c = x * y * x ^ 6 * y ^ 6) (hcx : c * x = x * c) (hcy : c * y = y * c)
    (hinj : ∀ i j k i' j' k' : ℕ, i < 7 → j < 7 → k < 7 → i' < 7 → j' < 7 → k' < 7 →
      x ^ i * y ^ j * c ^ k = x ^ i' * y ^ j' * c ^ k' → i = i' ∧ j = j' ∧ k = k')
    (hcardc : Nat.card (Subgroup.centralizer ({c} : Set G)) = 2058)
    (hcardy : Nat.card (Subgroup.centralizer ({y} : Set G)) = 17640)
    (h4 : u4 ^ 4 = 1) (h4sq : u4 ^ 2 ≠ 1) (h4y : u4 * y = y * u4)
    (h2c : u2 * c = c * u2) (h2y : u2 * y = y ^ 6 * (c ^ 6 * u2))
    (h3c : u3 * c = c * u3) (h3y : u3 * y = y ^ 2 * (c ^ 4 * u3)) :
    GLAPPrimeCoreOf 7 (Subgroup.centralizer ({y} : Set G)) = ⊥ := by
  have hxinv : x ^ 6 = x⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hx7)
  have hyinv : y ^ 6 = y⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hy7)
  have hcxy : c * y = x * y * x⁻¹ := by
    rw [hc, hxinv, hyinv]
    group
  have hxy : x * y * x⁻¹ = y * c := by rw [← hcxy, hcy]
  have hxc : x * c = c * x := hcx.symm
  have hc7 : c ^ 7 = 1 := by
    have h1 : (x * y * x⁻¹) ^ 7 = 1 := by
      rw [conj_pow, hy7]
      group
    rw [hxy, (show Commute y c from hcy.symm).mul_pow, hy7, one_mul] at h1
    exact h1
  have hinj2 : ∀ j k j' k' : ℕ, j < 7 → k < 7 → j' < 7 → k' < 7 →
      y ^ j * c ^ k = y ^ j' * c ^ k' → j = j' ∧ k = k' :=
    fun j k j' k' hj hk hj' hk' h =>
      (hinj 0 j k 0 j' k' (by norm_num) hj hk (by norm_num) hj' hk' (by
        simp only [pow_zero, one_mul]
        exact h)).2
  have hu2y := conj_eq_of_mul_eq (h2y.trans (mul_assoc _ _ _).symm)
  have hu3y := conj_eq_of_mul_eq (h3y.trans (mul_assoc _ _ _).symm)
  have pow7 := pow_seven_of_mem_cent hy7 hc7 hcy hinj2 hcardc hxc hxy h2c hu2y h3c hu3y
  have hfix : ∀ k ∈ GLAPPrimeCoreOf 7 (Subgroup.centralizer ({y} : Set G)),
      k * c = c * k → k = 1 := by
    intro k hk hkc
    have hkH : k ∈ Subgroup.centralizer ({y} : Set G) := Subgroup.map_subtype_le _ hk
    have h7 := pow7 k hkc (Subgroup.mem_centralizer_singleton_iff.1 hkH)
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard _ hk) (coprime_card_core _))
      (orderOf_dvd_of_pow_eq_one h7))
  exact core_eq_bot_17640 (Subgroup.mem_centralizer_singleton_iff.2 hcy) hc7 hcardy hfix
    (Subgroup.mem_centralizer_singleton_iff.2 h4y) h4 h4sq

end Generic

section J

open CFSG.Sporadic.Fi24 (J)
open CFSG.KD.Fi24Sev.SevenB (sev)
open CFSG.KD.Fi24ThreeO.Group (Bridge)


theorem finite_J : Finite J :=
  Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)

theorem core_c (hB : Bridge)
    (hinj : ∀ i j k i' j' k' : ℕ, i < 7 → j < 7 → k < 7 → i' < 7 → j' < 7 → k' < 7 →
      sev 64 ^ i * sev 66 ^ j * sev 67 ^ k = sev 64 ^ i' * sev 66 ^ j' * sev 67 ^ k' →
      i = i' ∧ j = j' ∧ k = k') :
    GLAPPrimeCoreOf 7 (Subgroup.centralizer ({sev 67} : Set J)) = ⊥ := by
  have := finite_J
  obtain ⟨hx7, -, -, hcx, -, -⟩ := CFSG.KD.Fi24Sev.SevenB.cube_facts hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h2sq, -, h2c, h2x, -, h3cu, -, h3c, h3x, -⟩ :=
    CFSG.KD.Fi24Sev.SevenB.elt_facts hB
  have hx1 : sev 64 ≠ 1 := fun h => by
    have := hinj 1 0 0 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by simp [h])
    exact absurd this.1 (by norm_num)
  exact core_eq_bot_2058 (CFSG.KD.Fi24Sev.Seven.card_centralizer_c hB)
    (Subgroup.mem_centralizer_singleton_iff.2 hcx.symm) hx7 hx1
    (Subgroup.mem_centralizer_singleton_iff.2 h2c) h2sq h2x
    (Subgroup.mem_centralizer_singleton_iff.2 h3c) h3cu h3x

theorem core_y (hB : Bridge)
    (hinj : ∀ i j k i' j' k' : ℕ, i < 7 → j < 7 → k < 7 → i' < 7 → j' < 7 → k' < 7 →
      sev 64 ^ i * sev 66 ^ j * sev 67 ^ k = sev 64 ^ i' * sev 66 ^ j' * sev 67 ^ k' →
      i = i' ∧ j = j' ∧ k = k') :
    GLAPPrimeCoreOf 7 (Subgroup.centralizer ({sev 66} : Set J)) = ⊥ := by
  have := finite_J
  obtain ⟨hx7, hy7, hc, hcx, hcy, -⟩ := CFSG.KD.Fi24Sev.SevenB.cube_facts hB
  obtain ⟨-, -, -, -, -, -, -, -, -, h4, h4sq, h4y, -, -, h2c, -, h2y, -, -, h3c, -, h3y⟩ :=
    CFSG.KD.Fi24Sev.SevenB.elt_facts hB
  exact core_y_of hx7 hy7 hc hcx hcy hinj (CFSG.KD.Fi24Sev.Seven.card_centralizer_c hB)
    (CFSG.KD.Fi24Sev.Seven.card_centralizer_y hB) h4 h4sq h4y h2c h2y h3c h3y

end J

end CFSG.KD.Fi24Sev.Core

end
