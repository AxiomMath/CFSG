module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Cover
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.U43ConfigSig

public section

namespace CertificateChecks.KernelHSStd.U43I4

open Subgroup CFSG.EvenSporadicStandard.HSStd.U43 CFSG.EvenSporadicStandard.M24Std.CU43

section General

variable {Γ : Type*} [Group Γ]

theorem card_sup_mul_card_inf [Finite Γ] {A B : Subgroup Γ}
    (h : A ≤ Subgroup.normalizer (B : Set Γ)) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  set N := Subgroup.normalizer (B : Set Γ) with hN
  have hB : B ≤ N := Subgroup.le_normalizer
  have hAB : A ⊔ B ≤ N := sup_le h hB
  have h1 := Subgroup.relIndex_sup_right (H := A.subgroupOf N) (K := B.subgroupOf N)
  have h2 := Subgroup.relIndex_mul_card (H := B.subgroupOf N)
    (K := A.subgroupOf N ⊔ B.subgroupOf N)
  have h3 := Subgroup.relIndex_mul_card (H := B.subgroupOf N) (K := A.subgroupOf N)
  rw [inf_eq_left.2 le_sup_right, h1] at h2
  have eA : Nat.card ↥(A.subgroupOf N) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  have eB : Nat.card ↥(B.subgroupOf N) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv
  have eAB : Nat.card ↥(A.subgroupOf N ⊔ B.subgroupOf N) = Nat.card ↥(A ⊔ B) := by
    rw [← Subgroup.subgroupOf_sup h hB]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv
  have eI : Nat.card ↥(B.subgroupOf N ⊓ A.subgroupOf N) = Nat.card ↥(A ⊓ B) := by
    have : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      exact and_comm
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans h)).toEquiv
  rw [eAB, eB] at h2
  rw [eI, eA] at h3
  rw [← h2, ← h3]
  ring

theorem pow_mod_three {u : Γ} (hu : u ^ 3 = 1) (a : ℕ) : u ^ a = u ^ (a % 3) := by
  conv_lhs => rw [← Nat.mod_add_div a 3, pow_add, pow_mul, hu, one_pow, mul_one]

theorem pair_mul {u v : Γ} (huv : Commute u v) (a b c d : ℕ) :
    u ^ a * v ^ b * (u ^ c * v ^ d) = u ^ (a + c) * v ^ (b + d) := by
  have h1 : Commute (v ^ b) (u ^ c) := huv.symm.pow_pow b c
  calc u ^ a * v ^ b * (u ^ c * v ^ d) = u ^ a * (v ^ b * u ^ c) * v ^ d := by group
    _ = u ^ a * (u ^ c * v ^ b) * v ^ d := by rw [h1.eq]
    _ = u ^ (a + c) * v ^ (b + d) := by rw [pow_add, pow_add]; group

theorem mem_closure_pair {u v : Γ} (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) (huv : Commute u v) {x : Γ}
    (hx : x ∈ closure ({u, v} : Set Γ)) : ∃ a < 3, ∃ b < 3, x = u ^ a * v ^ b := by
  let K : Subgroup Γ :=
    { carrier := {x | ∃ i j : ℕ, x = u ^ i * v ^ j}
      one_mem' := ⟨0, 0, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
        exact ⟨i + i', j + j', pair_mul huv i j i' j'⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨2 * i, 2 * j, ?_⟩
        have hui : (u ^ i)⁻¹ = u ^ (2 * i) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add, show i + 2 * i = 3 * i by ring, pow_mul, hu,
            one_pow]
        have hvj : (v ^ j)⁻¹ = v ^ (2 * j) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_add, show j + 2 * j = 3 * j by ring, pow_mul, hv,
            one_pow]
        rw [mul_inv_rev, hui, hvj]
        exact (Commute.pow_pow (huv.symm) (2 * j) (2 * i)).eq }
  have hle : closure ({u, v} : Set Γ) ≤ K := by
    rw [closure_le]
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨1, 0, by simp⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨0, 1, by simp [hx]⟩
  obtain ⟨i, j, rfl⟩ := hle hx
  exact ⟨i % 3, Nat.mod_lt _ (by norm_num), j % 3, Nat.mod_lt _ (by norm_num), by
    rw [← pow_mod_three hu, ← pow_mod_three hv]⟩

theorem card_sylow3 [Finite Γ] (hΓ : Nat.card Γ = 2880) (Q : Sylow 3 Γ) :
    Nat.card ↥(Q : Subgroup Γ) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Sylow.card_eq_multiplicity, hΓ, Nat.factorization_def _ Nat.prime_three,
    show (2880 : ℕ) = 3 ^ 2 * 320 by norm_num,
    padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem conj_of_sylow [Finite Γ] (hΓ : Nat.card Γ = 2880) {s₁ s₂ y₀ : Γ} (h₁ : s₁ ^ 3 = 1)
    (h₂ : s₂ ^ 3 = 1) (h₁₂ : Commute s₁ s₂) (hy₀ : y₀ ≠ 1)
    (hh : ∀ a < 3, ∀ b < 3, a ≠ 0 ∨ b ≠ 0 → ∃ h : Γ, h * y₀ * h⁻¹ = s₁ ^ a * s₂ ^ b)
    {y : Γ} (hy : orderOf y = 3) : ∃ g : Γ, y = g * y₀ * g⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set S := closure ({s₁, s₂} : Set Γ) with hS
  have hne : ∀ a < 3, ∀ b < 3, a ≠ 0 ∨ b ≠ 0 → s₁ ^ a * s₂ ^ b ≠ 1 := by
    intro a ha b hb hab h1
    obtain ⟨h, hh'⟩ := hh a ha b hb hab
    rw [h1] at hh'
    have e : y₀ = h⁻¹ * (h * y₀ * h⁻¹) * h := by group
    rw [hh'] at e
    exact hy₀ (by simpa using e)
  have hinj : ∀ a < 3, ∀ b < 3, ∀ c < 3, ∀ d < 3, s₁ ^ a * s₂ ^ b = s₁ ^ c * s₂ ^ d →
      a = c ∧ b = d := by
    intro a ha b hb c hc d hd he
    have h3 : (s₁ ^ c * s₂ ^ d) * (s₁ ^ c * s₂ ^ d) * (s₁ ^ c * s₂ ^ d) = 1 := by
      rw [pair_mul h₁₂, pair_mul h₁₂, pow_mod_three h₁, pow_mod_three h₂ (d + d + d)]
      have e1 : (c + c + c) % 3 = 0 := by omega
      have e2 : (d + d + d) % 3 = 0 := by omega
      rw [e1, e2]
      simp
    have h4 : s₁ ^ ((a + 2 * c) % 3) * s₂ ^ ((b + 2 * d) % 3) = 1 := by
      calc s₁ ^ ((a + 2 * c) % 3) * s₂ ^ ((b + 2 * d) % 3) = s₁ ^ (a + 2 * c) * s₂ ^ (b + 2 * d) := by
            rw [← pow_mod_three h₁, ← pow_mod_three h₂]
        _ = (s₁ ^ a * s₂ ^ b) * (s₁ ^ c * s₂ ^ d) * (s₁ ^ c * s₂ ^ d) := by
            rw [pair_mul h₁₂, pair_mul h₁₂, show a + c + c = a + 2 * c by ring,
              show b + d + d = b + 2 * d by ring]
        _ = (s₁ ^ c * s₂ ^ d) * (s₁ ^ c * s₂ ^ d) * (s₁ ^ c * s₂ ^ d) := by rw [he]
        _ = 1 := h3
    by_contra hcon
    refine hne _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num)) ?_ h4
    omega
  have hle9 : Nat.card ↥S ≤ 9 := card_closure_pair_le_nine h₁ h₂ h₁₂
  have hge9 : 9 ≤ Nat.card ↥S := by
    have hmem : ∀ a b : ℕ, s₁ ^ a * s₂ ^ b ∈ S := fun a b =>
      S.mul_mem (S.pow_mem (subset_closure (by simp)) a) (S.pow_mem (subset_closure (by simp)) b)
    let f : Fin 3 × Fin 3 → ↥S := fun p => ⟨s₁ ^ (p.1 : ℕ) * s₂ ^ (p.2 : ℕ), hmem _ _⟩
    have hf : Function.Injective f := by
      rintro ⟨a, b⟩ ⟨c, d⟩ he
      have he' : s₁ ^ (a : ℕ) * s₂ ^ (b : ℕ) = s₁ ^ (c : ℕ) * s₂ ^ (d : ℕ) := congrArg Subtype.val he
      obtain ⟨e1, e2⟩ := hinj a a.2 b b.2 c c.2 d d.2 he'
      exact Prod.ext (Fin.ext e1) (Fin.ext e2)
    have := Nat.card_le_card_of_injective f hf
    simpa [Nat.card_eq_fintype_card] using this
  have hS9 : Nat.card ↥S = 9 := le_antisymm hle9 hge9
  have hSp : IsPGroup 3 S := IsPGroup.of_card (n := 2) (by rw [hS9]; norm_num)
  obtain ⟨Q', hQ'⟩ := hSp.exists_le_sylow
  have hQ'S : (Q' : Subgroup Γ) = S :=
    (Subgroup.eq_of_le_of_card_ge hQ' (by rw [card_sylow3 hΓ, hS9])).symm
  have hyp : IsPGroup 3 (zpowers y) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy]; rfl)
  obtain ⟨Q, hQ⟩ := hyp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ Q Q'
  have hyQ : y ∈ (Q : Subgroup Γ) := hQ (mem_zpowers y)
  have hmem : g * y * g⁻¹ ∈ S := by
    rw [← hQ'S, ← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ← map_inv, MulAut.smul_def, MulAut.conj_apply]
    simpa [mul_assoc] using hyQ
  obtain ⟨a, ha, b, hb, hab⟩ := mem_closure_pair h₁ h₂ h₁₂ hmem
  have hab0 : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    rw [hcon.1, hcon.2, pow_zero, pow_zero, mul_one] at hab
    have e : y = g⁻¹ * (g * y * g⁻¹) * g := by group
    rw [hab] at e
    have hy1 : y = 1 := by simpa using e
    rw [hy1, orderOf_one] at hy
    exact absurd hy (by norm_num)
  obtain ⟨h, hh'⟩ := hh a ha b hb hab0
  refine ⟨g⁻¹ * h, ?_⟩
  have : g * y * g⁻¹ = h * y₀ * h⁻¹ := hab.trans hh'.symm
  calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
    _ = g⁻¹ * (h * y₀ * h⁻¹) * g := by rw [this]
    _ = g⁻¹ * h * y₀ * (g⁻¹ * h)⁻¹ := by group

theorem eq_range_of_injOn [Finite Γ] {H : Subgroup Γ} {N : ℕ} {f : ℕ → Γ}
    (hf : ∀ i < N, f i ∈ H) (hinj : ∀ i < N, ∀ j < N, f i = f j → i = j)
    (hH : Nat.card ↥H ≤ N) : ∀ x ∈ H, ∃ i < N, x = f i := by
  classical
  set s : Finset Γ := (Finset.range N).image f with hs
  have hcard : s.card = N := by
    rw [hs, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj he
    exact hinj i (Finset.mem_range.1 hi) j (Finset.mem_range.1 hj) he
  have hsub : (s : Set Γ) ⊆ (H : Set Γ) := by
    intro x hx
    rw [Finset.mem_coe, hs, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact hf i (Finset.mem_range.1 hi)
  have heq : (s : Set Γ) = (H : Set Γ) := Set.eq_of_subset_of_ncard_le hsub (by
    rw [Set.ncard_coe_finset, hcard, ← Nat.card_coe_set_eq]
    exact hH) (Set.toFinite _)
  intro x hx
  have hx' : x ∈ (s : Set Γ) := by rw [heq]; exact hx
  rw [Finset.mem_coe, hs, Finset.mem_image] at hx'
  obtain ⟨i, hi, rfl⟩ := hx'
  exact ⟨i, Finset.mem_range.1 hi, rfl⟩

end General

section Model

theorem R_le_normalizer_P : R ≤ normalizer (P : Set (Equiv.Perm (Fin 820))) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro p
  constructor
  · exact fun hp => conj_mem_P hx hp
  · intro hp
    have := conj_mem_P (R.inv_mem hx) hp
    simpa [mul_assoc] using this

theorem inf_centralizer_inf_P (S : Set (Equiv.Perm (Fin 820))) :
    R ⊓ centralizer S ⊓ P = P ⊓ centralizer S := by
  ext z
  simp only [mem_inf]
  constructor
  · rintro ⟨⟨-, h⟩, hp⟩
    exact ⟨hp, h⟩
  · rintro ⟨hp, h⟩
    exact ⟨⟨P_le_R hp, h⟩, hp⟩

theorem card_R_cent_le (x : Equiv.Perm (Fin 820)) :
    Nat.card ↥(R ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 820)))) ≤
      8 * Nat.card ↥(P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 820)))) := by
  have hA : R ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 820))) ≤
      normalizer (P : Set (Equiv.Perm (Fin 820))) := inf_le_left.trans R_le_normalizer_P
  have h := card_sup_mul_card_inf hA
  rw [inf_centralizer_inf_P] at h
  have hle := Subgroup.card_le_of_le (sup_le (inf_le_left (b := centralizer
    ({x} : Set (Equiv.Perm (Fin 820))))) P_le_R)
  rw [card_R] at hle
  have hP : 0 < Nat.card P := Nat.card_pos
  refine Nat.le_of_mul_le_mul_right ?_ hP
  calc Nat.card ↥(R ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 820)))) * Nat.card P
      = Nat.card ↥(R ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 820))) ⊔ P) *
        Nat.card ↥(P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 820)))) := h.symm
    _ ≤ (8 * Nat.card P) * Nat.card ↥(P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 820)))) :=
        Nat.mul_le_mul_right _ hle
    _ = 8 * Nat.card ↥(P ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 820)))) * Nat.card P := by
        ring

theorem coset_eq_of_conj {k k' : ℕ} (hk : k < 8) (hk' : k' < 8) {x p : Equiv.Perm (Fin 820)}
    (hx : x ∈ InvCoset k) (hp : p ∈ P) (hx' : p * x * p⁻¹ ∈ InvCoset k') : k = k' := by
  obtain ⟨g, hg, rfl, -⟩ := hx
  obtain ⟨g', hg', he, -⟩ := hx'
  by_contra hne
  apply tP_mul_inv_not_mem hk' hk (Ne.symm hne)
  have e : tP k' * (tP k)⁻¹ = g'⁻¹ * (p * g) * (tP k * p⁻¹ * (tP k)⁻¹) := by
    calc tP k' * (tP k)⁻¹ = g'⁻¹ * (g' * tP k') * (tP k)⁻¹ := by group
      _ = g'⁻¹ * (p * (g * tP k) * p⁻¹) * (tP k)⁻¹ := by rw [← he]
      _ = g'⁻¹ * (p * g) * (tP k * p⁻¹ * (tP k)⁻¹) := by group
  rw [e]
  exact P.mul_mem (P.mul_mem (P.inv_mem hg') (P.mul_mem hp hg)) (tP_normalizes (P.inv_mem hp))

theorem card_cent_rP4_le {u : Equiv.Perm (Fin 820)} (hu : u ∈ R)
    (h5 : rP 5 = u * rP 4 * u⁻¹) :
    Nat.card ↥(R ⊓ centralizer ({rP 4} : Set (Equiv.Perm (Fin 820)))) ≤ 2880 := by
  set C := R ⊓ centralizer ({rP 4} : Set (Equiv.Perm (Fin 820))) with hCdef
  by_contra hlt
  rw [not_le] at hlt
  have hA : C ≤ normalizer (P : Set (Equiv.Perm (Fin 820))) := inf_le_left.trans R_le_normalizer_P
  have h := card_sup_mul_card_inf hA
  rw [hCdef, inf_centralizer_inf_P, card_inf_centralizer_rP (j := 4) (by norm_num), card_P,
    show repCent[4]! = 720 by decide] at h
  have hHR : C ⊔ P ≤ R := sup_le inf_le_left P_le_R
  obtain ⟨a, ha⟩ := Subgroup.card_dvd_of_le (le_sup_right : P ≤ C ⊔ P)
  obtain ⟨b, hb⟩ := Subgroup.card_dvd_of_le hHR
  rw [card_P] at ha
  rw [card_R, card_P, ha, mul_assoc] at hb
  rw [← hCdef, ha] at h
  have hab : a * b = 8 := by omega
  have ha4 : 4 < a := by nlinarith
  have ha8 : a ≤ 8 := by
    rcases Nat.eq_zero_or_pos b with hb0 | hb0
    · rw [hb0, mul_zero] at hab
      omega
    · nlinarith
  have hb1 : b = 1 := by interval_cases a <;> omega
  rw [hb1, mul_one] at hab
  have hHeq : C ⊔ P = R := Subgroup.eq_of_le_of_card_ge hHR (by
    rw [card_R, card_P, ha, hab])
  have huP : u ∈ P ⊔ C := by
    rw [sup_comm, hHeq]
    exact hu
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left P C hA
  rw [← SetLike.mem_coe, hmul] at huP
  obtain ⟨p, hp, x, hx, rfl⟩ := Set.mem_mul.1 huP
  have hxT : x * rP 4 = rP 4 * x := mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2
  have h5' : rP 5 = p * rP 4 * p⁻¹ := by
    rw [h5]
    calc p * x * rP 4 * (p * x)⁻¹ = p * (x * rP 4) * x⁻¹ * p⁻¹ := by group
      _ = p * (rP 4 * x) * x⁻¹ * p⁻¹ := by rw [hxT]
      _ = p * rP 4 * p⁻¹ := by group
  have h4 := rP_mem_InvCoset (j := 4) (by norm_num)
  have h5c := rP_mem_InvCoset (j := 5) (by norm_num)
  rw [show repCoset[4]! = 7 by decide] at h4
  rw [show repCoset[5]! = 5 by decide, h5'] at h5c
  have := coset_eq_of_conj (by norm_num) (by norm_num) h4 hp h5c
  omega

theorem false_of_facts {u : Equiv.Perm (Fin 820)} (hu : u ∈ R)
    (h5 : rP 5 = u * rP 4 * u⁻¹)
    (hC : 2880 ≤ Nat.card ↥(R ⊓ centralizer ({rP 4} : Set (Equiv.Perm (Fin 820)))))
    {s₁ s₂ y₀ : Equiv.Perm (Fin 820)}
    (hs₁ : s₁ ∈ R ⊓ centralizer ({rP 4} : Set (Equiv.Perm (Fin 820))))
    (hs₂ : s₂ ∈ R ⊓ centralizer ({rP 4} : Set (Equiv.Perm (Fin 820))))
    (h₁ : s₁ ^ 3 = 1) (h₂ : s₂ ^ 3 = 1) (h₁₂ : s₁ * s₂ = s₂ * s₁) (hy₀ : y₀ ≠ 1)
    (hh : ∀ a < 3, ∀ b < 3, a ≠ 0 ∨ b ≠ 0 →
      ∃ h ∈ R ⊓ centralizer ({rP 4} : Set (Equiv.Perm (Fin 820))), h * y₀ * h⁻¹ = s₁ ^ a * s₂ ^ b)
    {h₀ : Equiv.Perm (Fin 820)} (hh₀ : h₀ ∈ P)
    (hub : Nat.card ↥(P ⊓ centralizer ({h₀ * y₀ * h₀⁻¹} : Set (Equiv.Perm (Fin 820)))) ≤ 81)
    {Y : ℕ → Equiv.Perm (Fin 820)}
    (hY : ∀ i < 648, Y i ∈ R ⊓ centralizer ({y₀} : Set (Equiv.Perm (Fin 820))))
    (hYinj : ∀ i < 648, ∀ j < 648, Y i = Y j → i = j)
    (hsol : ∀ i < 648, ∀ j < 648, ¬ SigRel (rP 4) y₀ (Y i) (Y j))
    {y c k : Equiv.Perm (Fin 820)} (hs : SigRel (rP 4) y c k) (hy : y ∈ R) (hc : c ∈ R)
    (hk : k ∈ R) : False := by
  set C := R ⊓ centralizer ({rP 4} : Set (Equiv.Perm (Fin 820))) with hCdef
  have hCc : Nat.card ↥C = 2880 := le_antisymm (card_cent_rP4_le hu h5) hC
  obtain ⟨h1, hh1C, hh1⟩ := hh 1 (by norm_num) 0 (by norm_num) (Or.inl one_ne_zero)
  have hy₀C : y₀ ∈ C := by
    have e : y₀ = h1⁻¹ * (s₁ ^ 1 * s₂ ^ 0) * h1 := by rw [← hh1]; group
    rw [e]
    exact C.mul_mem (C.mul_mem (C.inv_mem hh1C) (C.mul_mem (C.pow_mem hs₁ 1) (C.pow_mem hs₂ 0)))
      hh1C
  have hyC : y ∈ C := mem_inf.2 ⟨hy, mem_centralizer_singleton_iff.2 hs.comm_Ty.symm⟩
  obtain ⟨g, hg⟩ := conj_of_sylow (Γ := ↥C) hCc (s₁ := ⟨s₁, hs₁⟩) (s₂ := ⟨s₂, hs₂⟩)
    (y₀ := ⟨y₀, hy₀C⟩) (Subtype.ext (by simpa using h₁)) (Subtype.ext (by simpa using h₂))
    (Subtype.ext (by simpa using h₁₂)) (fun h => hy₀ (congrArg Subtype.val h))
    (fun a ha b hb hab => by
      obtain ⟨h, hhC, hh'⟩ := hh a ha b hb hab
      exact ⟨⟨h, hhC⟩, Subtype.ext (by simpa using hh')⟩)
    (y := ⟨y, hyC⟩) ((Subgroup.orderOf_coe (⟨y, hyC⟩ : ↥C)).symm.trans hs.y3)
  have hgy : y = (g : Equiv.Perm (Fin 820)) * y₀ * (g : Equiv.Perm (Fin 820))⁻¹ := by
    simpa using congrArg Subtype.val hg
  have hgT : (g : Equiv.Perm (Fin 820)) * rP 4 = rP 4 * g :=
    mem_centralizer_singleton_iff.1 (mem_inf.1 g.2).2
  have hgR : (g : Equiv.Perm (Fin 820)) ∈ R := (mem_inf.1 g.2).1
  have hs' := hs.conj (g : Equiv.Perm (Fin 820))⁻¹
  have eT : (g : Equiv.Perm (Fin 820))⁻¹ * rP 4 * (g : Equiv.Perm (Fin 820))⁻¹⁻¹ = rP 4 := by
    rw [inv_inv, mul_assoc, ← hgT]
    group
  have ey : (g : Equiv.Perm (Fin 820))⁻¹ * y * (g : Equiv.Perm (Fin 820))⁻¹⁻¹ = y₀ := by
    rw [hgy]
    group
  rw [eT, ey] at hs'
  set c' := (g : Equiv.Perm (Fin 820))⁻¹ * c * (g : Equiv.Perm (Fin 820))⁻¹⁻¹
  set k' := (g : Equiv.Perm (Fin 820))⁻¹ * k * (g : Equiv.Perm (Fin 820))⁻¹⁻¹
  have hc'R : c' ∈ R := R.mul_mem (R.mul_mem (R.inv_mem hgR) hc) (R.inv_mem (R.inv_mem hgR))
  have hk'R : k' ∈ R := R.mul_mem (R.mul_mem (R.inv_mem hgR) hk) (R.inv_mem (R.inv_mem hgR))
  set D := R ⊓ centralizer ({y₀} : Set (Equiv.Perm (Fin 820))) with hDdef
  have hD : Nat.card ↥D ≤ 648 := by
    have h2 := card_inf_centralizer_conj_set P hh₀ ({y₀} : Set (Equiv.Perm (Fin 820)))
    rw [Set.image_singleton] at h2
    calc Nat.card ↥D ≤ 8 * Nat.card ↥(P ⊓ centralizer ({y₀} : Set (Equiv.Perm (Fin 820)))) :=
          card_R_cent_le y₀
      _ = 8 * Nat.card ↥(P ⊓ centralizer ({h₀ * y₀ * h₀⁻¹} : Set (Equiv.Perm (Fin 820)))) := by
          rw [h2]
      _ ≤ 8 * 81 := Nat.mul_le_mul_left 8 hub
  have hc'D : c' ∈ D := mem_inf.2 ⟨hc'R, mem_centralizer_singleton_iff.2 hs'.yc.symm⟩
  have hk'D : k' ∈ D := mem_inf.2 ⟨hk'R, mem_centralizer_singleton_iff.2 hs'.yk.symm⟩
  obtain ⟨i, hi, hci⟩ := eq_range_of_injOn hY hYinj hD c' hc'D
  obtain ⟨j, hj, hkj⟩ := eq_range_of_injOn hY hYinj hD k' hk'D
  rw [hci, hkj] at hs'
  exact hsol i hi j hj hs'

theorem false_rP5_of_rP4 {u : Equiv.Perm (Fin 820)} (hu : u ∈ R) (h5 : rP 5 = u * rP 4 * u⁻¹)
    (h4 : ∀ {y c k : Equiv.Perm (Fin 820)}, SigRel (rP 4) y c k → y ∈ R → c ∈ R → k ∈ R → False)
    {y c k : Equiv.Perm (Fin 820)} (hs : SigRel (rP 5) y c k) (hy : y ∈ R) (hc : c ∈ R)
    (hk : k ∈ R) : False := by
  have hs' := hs.conj u⁻¹
  have e : u⁻¹ * rP 5 * u⁻¹⁻¹ = rP 4 := by
    rw [h5]
    group
  rw [e] at hs'
  have hui : u⁻¹⁻¹ ∈ R := R.inv_mem (R.inv_mem hu)
  exact h4 hs' (R.mul_mem (R.mul_mem (R.inv_mem hu) hy) hui)
    (R.mul_mem (R.mul_mem (R.inv_mem hu) hc) hui) (R.mul_mem (R.mul_mem (R.inv_mem hu) hk) hui)

end Model

end CertificateChecks.KernelHSStd.U43I4
