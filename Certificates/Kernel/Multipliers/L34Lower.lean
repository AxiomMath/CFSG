module

public import CFSG.Certificates.Kernel.Multipliers.MonoSound
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Rels
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Data.P3
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Data.F4a
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Data.F4b
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Checks.P3
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Checks.F4a
public import CFSG.Certificates.Kernel.Bounds.L34Alt.Checks.F4b
public import CFSG.LieType.Multipliers.L34Data
public import CFSG.Certificates.CosetTableOrders
import CFSG.LieType.Multipliers.CoverWords
import CFSG.Certificates.PresentationLetters
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Certificates.CosetTableShort
public import CFSG.Open.Defs
public import Mathlib.Algebra.Group.MinimalAxioms
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree

public section

namespace CertificateChecks.KernelL34

open CFSG.KC CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
  CFSG.Certificates.CosetEnumeration

abbrev cw : List (List (Fin 2 × Bool)) := coverWords rels fun i => commWords (coverPairs i)

theorem relCodes_eq : codes rels = CFSG.KC.L34Alt.relCodes := by decide +kernel

theorem coverCodes_eq :
    codes ((List.finRange 2).map fun i => (i, false) :: commWords (coverPairs i)) =
      CFSG.KC.L34Alt.coverCodes := by decide +kernel

theorem points_of_slices {p : ℕ → Bool} {s P : ℕ} (h : ∀ k < s, Mono.allR (k * P) P p = true) :
    ∀ x < s * P, p x = true := by
  intro x hx
  have hP : 0 < P := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hx
  have hk : x / P < s := (Nat.div_lt_iff_lt_mul hP).mpr hx
  exact CFSG.Certificates.Mono.allR_spec (h _ hk) x (Nat.div_mul_le_self x P)
    (Nat.lt_div_mul_add hP)

theorem pointsP3 : ∀ x < 21, Mono.pointOK CFSG.KD.L34P3.Tab 2 21 3 CFSG.KD.L34P3.Cst
    CFSG.KC.L34Alt.relCodes CFSG.KC.L34Alt.coverCodes x = true :=
  fun x hx => CFSG.Certificates.Mono.allR_spec CFSG.KD.L34P3.sP0 x (Nat.zero_le _) hx

theorem pointsF4a : ∀ x < 960, Mono.pointOK CFSG.KD.L34F4a.Tab 2 960 4 CFSG.KD.L34F4a.Cst
    CFSG.KC.L34Alt.relCodes CFSG.KC.L34Alt.coverCodes x = true :=
  points_of_slices (s := 8) (P := 120) fun k hk => by
    interval_cases k
    exacts [CFSG.KD.L34F4a.sP0, CFSG.KD.L34F4a.sP1, CFSG.KD.L34F4a.sP2, CFSG.KD.L34F4a.sP3,
      CFSG.KD.L34F4a.sP4, CFSG.KD.L34F4a.sP5, CFSG.KD.L34F4a.sP6, CFSG.KD.L34F4a.sP7]

theorem pointsF4b : ∀ x < 960, Mono.pointOK CFSG.KD.L34F4b.Tab 2 960 4 CFSG.KD.L34F4b.Cst
    CFSG.KC.L34Alt.relCodes CFSG.KC.L34Alt.coverCodes x = true :=
  points_of_slices (s := 8) (P := 120) fun k hk => by
    interval_cases k
    exacts [CFSG.KD.L34F4b.sP0, CFSG.KD.L34F4b.sP1, CFSG.KD.L34F4b.sP2, CFSG.KD.L34F4b.sP3,
      CFSG.KD.L34F4b.sP4, CFSG.KD.L34F4b.sP5, CFSG.KD.L34F4b.sP6, CFSG.KD.L34F4b.sP7]

theorem rels_length : rels.length = 7 := by decide +kernel

theorem descend {E : Type} [Group E] (ψ : PG 2 cw →* E)
    (hx : ∀ r ∈ extraWs, ψ (PresentedGroup.mk _ (FreeGroup.mk r)) = 1) :
    ∃ φ : PG 2 coverWs →* E, ∀ w : List (Fin 2 × Bool),
      φ (PresentedGroup.mk _ (FreeGroup.mk w)) = ψ (PresentedGroup.mk _ (FreeGroup.mk w)) := by
  let f : Fin 2 → E := fun i => ψ (PresentedGroup.of i)
  have key : FreeGroup.lift f = ψ.comp (PresentedGroup.mk _) :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  have h : ∀ r ∈ {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk}, FreeGroup.lift f r = 1 := by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    rw [key, MonoidHom.comp_apply]
    rcases List.mem_append.mp hw with hw | hw
    · rw [PresentedGroup.one_of_mem (List.mem_map_of_mem hw), map_one]
    · exact hx w hw
  refine ⟨PresentedGroup.toGroup h, fun w => ?_⟩
  change FreeGroup.lift f (FreeGroup.mk w) = _
  rw [key, MonoidHom.comp_apply]

theorem model {n : ℕ} {C : ℕ → ℕ}
    (hm : ∃ (E : Type) (_ : Group E) (ψ : PG 2 cw →* E)
      (τ : Multiplicative (ZMod n) →* E), Function.Injective τ ∧
        ∀ k (hk : k < rels.length), ψ (PresentedGroup.mk _ (FreeGroup.mk rels[k])) =
          τ (Multiplicative.ofAdd (C k : ZMod n)))
    (hx : (C 1 : ZMod n) = 0 ∧ (4 : ZMod n) * (C 0 + C 5) = 0 ∧ (4 : ZMod n) * (C 0 + C 6) = 0 ∧
      (3 : ZMod n) * (C 0 + C 0) = 0) :
    ∃ (E : Type) (_ : Group E) (φ : PG 2 coverWs →* E)
      (τ : Multiplicative (ZMod n) →* E), Function.Injective τ ∧
        ∀ i j m, i < 7 → j < 7 →
          φ (PresentedGroup.mk _ (FreeGroup.mk (wpow (rels.getD i [] ++ rels.getD j []) m))) =
            τ (Multiplicative.ofAdd ((m : ZMod n) * (C i + C j))) := by
  obtain ⟨E, _, ψ, τ, hτ, h⟩ := hm
  have hv : ∀ i j m, i < 7 → j < 7 →
      ψ (PresentedGroup.mk _ (FreeGroup.mk (wpow (rels.getD i [] ++ rels.getD j []) m))) =
        τ (Multiplicative.ofAdd ((m : ZMod n) * (C i + C j))) := by
    intro i j m hi hj
    rw [mk_wpow, ← FreeGroup.mul_mk, map_pow, map_mul, map_pow, map_mul,
      List.getD_eq_getElem _ _ (by rw [rels_length]; exact hi),
      List.getD_eq_getElem _ _ (by rw [rels_length]; exact hj), h i, h j, ← map_mul, ← map_pow,
      ← ofAdd_add, ← ofAdd_nsmul, nsmul_eq_mul]
  have e1 : bFive = rels.getD 1 [] := by decide +kernel
  have e5 : zOne = rels.getD 0 [] ++ rels.getD 5 [] := by decide +kernel
  have e6 : zTwo = rels.getD 0 [] ++ rels.getD 6 [] := by decide +kernel
  have e0 : zThree = rels.getD 0 [] ++ rels.getD 0 [] := by decide +kernel
  have hb : ψ (PresentedGroup.mk _ (FreeGroup.mk bFive)) = 1 := by
    rw [e1, List.getD_eq_getElem _ _ (by rw [rels_length]; omega), h 1, hx.1, ofAdd_zero, map_one]
  obtain ⟨φ, hφ⟩ := descend ψ (fun r hr => by
    simp only [extraWs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact hb
    · rw [e5, hv 0 5 4 (by omega) (by omega), Nat.cast_ofNat, hx.2.1, ofAdd_zero, map_one]
    · rw [e6, hv 0 6 4 (by omega) (by omega), Nat.cast_ofNat, hx.2.2.1, ofAdd_zero, map_one]
    · rw [e0, hv 0 0 3 (by omega) (by omega), Nat.cast_ofNat, hx.2.2.2, ofAdd_zero, map_one])
  exact ⟨E, inferInstance, φ, τ, hτ, fun i j m hi hj => by rw [hφ, hv i j m hi hj]⟩

theorem dvd_of_val {E : Type} [Group E] {n p : ℕ} [Fact p.Prime] (φ : PG 2 coverWs →* E)
    (τ : Multiplicative (ZMod n) →* E) (hτ : Function.Injective τ) {g : PG 2 coverWs}
    {c : ZMod n} (hg : φ g = τ (Multiplicative.ofAdd c)) (h1 : p • c = 0) (h2 : c ≠ 0) :
    p ∣ orderOf g := by
  have ho : orderOf (Multiplicative.ofAdd c) = p :=
    orderOf_eq_prime (by rw [← ofAdd_nsmul, h1, ofAdd_zero]) (by rwa [Ne, ofAdd_eq_one])
  rw [← ho, ← orderOf_injective τ hτ, ← hg]
  exact orderOf_map_dvd φ g

theorem walks : ∀ p ∈ walkWords, p.2 ∣ orderOf (PresentedGroup.mk
    {r : FreeGroup (Fin 2) | r ∈ coverWs.map FreeGroup.mk} (FreeGroup.mk p.1)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have e5 : zOne = rels.getD 0 [] ++ rels.getD 5 [] := by decide +kernel
  have e6 : zTwo = rels.getD 0 [] ++ rels.getD 6 [] := by decide +kernel
  have e0 : zThree = wpow (rels.getD 0 [] ++ rels.getD 0 []) 1 := by decide +kernel
  obtain ⟨E₁, _, φ₁, τ₁, hτ₁, h₁⟩ := model (n := 4) (C := CFSG.KD.L34F4a.Cst)
    (CFSG.Certificates.Mono.mono_sound (N := 960) rels (fun i => commWords (coverPairs i))
      relCodes_eq coverCodes_eq CFSG.KD.L34F4a.sQ pointsF4a) (by decide +kernel)
  obtain ⟨E₂, _, φ₂, τ₂, hτ₂, h₂⟩ := model (n := 4) (C := CFSG.KD.L34F4b.Cst)
    (CFSG.Certificates.Mono.mono_sound (N := 960) rels (fun i => commWords (coverPairs i))
      relCodes_eq coverCodes_eq CFSG.KD.L34F4b.sQ pointsF4b) (by decide +kernel)
  obtain ⟨E₃, _, φ₃, τ₃, hτ₃, h₃⟩ := model (n := 3) (C := CFSG.KD.L34P3.Cst)
    (CFSG.Certificates.Mono.mono_sound (N := 21) rels (fun i => commWords (coverPairs i))
      relCodes_eq coverCodes_eq CFSG.KD.L34P3.sQ pointsP3) (by decide +kernel)
  intro p hp
  simp only [walkWords, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · rw [e5]
    exact dvd_of_val φ₁ τ₁ hτ₁ (h₁ 0 5 2 (by omega) (by omega)) (by decide +kernel)
      (by decide +kernel)
  · rw [e6]
    exact dvd_of_val φ₂ τ₂ hτ₂ (h₂ 0 6 2 (by omega) (by omega)) (by decide +kernel)
      (by decide +kernel)
  · rw [e5, e6]
    refine dvd_of_val φ₁ τ₁ hτ₁ (c := (2 : ZMod 4) * (CFSG.KD.L34F4a.Cst 0 + CFSG.KD.L34F4a.Cst 5) +
      (2 : ZMod 4) * (CFSG.KD.L34F4a.Cst 0 + CFSG.KD.L34F4a.Cst 6)) ?_ (by decide +kernel)
      (by decide +kernel)
    rw [← FreeGroup.mul_mk, map_mul, map_mul, h₁ 0 5 2 (by omega) (by omega),
      h₁ 0 6 2 (by omega) (by omega), ← map_mul, ← ofAdd_add, Nat.cast_ofNat]
  · rw [e0]
    exact dvd_of_val φ₃ τ₃ hτ₃ (h₃ 0 0 1 (by omega) (by omega)) (by decide +kernel)
      (by decide +kernel)

end CertificateChecks.KernelL34

end
