module

public import Certificates.Kernel.Pk442010.Glue

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelPk442010

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbFind CFSG.KC.A45Cls CFSG.KC.EnumSound
  CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.Sporadic.Schreier
  CFSG.ClassicalInvolution.Q3.TA3.Check Certificates.OmegaPk Subgroup
open CFSG.KC.Pk442010 (injK_spec memRK_spec hitK_spec subK_spec centK_spec commK_spec nsK_spec
  prodK_spec eWK_spec eAllK_spec e9K_spec eGK_spec noOddK_spec ord9K_spec uK_spec pairK_spec
  lnK_shift lnK6_div lnK6_mod csAt lnK eL)

local notation "P45" => Equiv.Perm (Fin 45)

local notation "PR" => PRep 45 6

theorem mem8 {L : List P45} (hL : L.length = 8) {q : P45} : q ∈ L ↔ ∃ j < 8, L.getD j 1 = q := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hL ▸ hj, List.getD_eq_getElem _ _ hj⟩
  · rintro ⟨j, hj, rfl⟩
    have hj' : j < L.length := by
      rw [hL]
      exact hj
    exact ⟨j, hj', (List.getD_eq_getElem _ _ hj').symm⟩

theorem len_Q1 : (Certificates.P43Twin.Q1 ()).length = 8 := rfl

theorem len_Q2 : (Certificates.P43Twin.Q2 ()).length = 8 := rfl

theorem hQ1 : ∀ j < 8, PR (rQ1 j) ((Certificates.P43Twin.Q1 ()).getD j 1) := pins'.2.2.2.2.2.1

theorem hQ2 : ∀ j < 8, PR (rQ2 j) ((Certificates.P43Twin.Q2 ()).getD j 1) := pins'.2.2.2.2.2.2

theorem cjg (y : P45) : cj (g0 ()) y = g0 () * y * g0 () := by
  rw [cj, g0_inv]

theorem conj_swap1 {G : Type*} [Group G] (a b g a' : G) (hg : g * g = 1)
    (hc : a⁻¹ * a' * a * (g * b * g) = g * b * g * (a⁻¹ * a' * a)) :
    g * (a⁻¹ * a' * a) * g = (a * (g * b * g) * g)⁻¹ * a' * (a * (g * b * g) * g) := by
  have hgi : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have e1 : (a * (g * b * g) * g)⁻¹ * a' * (a * (g * b * g) * g) =
      g⁻¹ * ((g * b * g)⁻¹ * (a⁻¹ * a' * a * (g * b * g))) * g := by group
  have e2 : g⁻¹ * ((g * b * g)⁻¹ * (g * b * g * (a⁻¹ * a' * a))) * g =
      g⁻¹ * (a⁻¹ * a' * a) * g := by group
  rw [e1, hc, e2, hgi]

theorem conj_swap2 {G : Type*} [Group G] (a b g b' : G) (hg : g * g = 1)
    (hc : a * (g * b' * g) = g * b' * g * a) :
    b⁻¹ * b' * b = (a * (g * b * g) * g)⁻¹ * (g * b' * g) * (a * (g * b * g) * g) := by
  have h1 : a⁻¹ * (g * b' * g) * a = g * b' * g := by
    rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
  have e1 : (a * (g * b * g) * g)⁻¹ * (g * b' * g) * (a * (g * b * g) * g) =
      g⁻¹ * ((g * b * g)⁻¹ * (a⁻¹ * (g * b' * g) * a) * (g * b * g)) * g := by group
  have e2 : g⁻¹ * ((g * b * g)⁻¹ * (g * b' * g) * (g * b * g)) * g =
      (g * g)⁻¹ * (b⁻¹ * b' * (g * g) * b) * (g * g) := by group
  rw [e1, h1, e2, hg]
  simp only [inv_one, one_mul, mul_one]

variable {c : ℕ → P45}

theorem rho_facts (hc : ∀ i < CP.N, PR (CP.T i) (c i)) (hcC : ∀ i < CP.N, c i ∈ pkC) :
    (∀ A B, pkRho (A * B) = pkRho A * pkRho B) ∧ (∀ A, pkRho A = 1 → A = 1) ∧
      (∀ A, pkRho A ∈ pkP) ∧ (∀ A, pkRho A * Certificates.P43Twin.tA () =
        Certificates.P43Twin.tA () * pkRho A) ∧ ∃ A, pkRho A = Certificates.P43Twin.tA () := by
  have hmemC : ∀ A, pkRho A ∈ pkC := by
    intro A
    obtain ⟨i, hi, e⟩ := code_mem A
    obtain ⟨m, hm, em⟩ := memRK_spec rho.2.2.1 i hi
    have h1 : c m = rc (csAt csW i) := prep_unique (hc m hm) (by rw [em]; exact prep_rR i hi)
    change rc (code A) ∈ pkC
    rw [← e, ← h1]
    exact hcC m hm
  refine ⟨rho_mul, fun A hA => ?_, fun A => (Subgroup.mem_inf.1 (hmemC A)).1,
    fun A => Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hmemC A)).2, ?_⟩
  · obtain ⟨i, hi, e⟩ := code_mem A
    rcases injK_spec rho.2.1 prep_rR i hi with h | h
    · exact code28 A (by rw [← e]; exact h)
    · refine absurd ?_ h
      change rc (code A) = 1 at hA
      rw [e]
      exact hA
  · obtain ⟨i, hi, e⟩ := hitK_spec rho.2.2.2.1
    obtain ⟨A, hA⟩ := code_surj hi
    refine ⟨A, ?_⟩
    change rc (code A) = _
    rw [hA]
    exact prep_unique (prep_rR i hi) (by rw [e]; exact htA)

theorem subQ_facts (hc : ∀ i < CP.N, PR (CP.T i) (c i)) (hcC : ∀ i < CP.N, c i ∈ pkC)
    {Q : ℕ → ℕ} {L : List P45} (hL : L.length = 8) (hQ : ∀ j < 8, PR (Q j) (L.getD j 1))
    (h : CFSG.KC.Pk442010.subK CP.N CP.T CP.S Q tAL = true) :
    ((∀ q ∈ L, q ∈ pkC) ∧ (1 : P45) ∈ L ∧ (∀ a ∈ L, ∀ b ∈ L, a * b ∈ L) ∧ ∀ a ∈ L, a⁻¹ ∈ L) ∧
      Certificates.P43Twin.tA () ∈ L := by
  obtain ⟨h1, ⟨j1, hj1, e1⟩, ⟨jt, hjt, et⟩, h4, h5⟩ := subK_spec h hQ
  refine ⟨⟨fun q hq => ?_, (mem8 hL).2 ⟨j1, hj1, e1⟩, fun a ha b hb => ?_, fun a ha => ?_⟩,
    (mem8 hL).2 ⟨jt, hjt, prep_unique (hQ jt hjt) (by rw [et]; exact htA)⟩⟩
  · obtain ⟨j, hj, rfl⟩ := (mem8 hL).1 hq
    obtain ⟨m, hm, em⟩ := h1 j hj
    have e : c m = L.getD j 1 := prep_unique (hc m hm) (by rw [em]; exact hQ j hj)
    rw [← e]
    exact hcC m hm
  · obtain ⟨j, hj, rfl⟩ := (mem8 hL).1 ha
    obtain ⟨k, hk, rfl⟩ := (mem8 hL).1 hb
    obtain ⟨l, hl, e⟩ := h4 j hj k hk
    exact (mem8 hL).2 ⟨l, hl, e⟩
  · obtain ⟨j, hj, rfl⟩ := (mem8 hL).1 ha
    obtain ⟨k, hk, e⟩ := h5 j hj
    exact (mem8 hL).2 ⟨k, hk, (inv_eq_of_mul_eq_one_right e).symm⟩

theorem cent_facts (hc : ∀ i < CP.N, PR (CP.T i) (c i))
    (hcall : ∀ y ∈ pkC, ∃ i < CP.N, c i = y) {R Q : ℕ → ℕ} (f : ℕ → P45) {L : List P45}
    (hL : L.length = 8) (hQ : ∀ j < 8, PR (Q j) (L.getD j 1))
    (hR : ∀ i < 24, PR (R (csAt csW i)) (f (csAt csW i))) (htL : Certificates.P43Twin.tA () ∈ L)
    (h : CFSG.KC.Pk442010.centK CP.N CP.T csW R Q = true) :
    (∀ A : SL23, ∀ q ∈ L, f (code A) * q = q * f (code A)) ∧
      ∀ x ∈ pkP, (∀ q ∈ L, x * q = q * x) → ∃ A : SL23, f (code A) = x := by
  obtain ⟨h1, h2⟩ := centK_spec (ρ := f) h hR hQ hc
  refine ⟨fun A q hq => ?_, fun x hx hcx => ?_⟩
  · obtain ⟨i, hi, e⟩ := code_mem A
    obtain ⟨j, hj, rfl⟩ := (mem8 hL).1 hq
    rw [← e]
    exact h1 i hi j hj
  · have hxC : x ∈ pkC :=
      Subgroup.mem_inf.2 ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 (hcx _ htL)⟩
    obtain ⟨k, hk, rfl⟩ := hcall x hxC
    obtain ⟨i, hi, e⟩ := h2 k hk fun j hj => hcx _ ((mem8 hL).2 ⟨j, hj, rfl⟩)
    obtain ⟨A, hA⟩ := code_surj hi
    exact ⟨A, by rw [hA]; exact e⟩

theorem memG_fact (hc : ∀ i < CP.N, PR (CP.T i) (c i)) (hcC : ∀ i < CP.N, c i ∈ pkC) :
    g0 () ∈ pkC := by
  obtain ⟨m, hm, em⟩ := memK_spec comm.2.1
  have e : c m = g0 () := prep_unique (hc m hm) (by rw [em]; exact hg0)
  rw [← e]
  exact hcC m hm

theorem comm_facts :
    (∀ A B : SL23, pkRho A * cj (g0 ()) (pkRho B) = cj (g0 ()) (pkRho B) * pkRho A) ∧
      ∃ A : SL23, ∀ B : SL23, pkRho A ≠ cj (g0 ()) (pkRho B) := by
  obtain ⟨h1, i, hi, hne⟩ := commK_spec (ρ := rc) (β := fun c => cj (g0 ()) (rc c)) comm.1
    prep_rR prep_rB
  refine ⟨fun A B => ?_, ?_⟩
  · obtain ⟨i, hi, ei⟩ := code_mem A
    obtain ⟨j, hj, ej⟩ := code_mem B
    have h := h1 i hi j hj
    rw [ei, ej] at h
    exact h
  · obtain ⟨A, hA⟩ := code_surj hi
    refine ⟨A, fun B e => ?_⟩
    obtain ⟨j, hj, ej⟩ := code_mem B
    have hb := prep_rB j hj
    have e' : cj (g0 ()) (rc (csAt csW j)) = rc (csAt csW i) := by
      rw [ej, ← hA]
      exact e.symm
    rw [e'] at hb
    exact hne j hj (CFSG.KC.OrbRow.eq_of_prep (by norm_num) (prep_rR i hi) hb
      (lnK_shift 270 rhoL _) (lnK_shift 270 kbL _))

theorem ns_facts (hc : ∀ i < CP.N, PR (CP.T i) (c i)) (hcall : ∀ y ∈ pkC, ∃ i < CP.N, c i = y)
    {Q : ℕ → ℕ} {L : List P45} (hL : L.length = 8) (hQ : ∀ j < 8, PR (Q j) (L.getD j 1))
    (h : CFSG.KC.Pk442010.nsK CP.N CP.T Q tAL = true) :
    ∀ x ∈ pkC, x ^ 3 = 1 → ¬ (∀ q ∈ L, x * q = q * x) → ∀ q ∈ L, ∃ q' ∈ L,
      q = x * q' * x⁻¹ * q'⁻¹ ∨ q = Certificates.P43Twin.tA () * (x * q' * x⁻¹ * q'⁻¹) := by
  intro x hx h3 hnc q hq
  obtain ⟨k, hk, rfl⟩ := hcall x hx
  obtain ⟨j, hj, rfl⟩ := (mem8 hL).1 hq
  have hnc' : ¬ ∀ j < 8, c k * L.getD j 1 = L.getD j 1 * c k := fun h' => hnc fun q hq => by
    obtain ⟨j, hj, rfl⟩ := (mem8 hL).1 hq
    exact h' j hj
  obtain ⟨l, hl, e | e⟩ := nsK_spec h hc hQ htA k hk h3 hnc' j hj
  · refine ⟨_, (mem8 hL).2 ⟨l, hl, rfl⟩, Or.inl ?_⟩
    rw [← e]
    group
  · refine ⟨_, (mem8 hL).2 ⟨l, hl, rfl⟩, Or.inr ?_⟩
    have htt := (sq_ne_of_ord ordA).1
    have e2 : Certificates.P43Twin.tA () * (Certificates.P43Twin.tA () * L.getD j 1 *
        L.getD l 1 * c k * (c k)⁻¹ * (L.getD l 1)⁻¹) =
        Certificates.P43Twin.tA () * Certificates.P43Twin.tA () * L.getD j 1 := by group
    rw [← e, e2, htt, one_mul]

theorem prod_facts : ∃ s : Finset P45, s.card = 32 ∧
    ∀ p ∈ s, ∃ q ∈ Certificates.P43Twin.Q1 (), ∃ r ∈ Certificates.P43Twin.Q2 (), p = q * r := by
  have h := prodK_spec comm.2.2 hQ1 hQ2
  refine ⟨(Finset.range 32).image fun a => (Certificates.P43Twin.Q1 ()).getD
    (Nat.div (lnK 6 prodP a) 8) 1 * (Certificates.P43Twin.Q2 ()).getD (Nat.mod (lnK 6 prodP a) 8) 1,
    ?_, fun p hp => ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb e
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    rcases lt_trichotomy a b with hab | hab | hab
    · exact absurd e.symm (h b hb a hab)
    · exact hab
    · exact absurd e (h a ha b hab)
  · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨_, (mem8 len_Q1).2 ⟨_, lnK6_div, rfl⟩, _, (mem8 len_Q2).2 ⟨_, lnK6_mod, rfl⟩, rfl⟩

theorem inE_iff (hc : ∀ i < CP.N, PR (CP.T i) (c i))
    (hinj : ∀ i < CP.N, ∀ j < CP.N, c i = c j → i = j) {k : ℕ} (hk : k < CP.N) :
    (∃ A B : SL23, pkRho A * cj (g0 ()) (pkRho B) = c k) ↔ eL eW k ≠ 0 := by
  constructor
  · rintro ⟨A, B, e⟩
    obtain ⟨i, hi, ei⟩ := code_mem A
    obtain ⟨j, hj, ej⟩ := code_mem B
    obtain ⟨m, hm, em, hne⟩ := eAllK_spec (ρ := rc) (β := fun c => cj (g0 ()) (rc c)) eWit.2
      prep_rR prep_rB hc i hi j hj
    have h : c m = c k := by
      rw [em, ← e, ei, ej]
      rfl
    rw [← hinj m hm k hk h]
    exact hne
  · intro hne
    obtain ⟨i, hi, j, hj, e⟩ := eWK_spec (ρ := rc) (β := fun c => cj (g0 ()) (rc c)) eWit.1
      prep_rR prep_rB hc k hk hne
    obtain ⟨A, hA⟩ := code_surj hi
    obtain ⟨B, hB⟩ := code_surj hj
    refine ⟨A, B, ?_⟩
    change rc (code A) * cj (g0 ()) (rc (code B)) = c k
    rw [hA, hB, e]

theorem swap_of {x : P45} {A B : SL23} (e : pkRho A * cj (g0 ()) (pkRho B) = x * g0 ()) :
    (∀ A', ∃ B', cj (g0 ()) (pkRho B') = x⁻¹ * pkRho A' * x) ∧
      ∀ B', ∃ A', pkRho A' = x⁻¹ * cj (g0 ()) (pkRho B') * x := by
  have hx : x = pkRho A * (g0 () * pkRho B * g0 ()) * g0 () := by
    rw [← cjg, e, mul_assoc, g0_sq, mul_one]
  have hD : ∀ A' : SL23, pkRho (A⁻¹ * A' * A) = (pkRho A)⁻¹ * pkRho A' * pkRho A := fun A' => by
    change rhoH (A⁻¹ * A' * A) = (rhoH A)⁻¹ * rhoH A' * rhoH A
    rw [map_mul, map_mul, map_inv]
  have hDB : ∀ B' : SL23, pkRho (B⁻¹ * B' * B) = (pkRho B)⁻¹ * pkRho B' * pkRho B := fun B' => by
    change rhoH (B⁻¹ * B' * B) = (rhoH B)⁻¹ * rhoH B' * rhoH B
    rw [map_mul, map_mul, map_inv]
  refine ⟨fun A' => ⟨A⁻¹ * A' * A, ?_⟩, fun B' => ⟨B⁻¹ * B' * B, ?_⟩⟩
  · have hc := comm_facts.1 (A⁻¹ * A' * A) B
    rw [cjg, hD] at hc
    rw [cjg, hD, hx]
    exact conj_swap1 _ _ _ _ g0_sq hc
  · have hc := comm_facts.1 A B'
    rw [cjg] at hc
    rw [cjg, hDB, hx]
    exact conj_swap2 _ _ _ _ g0_sq hc

theorem e_facts (hc : ∀ i < CP.N, PR (CP.T i) (c i)) (hcall : ∀ y ∈ pkC, ∃ i < CP.N, c i = y)
    (hinj : ∀ i < CP.N, ∀ j < CP.N, c i = c j → i = j) :
    (∀ x ∈ pkC, x ^ 9 = 1 → ∃ A B, pkRho A * cj (g0 ()) (pkRho B) = x) ∧
    (∀ x ∈ pkC, (¬ ∃ A B, pkRho A * cj (g0 ()) (pkRho B) = x) →
      (∀ A, ∃ B, cj (g0 ()) (pkRho B) = x⁻¹ * pkRho A * x) ∧
        ∀ B, ∃ A, pkRho A = x⁻¹ * cj (g0 ()) (pkRho B) * x) ∧
    ∀ b ∈ pkC, ((∃ A B, pkRho A * cj (g0 ()) (pkRho B) = b) ↔
      ¬ ∃ A B, pkRho A * cj (g0 ()) (pkRho B) = b * g0 ()) := by
  have h3 : ∀ b ∈ pkC, ((∃ A B, pkRho A * cj (g0 ()) (pkRho B) = b) ↔
      ¬ ∃ A B, pkRho A * cj (g0 ()) (pkRho B) = b * g0 ()) := by
    intro b hb
    obtain ⟨k, hk, rfl⟩ := hcall b hb
    obtain ⟨m, hm, em, hiff⟩ := eGK_spec eG hc hg0 k hk
    rw [inE_iff hc hinj hk, ← em, inE_iff hc hinj hm, hiff]
  refine ⟨fun x hx h9 => ?_, fun x hx hnE => ?_, h3⟩
  · obtain ⟨k, hk, rfl⟩ := hcall x hx
    exact (inE_iff hc hinj hk).2 (e9K_spec e9 hc k hk h9)
  · obtain ⟨A, B, e⟩ := not_not.1 (fun h => hnE ((h3 x hx).2 h))
    exact swap_of e

theorem noOdd_facts {N W : ℕ} {T : ℕ → ℕ} {C : Subgroup P45} (hc : ∀ i < N, PR (T i) (c i))
    (hcC : ∀ i < N, c i ∈ C) (hcall : ∀ y ∈ C, ∃ i < N, c i = y)
    (h1 : CFSG.KC.Pk442010.noOddK N T W = true) (h2 : CFSG.KC.Pk442010.ord9K N T = true) :
    (∀ o ∈ C, o ≠ 1 → o ^ 3 = 1 → ∃ x ∈ C, (o * (x * o * x⁻¹)) ^ 3 ≠ 1) ∧
      ∀ x ∈ C, x ^ 9 = 1 → x ^ 3 = 1 := by
  refine ⟨fun o ho h1' h3 => ?_, fun x hx h9 => ?_⟩
  · obtain ⟨k, hk, rfl⟩ := hcall o ho
    obtain ⟨s, hs, s', hs', e, hne⟩ := noOddK_spec h1 hc k hk h1' h3
    have hs'' : c s' = (c s)⁻¹ := (inv_eq_of_mul_eq_one_right e).symm
    rw [hs''] at hne
    exact ⟨c s, hcC s hs, hne⟩
  · obtain ⟨k, hk, rfl⟩ := hcall x hx
    exact ord9K_spec h2 hc k hk h9

theorem u_facts (hc : ∀ i < CQ.N, PR (CQ.T i) (c i)) (hcall : ∀ y ∈ pkCB, ∃ i < CQ.N, c i = y) :
    ∃ U : List P45, U.length = 12 ∧ (1 : P45) ∈ U ∧ (∀ a ∈ U, ∀ b ∈ U, a * b ∈ U) ∧
      (∀ a ∈ U, a⁻¹ ∈ U) ∧ ∀ x ∈ pkCB, x ^ 3 = 1 → x ∈ U := by
  obtain ⟨-, ⟨k1, hk1, e1⟩, hmul, hinv, hall⟩ := uK_spec u hc
  have hmem : ∀ {y : P45}, y ∈ (List.range 12).map (fun a => c (lnK 7 uW a)) ↔
      ∃ a < 12, c (lnK 7 uW a) = y := by
    intro y
    simp only [List.mem_map, List.mem_range]
  refine ⟨(List.range 12).map fun a => c (lnK 7 uW a), by simp, hmem.2 ⟨k1, hk1, e1⟩,
    fun a ha b hb => ?_, fun a ha => ?_, fun x hx h3 => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := hmem.1 ha
    obtain ⟨j, hj, rfl⟩ := hmem.1 hb
    obtain ⟨k, hk, e⟩ := hmul i hi j hj
    exact hmem.2 ⟨k, hk, e⟩
  · obtain ⟨i, hi, rfl⟩ := hmem.1 ha
    obtain ⟨j, hj, e⟩ := hinv i hi
    exact hmem.2 ⟨j, hj, (inv_eq_of_mul_eq_one_right e).symm⟩
  · obtain ⟨k, hk, rfl⟩ := hcall x hx
    obtain ⟨j, hj, e⟩ := hall k hk h3
    exact hmem.2 ⟨j, hj, e⟩

theorem pair_facts (hc : ∀ i < CP.N, PR (CP.T i) (c i)) (hcall : ∀ y ∈ pkC, ∃ i < CP.N, c i = y) :
    ∀ a ∈ pkC, ∀ b ∈ pkC, a * a = Certificates.P43Twin.tA () →
      b * b = Certificates.P43Twin.tA () → b * a = Certificates.P43Twin.tA () * a * b →
      (∀ q ∈ Certificates.P43Twin.Q1 (), q ∈ q8B (Certificates.P43Twin.tA ()) a b) ∨
        ∀ q ∈ Certificates.P43Twin.Q2 (), q ∈ q8B (Certificates.P43Twin.tA ()) a b := by
  intro a ha b hb haa hbb hba
  obtain ⟨i, hi, rfl⟩ := hcall a ha
  obtain ⟨j, hj, rfl⟩ := hcall b hb
  rcases pairK_spec pair hc hQ1 hQ2 htA i hi j hj haa hbb hba with h | h
  · refine Or.inl fun q hq => ?_
    obtain ⟨k, hk, rfl⟩ := (mem8 len_Q1).1 hq
    exact h k hk
  · refine Or.inr fun q hq => ?_
    obtain ⟨k, hk, rfl⟩ := (mem8 len_Q2).1 hq
    exact h k hk

theorem cover_facts (hcard : Nat.card pkC = 576) (hcardB : Nat.card pkCB = 96)
    (htP : Certificates.P43Twin.tA () ∈ pkP) (htBP : Certificates.P43Twin.tB () ∈ pkP) :
    ∀ p ∈ pkP, p * p = 1 → p ≠ 1 → ∃ g ∈ pkP,
      g * p * g⁻¹ = Certificates.P43Twin.tA () ∨ g * p * g⁻¹ = Certificates.P43Twin.tB () := by
  obtain ⟨a, b, h⟩ := inv_cls
  obtain ⟨gA, hgA, hA⟩ := h _ htP (sq_ne_of_ord ordA).1 (sq_ne_of_ord ordA).2
  obtain ⟨gB, hgB, hB⟩ := h _ htBP (sq_ne_of_ord ordB).1 (sq_ne_of_ord ordB).2
  have eA : gA * Certificates.P43Twin.tA () * gA⁻¹ = a := by
    rcases hA with hA | hA
    · exact hA.1
    · exact absurd (hcard.symm.trans hA.2) (by decide)
  have eB : gB * Certificates.P43Twin.tB () * gB⁻¹ = b := by
    rcases hB with hB | hB
    · exact absurd (hcardB.symm.trans hB.2) (by decide)
    · exact hB.1
  intro p hp h2 h1
  obtain ⟨g, hg, hp' | hp'⟩ := h p hp h2 h1
  · refine ⟨gA⁻¹ * g, mul_mem (inv_mem hgA) hg, Or.inl ?_⟩
    have e : gA⁻¹ * g * p * (gA⁻¹ * g)⁻¹ = gA⁻¹ * (g * p * g⁻¹) * gA := by group
    rw [e, hp'.1, ← eA]
    group
  · refine ⟨gB⁻¹ * g, mul_mem (inv_mem hgB) hg, Or.inr ?_⟩
    have e : gB⁻¹ * g * p * (gB⁻¹ * g)⁻¹ = gB⁻¹ * (g * p * g⁻¹) * gB := by group
    rw [e, hp'.1, ← eB]
    group

theorem facts : Certificates.OmegaPk.Facts := by
  obtain ⟨c, hc, hcC, hcall, hinj, hcard⟩ := cp_facts
  obtain ⟨d, hd, hdC, hdall, hcardB, htBP⟩ := cq_facts
  have hrho := rho_facts hc hcC
  have htP : Certificates.P43Twin.tA () ∈ pkP := by
    obtain ⟨-, -, h3, -, A, hA⟩ := hrho
    rw [← hA]
    exact h3 A
  have hs1 := subQ_facts hc hcC len_Q1 hQ1 subQ.1
  have hs2 := subQ_facts hc hcC len_Q2 hQ2 subQ.2
  exact
    { ordA := ordA
      ordB := ordB
      cardC := hcard
      cardCB := hcardB
      cover := cover_facts hcard hcardB htP htBP
      rho := hrho
      subQ1 := hs1.1
      subQ2 := hs2.1
      centA := cent_facts hc hcall rc len_Q2 hQ2 prep_rR hs2.2 cent.1
      centB := cent_facts hc hcall (fun c => cj (g0 ()) (rc c)) len_Q1 hQ1 prep_rB hs1.2 cent.2.1
      memG := memG_fact hc hcC
      comm := comm_facts
      nsQ1 := ns_facts hc hcall len_Q1 hQ1 ns.1
      nsQ2 := ns_facts hc hcall len_Q2 hQ2 ns.2
      prod := prod_facts
      e := e_facts hc hcall hinj
      noOddA := noOdd_facts hc hcC hcall noOdd.1 noOdd.2.1
      noOddB := noOdd_facts hd hdC hdall noOdd.2.2.1 noOdd.2.2.2
      u := u_facts hd hdall
      pair := pair_facts hc hcall }

end CertificateChecks.KernelPk442010

end
