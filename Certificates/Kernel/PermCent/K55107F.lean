module

public import Certificates.Kernel.PermCent.K55107
public import CFSG.Certificates.Kernel.PermCent.ClassReps
public import CFSG.Sporadic.SmallOddCore.Normalizing
public import CFSG.GH74.KGroups.U33
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic

public section

namespace CertificateChecks.KernelPermCent.U33

open CFSG.GH74.KGroups.U33 CFSG.GH74.KGroups.U33.Cover CFSG.KC.OrbGroup CFSG.KS.Raw.Orb
  CFSG.KC.Enum CFSG.KS CFSG.KC.ConjOrb CFSG.KC.LeftOrb CFSG.KC.BfsPin CFSG.KC.ClassReps
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallOddCore
open Subgroup

theorem prep_tab {a : Array ℕ} {p : ℕ} {g : Equiv.Perm (Fin 28)} (ht : tabOK a p = true)
    (hr : CFSG.Monster.B.Co2.Rep 28 a g) : PRep 28 5 p g := fun x =>
  (Nat.eq_of_beq_eq_true (List.all_eq_true.1 ht x (List.mem_range.2 x.2))).trans (hr x)

theorem eq_of_eqF {p q : ℕ} {σ τ : Equiv.Perm (Fin 28)} (h : eqF p q = true)
    (hp : PRep 28 5 p σ) (hq : PRep 28 5 q τ) : σ = τ :=
  Equiv.ext fun x => Fin.ext ((hp x).symm.trans
    ((Nat.eq_of_beq_eq_true (List.all_eq_true.1 h x (List.mem_range.2 x.2))).trans (hq x)))

theorem one_of_isId {p : ℕ} {σ : Equiv.Perm (Fin 28)} (h : isId p = true) (hp : PRep 28 5 p σ) :
    σ = 1 :=
  Equiv.ext fun x => Fin.ext ((hp x).symm.trans
    (Nat.eq_of_beq_eq_true (List.all_eq_true.1 h x (List.mem_range.2 x.2))))

theorem ne_one_of_isId {p : ℕ} {σ : Equiv.Perm (Fin 28)} (h : isId p = false)
    (hp : PRep 28 5 p σ) : σ ≠ 1 := by
  rintro rfl
  have : isId p = true := List.all_eq_true.2 fun i hi => by
    have e : at5 p i = i := hp ⟨i, List.mem_range.1 hi⟩
    rw [e]
    exact Nat.beq_refl i
  rw [this] at h
  simp at h

theorem prep_pc {p q : ℕ} {σ τ : Equiv.Perm (Fin 28)} (hp : PRep 28 5 p σ) (hq : PRep 28 5 q τ) :
    PRep 28 5 (pc p q) (σ * τ) :=
  prep_pcomp (by norm_num) hp hq

theorem baseL_lt : ∀ p ∈ baseL, p < 28 := by decide

@[expose] def gP (k : ℕ) : Equiv.Perm (Fin 28) := if k = 0 then pa else pb

abbrev P : Subgroup (Equiv.Perm (Fin 28)) := QP.originalSubgroup

theorem closure_gP : closure (gP '' {k | k < 2}) = P := by
  change closure (gP '' {k | k < 2}) = QP.originalSubgroup
  rw [QP_closure]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k
    · exact Or.inl (if_pos rfl)
    · exact Or.inr (if_neg (by norm_num))
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, if_pos rfl⟩
    · exact ⟨1, by norm_num, if_neg (by norm_num)⟩

theorem rep_pa : CFSG.Monster.B.Co2.Rep 28 genL[0]! pa := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem rep_pb : CFSG.Monster.B.Co2.Rep 28 genL[1]! pb := by
  unfold CFSG.Monster.B.Co2.Rep
  decide

theorem prep_gP {G : ℕ → ℕ} (h0 : tabOK genL[0]! (G 0) = true)
    (h1 : tabOK genL[1]! (G 1) = true) : ∀ k < 2, PRep 28 5 (G k) (gP k) := by
  intro k hk
  interval_cases k
  · rw [gP, if_pos rfl]
    exact prep_tab h0 rep_pa
  · rw [gP, if_neg (by norm_num)]
    exact prep_tab h1 rep_pb

@[expose] noncomputable def sylP (k : ℕ) : Equiv.Perm (Fin 28) := permOfArr 28 sylL[k]!

theorem syl_inv : (List.range 6).all (fun k => isInvA 28 sylL[k]! (invCand 28 sylL[k]!)) = true := by
  decide +kernel

theorem prep_syl : ∀ k < 6, PRep 28 5 (SH.G k) (sylP k) := by
  intro k hk
  obtain ⟨-, -, -, -, -, -, h, -⟩ := binds
  exact prep_tab (List.all_eq_true.1 h k (List.mem_range.2 hk))
    (rep_permOfArr (List.all_eq_true.1 syl_inv k (List.mem_range.2 hk))).1

noncomputable abbrev U : Equiv.Perm (Fin 28) := sylP 3

theorem prep_U : PRep 28 5 pU U := prep_syl 3 (by norm_num)

theorem prep_one {p : ℕ} (h : isId p = true) : PRep 28 5 p 1 := fun x =>
  (Nat.eq_of_beq_eq_true (List.all_eq_true.1 h x (List.mem_range.2 x.2)))

theorem pe_facts : Nat.card P = 6048 ∧ (∀ i < 6048, ∃ σ ∈ P, PRep 28 5 (PE.T i) σ) ∧
    ∀ y ∈ P, ∃ i < 6048, PRep 28 5 (PE.T i) y := by
  obtain ⟨h0, h1, -, -, -, -, -, -, -, hT0, -, hN, -, -, -, hng, -⟩ := binds
  obtain ⟨c, hc0, hc, hmem, hcl, hinj⟩ := leftOrb_reps (g := gP) (N := PE.N) (by norm_num)
    (fun k hk => prep_gP h0 h1 k (hng ▸ hk)) (fun i hi => PE.cl i hi) (fun i hi => PE.tr i hi)
    (by rw [hN]; norm_num) (prep_one hT0) baseL_lt PE.k
  obtain ⟨hcard, hall⟩ := group_of_reps (MonoidHom.id _) Function.injective_id gP c
    ⟨0, by rw [hN]; norm_num, hc0⟩ hmem hcl hinj
  rw [hng, closure_gP, hN] at hcard hall
  rw [hng, closure_gP] at hmem
  rw [hN] at hc hmem
  refine ⟨hcard, fun i hi => ⟨c i, hmem i hi, hc i hi⟩, fun y hy => ?_⟩
  obtain ⟨i, hi, e⟩ := hall y hy
  have h := hc i hi
  rw [e] at h
  exact ⟨i, hi, h⟩

theorem mem_P {p : ℕ} {σ : Equiv.Perm (Fin 28)} (hm : memP p = true) (hp : PRep 28 5 p σ) :
    σ ∈ P := by
  obtain ⟨i, hi, e⟩ := List.any_eq_true.1 hm
  obtain ⟨τ, hτ, hτp⟩ := pe_facts.2.1 i (List.mem_range.1 hi)
  rw [Nat.eq_of_beq_eq_true e] at hτp
  rwa [prep_eq hp hτp]

theorem ex_P {p : ℕ} (hm : memP p = true) : ∃ σ ∈ P, PRep 28 5 p σ := by
  obtain ⟨i, hi, e⟩ := List.any_eq_true.1 hm
  obtain ⟨τ, hτ, hτp⟩ := pe_facts.2.1 i (List.mem_range.1 hi)
  rw [Nat.eq_of_beq_eq_true e] at hτp
  exact ⟨τ, hτ, hτp⟩

theorem U_mul_U : U * U = 1 := one_of_isId outer.2.1 (prep_pc prep_U prep_U)

theorem U_sq : U ^ 2 = 1 := by rw [sq, U_mul_U]

theorem U_inv : U⁻¹ = U := inv_eq_of_mul_eq_one_right U_mul_U

theorem U_not_mem : U ∉ P := by
  intro h
  obtain ⟨i, hi, hr⟩ := pe_facts.2.2 U h
  have e := pkeyK_congr baseL_lt hr prep_U
  have h1 := List.all_eq_true.1 outer.1 i (List.mem_range.2 hi)
  rw [e, Nat.beq_refl] at h1
  simp at h1

theorem U_normalizes : ∀ p ∈ P, U * p * U⁻¹ ∈ P := by
  have hle : closure (gP '' {k | k < 2}) ≤ P.comap (MulAut.conj U).toMonoidHom := by
    rw [closure_le]
    rintro z ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, U_inv]
    obtain ⟨h0, h1, -⟩ := binds
    have hk' : k < 2 := hk
    have hg := prep_gP h0 h1 k hk'
    interval_cases k
    · exact mem_P outer.2.2.1 (by rw [mul_assoc]; exact prep_pc prep_U (prep_pc hg prep_U))
    · exact mem_P outer.2.2.2.1 (by rw [mul_assoc]; exact prep_pc prep_U (prep_pc hg prep_U))
  rw [closure_gP] at hle
  intro p hp
  have := hle hp
  rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

noncomputable abbrev R : Subgroup (Equiv.Perm (Fin 28)) := P ⊔ zpowers U

theorem card_R : Nat.card R = 12096 := by
  have h := card_sup_zpowers U_sq U_normalizes U_not_mem
  rw [pe_facts.1] at h
  omega

theorem syl_facts : Nat.card (closure (sylP '' {k | k < 6})) = 64 ∧
    closure (sylP '' {k | k < 6}) ≤ R ∧
    ∀ y ∈ closure (sylP '' {k | k < 6}), ∃ i < 64, PRep 28 5 (SH.T i) y := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hT0, -, -, -, hN, -, -, -, hng, -⟩ := binds
  obtain ⟨c, hc0, hc, hmem, hcl, hinj⟩ := leftOrb_reps (g := sylP) (N := SH.N) (by norm_num)
    (fun k hk => prep_syl k (hng ▸ hk)) (fun i hi => SH.cl i hi) (fun i hi => SH.tr i hi)
    (by rw [hN]; norm_num) (prep_one hT0) baseL_lt SH.k
  obtain ⟨hcard, hall⟩ := group_of_reps (MonoidHom.id _) Function.injective_id sylP c
    ⟨0, by rw [hN]; norm_num, hc0⟩ hmem hcl hinj
  rw [hng, hN] at hcard hall
  rw [hN] at hc
  refine ⟨hcard, ?_, fun y hy => ?_⟩
  · rw [closure_le]
    rintro z ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, mem_sup_zpowers_iff U_sq U_normalizes]
    have h := List.all_eq_true.1 outer.2.2.2.2 k (List.mem_range.2 hk)
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · exact Or.inl (mem_P h (prep_syl k hk))
    · exact Or.inr (mem_P h (prep_pc (prep_syl k hk) prep_U))
  · obtain ⟨i, hi, e⟩ := hall y hy
    have h := hc i hi
    rw [e] at h
    exact ⟨i, hi, h⟩

theorem card_factorization : 2 ^ (Nat.card R).factorization 2 = 64 := by
  rw [card_R, show (12096 : ℕ) = 2 ^ 6 * 189 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  norm_num

theorem class_facts {N r : ℕ} {G GI T E D S : ℕ → ℕ} {t : Equiv.Perm (Fin 28)}
    (hh : headK 28 5 2 G GI = true) (h0 : tabOK genL[0]! (G 0) = true)
    (h1 : tabOK genL[1]! (G 1) = true) (hcl : ∀ i < N, closPt 28 5 2 N G GI T E i = true)
    (htr : ∀ i < N, treePt 2 N r E D i = true) (hr : r < N) (ht : PRep 28 5 (T r) t)
    (hK : distinctK N (fun i => pkeyK 28 5 baseL (T i)) S = true) :
    N * Nat.card ↥(P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 28)))) = 6048 ∧
      ∀ y, (∃ i < N, PRep 28 5 (T i) y) → ∃ h ∈ P, y = h * t * h⁻¹ := by
  obtain ⟨c, hc, hreach, hcl', hinj⟩ := conjOrb_reps (g := gP) (t := t) (by norm_num) hh
    (prep_gP h0 h1) hcl htr hr ht baseL_lt hK
  rw [closure_gP] at hreach
  have hn := ncard_conjClass_of_reps (ng := 2) gP c (by rw [closure_gP]; exact hreach) hcl'
    ⟨r, hr, prep_eq (hc r hr) ht⟩ hinj
  rw [closure_gP] at hn
  refine ⟨?_, fun y ⟨i, hi, hy⟩ => ?_⟩
  · rw [← hn, ncard_conjClass_mul_card, pe_facts.1]
  · rw [← prep_eq (hc i hi) hy]
    exact hreach i hi

theorem classA : Nat.card ↥(P ⊓ centralizer ({sylP 0} : Set (Equiv.Perm (Fin 28)))) = 96 ∧
    ∀ y, (∃ i < 63, PRep 28 5 (CA.T i) y) → ∃ h ∈ P, y = h * sylP 0 * h⁻¹ := by
  obtain ⟨-, -, a3, a4, -, -, -, a8, -, -, -, -, a13, -, -, -, -, -, -, a20, -⟩ := binds
  have ht : PRep 28 5 (CA.T CA.r0) (sylP 0) := by
    rw [Nat.eq_of_beq_eq_true a8]
    exact prep_syl 0 (by norm_num)
  have h := class_facts (N := CA.N) CA.h a3 a4 (fun i hi => CA.cl i hi) (fun i hi => CA.tr0 i hi)
    (by rw [a13]; exact a20) ht CA.k
  rw [a13] at h
  exact ⟨by omega, h.2⟩

theorem classB : Nat.card ↥(P ⊓ centralizer ({U} : Set (Equiv.Perm (Fin 28)))) = 24 ∧
    ∀ y, (∃ i < 252, PRep 28 5 (CB.T i) y) → ∃ h ∈ P, y = h * U * h⁻¹ := by
  obtain ⟨-, -, -, -, a5, a6, -, -, a9, -, -, -, -, a14, -, -, -, -, -, -, a21⟩ := binds
  have ht : PRep 28 5 (CB.T CB.r0) U := by
    rw [Nat.eq_of_beq_eq_true a9]
    exact prep_U
  have h := class_facts (N := CB.N) CB.h a5 a6 (fun i hi => CB.cl i hi) (fun i hi => CB.tr0 i hi)
    (by rw [a14]; exact a21) ht CB.k
  rw [a14] at h
  exact ⟨by omega, h.2⟩

theorem inClasses_spec {p : ℕ} {σ : Equiv.Perm (Fin 28)} (h : inClasses true true p = true)
    (hp : PRep 28 5 p σ) : ∃ h ∈ P, σ = h * sylP 0 * h⁻¹ ∨ σ = h * U * h⁻¹ := by
  rw [inClasses, Bool.or_eq_true, Bool.true_and, Bool.true_and, List.any_eq_true,
    List.any_eq_true] at h
  rcases h with ⟨j, hj, e⟩ | ⟨j, hj, e⟩
  · obtain ⟨g, hg, e2⟩ := classA.2 σ ⟨j, List.mem_range.1 hj, by
      rw [Nat.eq_of_beq_eq_true e]
      exact hp⟩
    exact ⟨g, hg, Or.inl e2⟩
  · obtain ⟨g, hg, e2⟩ := classB.2 σ ⟨j, List.mem_range.1 hj, by
      rw [Nat.eq_of_beq_eq_true e]
      exact hp⟩
    exact ⟨g, hg, Or.inr e2⟩

theorem invol_conj {t : Equiv.Perm (Fin 28)} (htR : t ∈ R) (ht : orderOf t = 2) :
    ∃ g ∈ P, t = g * sylP 0 * g⁻¹ ∨ t = g * U * g⁻¹ := by
  obtain ⟨hS, hSR, hSmem⟩ := syl_facts
  obtain ⟨x, hxR, hxS⟩ := CFSG.Sporadic.SmallOddCore.exists_conj_mem_of_card hSR
    (by rw [hS, card_factorization]) htR ht
  obtain ⟨i, hi, hy⟩ := hSmem _ hxS
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht, sq] at h
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hsq : (x⁻¹ * t * x) * (x⁻¹ * t * x) = 1 := by
    have e : x⁻¹ * t * x * (x⁻¹ * t * x) = x⁻¹ * (t * t) * x := by group
    rw [e, ht2, mul_one, inv_mul_cancel]
  have hne : x⁻¹ * t * x ≠ 1 := by
    intro e
    apply ht1
    calc t = x * (x⁻¹ * t * x) * x⁻¹ := by group
      _ = 1 := by rw [e, mul_one, mul_inv_cancel]
  have hv : invol (SH.T i) = true := by
    rw [invol, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · exact List.all_eq_true.2 fun k hk => by
        have e := prep_pc hy hy ⟨k, List.mem_range.1 hk⟩
        rw [hsq, Equiv.Perm.one_apply] at e
        have e' : at5 (pc (SH.T i) (SH.T i)) k = k := e
        rw [e']
        exact Nat.beq_refl k
    · cases e : isId (SH.T i)
      · rfl
      · exact absurd (one_of_isId e hy) hne
  have hc := List.all_eq_true.1 cover i (List.mem_range.2 hi)
  rw [hv, Bool.not_true, Bool.false_or] at hc
  obtain ⟨h, hh, hs⟩ := inClasses_spec hc hy
  have key : ∀ r, x⁻¹ * t * x = h * r * h⁻¹ → ∃ g ∈ P, t = g * r * g⁻¹ ∨
      t = g * (U * r * U⁻¹) * g⁻¹ := by
    intro r e
    have et : t = (x * h) * r * (x * h)⁻¹ := by
      calc t = x * (x⁻¹ * t * x) * x⁻¹ := by group
        _ = (x * h) * r * (x * h)⁻¹ := by rw [e]; group
    rcases (mem_sup_zpowers_iff U_sq U_normalizes).1 (R.mul_mem hxR (mem_sup_left hh)) with
      hp | hp
    · exact ⟨x * h, hp, Or.inl et⟩
    · refine ⟨x * h * U, hp, Or.inr ?_⟩
      rw [et, U_inv]
      have e2 : (x * h * U) * (U * r * U) * (x * h * U)⁻¹ =
          (x * h) * (U * U) * r * (x * h)⁻¹ := by group
      rw [e2, U_mul_U, mul_one]
  have hUr : ∀ r, (∃ q : ℕ, inClasses true true q = true ∧ PRep 28 5 q (U * r * U⁻¹)) →
      ∃ g ∈ P, U * r * U⁻¹ = g * sylP 0 * g⁻¹ ∨ U * r * U⁻¹ = g * U * g⁻¹ :=
    fun r ⟨q, hq, hpq⟩ => inClasses_spec hq hpq
  have hUA : ∃ g ∈ P, U * sylP 0 * U⁻¹ = g * sylP 0 * g⁻¹ ∨ U * sylP 0 * U⁻¹ = g * U * g⁻¹ :=
    hUr _ ⟨_, ucover.1, by
      rw [U_inv, mul_assoc]
      exact prep_pc prep_U (prep_pc (prep_syl 0 (by norm_num)) prep_U)⟩
  have hUB : ∃ g ∈ P, U * U * U⁻¹ = g * sylP 0 * g⁻¹ ∨ U * U * U⁻¹ = g * U * g⁻¹ :=
    hUr _ ⟨_, ucover.2, by
      rw [U_inv, mul_assoc]
      exact prep_pc prep_U (prep_pc prep_U prep_U)⟩
  have fin : ∀ r, (r = sylP 0 ∨ r = U) →
      (∃ g ∈ P, U * r * U⁻¹ = g * sylP 0 * g⁻¹ ∨ U * r * U⁻¹ = g * U * g⁻¹) →
      x⁻¹ * t * x = h * r * h⁻¹ → ∃ g ∈ P, t = g * sylP 0 * g⁻¹ ∨ t = g * U * g⁻¹ := by
    intro r hr0 hU e
    obtain ⟨g, hg, hr | hr⟩ := key r e
    · rcases hr0 with rfl | rfl
      · exact ⟨g, hg, Or.inl hr⟩
      · exact ⟨g, hg, Or.inr hr⟩
    · obtain ⟨g', hg', hr' | hr'⟩ := hU
      · exact ⟨g * g', P.mul_mem hg hg', Or.inl (by rw [hr, hr']; group)⟩
      · exact ⟨g * g', P.mul_mem hg hg', Or.inr (by rw [hr, hr']; group)⟩
  rcases hs with hs | hs
  · exact fin _ (Or.inl rfl) hUA hs
  · exact fin _ (Or.inr rfl) hUB hs

theorem oddA : CFSG.oddCore ↥(P ⊓ centralizer ({sylP 0} : Set (Equiv.Perm (Fin 28)))) = ⊥ := by
  obtain ⟨m1, m2, m3, c1, c2, o1, o2, o3, o4, o5⟩ := witA
  obtain ⟨x, hxP, hx⟩ := ex_P m1
  obtain ⟨h, hhP, hh⟩ := ex_P m2
  obtain ⟨hI, -, hhI⟩ := ex_P m3
  have hr := prep_syl 0 (by norm_num)
  have hxc : x * sylP 0 = sylP 0 * x := eq_of_eqF c1 (prep_pc hx hr) (prep_pc hr hx)
  have hhc : h * sylP 0 = sylP 0 * h := eq_of_eqF c2 (prep_pc hh hr) (prep_pc hr hh)
  have hinv : hI = h⁻¹ := eq_inv_of_mul_eq_one_right (one_of_isId o3 (prep_pc hh hhI))
  have hx1 : x ^ 3 = 1 := by
    rw [pow_three]
    exact one_of_isId o1 (prep_pc hx (prep_pc hx hx))
  have hx3 : orderOf x = 3 := orderOf_eq_prime hx1 (ne_one_of_isId o2 hx)
  have hy : PRep 28 5 (wy xA hA hAI) (x * (h * x * h⁻¹)) := by
    rw [mul_assoc h, ← hinv]
    exact prep_pc hx (prep_pc hh (prep_pc hx hhI))
  have hy4 : orderOf (x * (h * x * h⁻¹)) = 2 ^ (1 + 1) := by
    refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · rw [pow_one, sq]
      exact ne_one_of_isId o5 (prep_pc hy hy)
    · rw [show 2 ^ (1 + 1) = 2 + 2 by norm_num, pow_add, sq]
      exact one_of_isId o4 (prep_pc (prep_pc hy hy) (prep_pc hy hy))
  have hK : Nat.card ↥(P ⊓ centralizer ({sylP 0} : Set (Equiv.Perm (Fin 28)))) = 2 ^ 5 * 3 :=
    classA.1.trans (by norm_num)
  exact oddCore_eq_bot_of_three _ hK (mem_inf.2 ⟨hxP, mem_centralizer_singleton_iff.2 hxc⟩)
    (mem_inf.2 ⟨hhP, mem_centralizer_singleton_iff.2 hhc⟩) hx3 (by rw [hy4]; norm_num)

theorem oddB : CFSG.oddCore ↥(P ⊓ centralizer ({U} : Set (Equiv.Perm (Fin 28)))) = ⊥ := by
  obtain ⟨m1, m2, c1, c2, o1, o2, o3, o4, o5⟩ := witB
  obtain ⟨x, hxP, hx⟩ := ex_P m1
  obtain ⟨h, hhP, hh⟩ := ex_P m2
  have hxc : x * U = U * x := eq_of_eqF c1 (prep_pc hx prep_U) (prep_pc prep_U hx)
  have hhc : h * U = U * h := eq_of_eqF c2 (prep_pc hh prep_U) (prep_pc prep_U hh)
  have hinv : h = h⁻¹ := eq_inv_of_mul_eq_one_right (one_of_isId o3 (prep_pc hh hh))
  have hx1 : x ^ 3 = 1 := by
    rw [pow_three]
    exact one_of_isId o1 (prep_pc hx (prep_pc hx hx))
  have hx3 : orderOf x = 3 := orderOf_eq_prime hx1 (ne_one_of_isId o2 hx)
  have hy : PRep 28 5 (wy xB hB hB) (x * (h * x * h⁻¹)) := by
    rw [mul_assoc h, ← hinv]
    exact prep_pc hx (prep_pc hh (prep_pc hx hh))
  have hy1 : (x * (h * x * h⁻¹)) ^ 2 = 1 := by
    rw [sq]
    exact one_of_isId o4 (prep_pc hy hy)
  have hy2 : orderOf (x * (h * x * h⁻¹)) = 2 := orderOf_eq_prime hy1 (ne_one_of_isId o5 hy)
  have hK : Nat.card ↥(P ⊓ centralizer ({U} : Set (Equiv.Perm (Fin 28)))) = 2 ^ 3 * 3 :=
    classB.1.trans (by norm_num)
  exact oddCore_eq_bot_of_three _ hK (mem_inf.2 ⟨hxP, mem_centralizer_singleton_iff.2 hxc⟩)
    (mem_inf.2 ⟨hhP, mem_centralizer_singleton_iff.2 hhc⟩) hx3 (by rw [hy2])

theorem centralizer_P : centralizer (P : Set (Equiv.Perm (Fin 28))) = ⊥ := by
  refine centralizer_eq_bot_of_transitive 0 (fun x => ?_) (fun x hx => ?_)
  · obtain ⟨i, hi, e⟩ := List.any_eq_true.1 (List.all_eq_true.1 trans x (List.mem_range.2 x.2))
    obtain ⟨σ, hσ, hp⟩ := pe_facts.2.1 i (List.mem_range.1 hi)
    exact ⟨σ, hσ, Fin.ext ((hp 0).symm.trans (Nat.eq_of_beq_eq_true e))⟩
  · have h := List.all_eq_true.1 stab x (List.mem_range.2 x.2)
    have hx0 : Nat.beq (x : ℕ) 0 = false := by
      rw [Bool.eq_false_iff]
      exact fun e => hx (Fin.ext (Nat.eq_of_beq_eq_true e))
    rw [hx0, Bool.false_or] at h
    obtain ⟨i, hi, e⟩ := List.any_eq_true.1 h
    rw [Bool.and_eq_true] at e
    obtain ⟨σ, hσ, hp⟩ := pe_facts.2.1 i (List.mem_range.1 hi)
    refine ⟨σ, hσ, Fin.ext ((hp 0).symm.trans (Nat.eq_of_beq_eq_true e.1)), fun e2 => ?_⟩
    have e3 := hp x
    rw [e2] at e3
    have e4 : at5 (PE.T i) x = x := e3
    have e5 := e.2
    rw [e4, Nat.beq_refl] at e5
    simp at e5

theorem facts : Nat.card P = 6048 ∧ centralizer (P : Set (Equiv.Perm (Fin 28))) = ⊥ ∧
    ∃ u : Equiv.Perm (Fin 28), u ^ 2 = 1 ∧ u ∉ P ∧ (∀ p ∈ P, u * p * u⁻¹ ∈ P) ∧
      ∀ t ∈ P ⊔ zpowers u, orderOf t = 2 →
        CFSG.oddCore ↥(P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 28)))) = ⊥ := by
  refine ⟨pe_facts.1, centralizer_P, U, U_sq, U_not_mem, U_normalizes, fun t ht h2 => ?_⟩
  obtain ⟨g, hg, rfl | rfl⟩ := invol_conj ht h2
  · exact oddCore_inf_centralizer_conj P hg oddA
  · exact oddCore_inf_centralizer_conj P hg oddB

end CertificateChecks.KernelPermCent.U33

end
