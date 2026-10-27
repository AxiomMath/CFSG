module

public import Certificates.Kernel.J2Five.Checks
public import Certificates.Kernel.J2Five.Gens
public import CFSG.Certificates.Kernel.J2FiveSound
public import CFSG.Sporadic.SmallOddCore.J2
public import Certificates.Kernel.Sporadic.OddCore.J2Cent
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

set_option maxRecDepth 400000
set_option exponentiation.threshold 3000

namespace CFSG.KD.J2Five

open Subgroup CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th.Native

noncomputable def σ0 (i : ℕ) : Equiv.Perm (Fin 315) := [j2Gen 0, j2Gen 1, j2u].getD i 1

theorem gen0_eq : getN gen 0 = Certificates.KernelJ2Five.HX.F 0 := by decide +kernel

theorem gen1_eq : getN gen 1 = Certificates.KernelJ2Five.HX.F 1 := by decide +kernel

theorem gen2_eq : getN gen 2 = CertificateChecks.KernelSpor.J2CentT.F 0 := by decide +kernel

theorem prep_of_arr {p : ℕ} {g : Equiv.Perm (Fin 315)}
    (h : CFSG.Monster.B.Co2.Rep 315 (CFSG.KS.Raw.unpack 315 9 p) g) : PRep p g := by
  intro q hq
  have e := h ⟨q, hq⟩
  rw [CFSG.KS.Raw.Orb.unpack_get hq] at e
  exact e

theorem strong_eq {j : ℕ} (hj : j < 2) :
    (CFSG.Sporadic.Schreier.PairNative.j2StrongArrs ())[j]! =
      CFSG.KS.Raw.unpack 315 9 (Certificates.KernelJ2Five.HX.F j) := by
  unfold CFSG.Sporadic.Schreier.PairNative.j2StrongArrs
  rw [getElem!_pos _ j (by simp; omega), Array.getElem_ofFn,
    CFSG.Sporadic.Schreier.PairNative.j2Strong, Certificates.KernelJ2Five.HX.eq]
  exact CFSG.KC.Misc.HexFlat.hexTable_sound Certificates.KernelJ2Five.HX.all j hj

theorem prep_gen {j : ℕ} (hj : j < 2) :
    PRep (getN gen j) (j2Gen j) := by
  have h := rep_j2StrongPerm (by omega : j < 7)
  rw [strong_eq hj] at h
  have e : getN gen j = Certificates.KernelJ2Five.HX.F j := by
    interval_cases j
    · exact gen0_eq
    · exact gen1_eq
  rw [e]
  exact prep_of_arr h

theorem prep_u : PRep (getN gen 2) j2u := by
  obtain ⟨-, h2⟩ := CFSG.KS.Prim.invEqK_sound (n := 315) (w := 9)
    (CFSG.KS.allN_spec CertificateChecks.KernelSpor.OddCore.j2_perms 0 (by norm_num))
  obtain ⟨r1, -⟩ := CFSG.Monster.B.Co2.rep_permOfArr h2
  have e : j2u = CFSG.Monster.B.Co2.permOfArr 315
      (CFSG.KS.Raw.unpack 315 9 (CertificateChecks.KernelSpor.J2CentT.F 0)) := by
    change CFSG.Monster.B.Co2.permOfArr 315 (CFSG.Sporadic.SmallOddCore.Native.natArr
      (j2CentTbl 0)) = _
    rw [CertificateChecks.KernelSpor.OddCore.j2CentTbl_eq (by norm_num)]
  rw [e, gen2_eq]
  exact prep_of_arr r1


theorem hG0 : ∀ i < G0.length, PRep (getN G0 i) (σ0 i) := by
  intro i hi
  have hi3 : i < 3 := by simpa [G0] using hi
  interval_cases i
  · exact prep_gen (j := 0) (by norm_num)
  · exact prep_gen (j := 1) (by norm_num)
  · exact prep_u

theorem gens_facts : σ0 0 * σ0 0 = 1 ∧ σ0 1 * (σ0 1 * σ0 1) = 1 ∧ σ0 2 * σ0 2 = 1 ∧
    PRep (getN gen 3) (σ0 1 * σ0 1) := by
  have h := gens_ok
  rw [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  unfold gensOK at h1
  rw [bAnd_eq, bAnd_eq] at h1
  simp only [Bool.and_eq_true] at h1
  obtain ⟨e0, e1, e2⟩ := h1
  have p0 := hG0 0 (by decide)
  have p1 := hG0 1 (by decide)
  have p2 := hG0 2 (by decide)
  exact ⟨(prep_eq (prep_pm p0 p0) prep_one).1 e0,
    (prep_eq (prep_pm p1 (prep_pm p1 p1)) prep_one).1 e1,
    (prep_eq (prep_pm p2 p2) prep_one).1 e2, prep_of_eq h2 (prep_pm p1 p1)⟩

theorem hGi0 : ∀ i < G0.length, PRep (getN Gi0 i) (σ0 i)⁻¹ := by
  obtain ⟨e0, e1, e2, p3⟩ := gens_facts
  intro i hi
  have hi3 : i < 3 := by simpa [G0] using hi
  interval_cases i
  · rw [inv_eq_of_mul_eq_one_right e0]
    exact hG0 0 (by decide)
  · rw [← eq_inv_of_mul_eq_one_right e1]
    exact p3
  · rw [inv_eq_of_mul_eq_one_right e2]
    exact hG0 2 (by decide)

theorem σ0_memP {i : ℕ} (hi : i < 2) : σ0 i ∈ j2P := by
  interval_cases i
  · exact subset_closure (by simp [σ0])
  · exact subset_closure (by simp [σ0])

theorem j2u_memR : j2u ∈ j2R := (le_sup_right : zpowers j2u ≤ j2R) (mem_zpowers j2u)

theorem σ0_memR {i : ℕ} (hi : i < 3) : σ0 i ∈ j2R := by
  rcases Nat.lt_or_ge i 2 with h | h
  · exact (le_sup_left : j2P ≤ j2R) (σ0_memP h)
  · have : i = 2 := by omega
    subst this
    exact j2u_memR

theorem hpts {pts : List ℕ} (h : pts.all (fun p => decide (p < 315)) = true) :
    ∀ p ∈ pts, p < 315 := by
  intro p hp
  have := List.all_eq_true.1 h p hp
  simpa using this

noncomputable def sv (sw : List (List ℕ)) (j : ℕ) : Equiv.Perm (Fin 315) :=
  wordP σ0 (sw.getD j [])

theorem hS {sw : List (List ℕ)} (h0 : letOK 2 (getW sw 0) = true)
    (h1 : letOK 2 (getW sw 1) = true) :
    ∀ j < [wordN G0 (getW sw 0), wordN G0 (getW sw 1)].length,
      PRep (getN [wordN G0 (getW sw 0), wordN G0 (getW sw 1)] j) (sv sw j) := by
  intro j hj
  have hj2 : j < 2 := by simpa using hj
  have hlt : ∀ k, letOK 2 (getW sw k) = true → ∀ a ∈ getW sw k, a < G0.length := by
    intro k hk a ha
    have := (letOK_iff _ _).1 hk a ha
    change a < 3
    omega
  interval_cases j
  · have := wordN_rep hG0 (hlt 0 h0)
    have e : wordP σ0 (getW sw 0) = sv sw 0 := by rw [getW_eq]; rfl
    rw [e] at this
    exact this
  · have := wordN_rep hG0 (hlt 1 h1)
    have e : wordP σ0 (getW sw 1) = sv sw 1 := by rw [getW_eq]; rfl
    rw [e] at this
    exact this

theorem sv_memP {sw : List (List ℕ)} (h0 : letOK 2 (getW sw 0) = true)
    (h1 : letOK 2 (getW sw 1) = true) {j : ℕ} (hj : j < 2) : sv sw j ∈ j2P := by
  have hw : ∀ k, letOK 2 (getW sw k) = true → ∀ a ∈ sw.getD k [], a < 2 := by
    intro k hk a ha
    rw [← getW_eq] at ha
    exact (letOK_iff _ _).1 hk a ha
  interval_cases j
  · exact wordP_mem j2P (fun i hi => σ0_memP hi) (hw 0 h0)
  · exact wordP_mem j2P (fun i hi => σ0_memP hi) (hw 1 h1)

theorem closure_sv_le {sw : List (List ℕ)} (h0 : letOK 2 (getW sw 0) = true)
    (h1 : letOK 2 (getW sw 1) = true) :
    closure (sv sw '' {j | j < [wordN G0 (getW sw 0), wordN G0 (getW sw 1)].length}) ≤ j2P := by
  rw [closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact sv_memP h0 h1 (by simpa using hj)

theorem part3 : ∃ H : Subgroup (Equiv.Perm (Fin 315)), H ≤ j2P ∧ Nat.card H = 27 ∧
    ∀ y ∈ H, y ≠ 1 → ∃ u ∈ j2P, u * u = 1 ∧ y * u * y⁻¹ * (y * u * y⁻¹) = 1 ∧
      u * (y * u * y⁻¹) = y * u * y⁻¹ * u ∧ y * (y * u * y⁻¹) * y⁻¹ = u * (y * u * y⁻¹) ∧
      y * u * y⁻¹ ≠ u := by
  have h := ck3_ok
  unfold ck3 at h
  rw [bAnd_eq, bAnd_eq, strictB_eq', strictB_eq', bAnd_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h0, h1, hg, hk⟩ := h
  obtain ⟨hmem, hcard, -, hrep, hi0, hx0⟩ :=
    grpOK_sound (sv s3) (hS h0 h1) (hpts (by decide +kernel)) hg
  have hlen : x3.length = 27 := by decide +kernel
  refine ⟨_, closure_sv_le h0 h1, by rw [hcard, hlen], ?_⟩
  intro y hy hy1
  obtain ⟨i, hi, rfl⟩ := (hmem y).1 hy
  have hii : i ≠ id3 := by
    rintro rfl
    exact hy1 hx0
  have hk' := CFSG.KS.allN_spec hk i (by rw [lenW_eq]; exact hi)
  rw [bIf_true_eq, bAnd_eq] at hk'
  simp only [Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq, hii, false_or] at hk'
  obtain ⟨hl, hko⟩ := hk'
  have hw : ∀ a ∈ getW k3 i, a < 2 := (letOK_iff _ _).1 hl
  have hU := wordN_rep hG0 (w := getW k3 i) (fun a ha => by
    have := (letOK_iff _ _).1 hl a ha
    change a < 3
    omega)
  obtain ⟨-, e1, e2, e3, e4, e5⟩ := kleinOK_sound (hrep i hi) hU hko
  exact ⟨_, wordP_mem j2P (fun i hi => σ0_memP hi) hw, e1, e2, e3, e4, e5⟩


theorem klein : ∀ x ∈ j2P, orderOf x = 3 → ∃ u₁ ∈ j2P, ∃ u₂ ∈ j2P, u₁ * u₁ = 1 ∧
    u₂ * u₂ = 1 ∧ u₁ * u₂ = u₂ * u₁ ∧ x * u₁ * x⁻¹ = u₂ ∧ x * u₂ * x⁻¹ = u₁ * u₂ ∧
      u₂ ≠ u₁ := by
  intro x hx ho
  obtain ⟨H, hHP, hH, hK⟩ := part3
  obtain ⟨g, hg, hgH⟩ := exists_conj_mem Nat.prime_three hHP (k := 3) (m := 22400)
    (by norm_num [hH]) (by norm_num [card_j2P]) (by norm_num) hx ho
  have hy1 : g⁻¹ * x * g ≠ 1 := by
    intro e
    have : x = 1 := by
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [e]; group
    rw [this, orderOf_one] at ho
    exact absurd ho (by norm_num)
  obtain ⟨u, hu, e1, e2, e3, e4, e5⟩ := hK _ hgH hy1
  set y := g⁻¹ * x * g with hydef
  have hxy : x = g * y * g⁻¹ := by rw [hydef]; group
  refine ⟨g * u * g⁻¹, j2P.mul_mem (j2P.mul_mem hg hu) (j2P.inv_mem hg),
    x * (g * u * g⁻¹) * x⁻¹, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · refine j2P.mul_mem (j2P.mul_mem hx (j2P.mul_mem (j2P.mul_mem hg hu) (j2P.inv_mem hg)))
      (j2P.inv_mem hx)
  · calc g * u * g⁻¹ * (g * u * g⁻¹) = g * (u * u) * g⁻¹ := by group
      _ = 1 := by rw [e1]; group
  · rw [hxy]
    calc g * y * g⁻¹ * (g * u * g⁻¹) * (g * y * g⁻¹)⁻¹ *
          (g * y * g⁻¹ * (g * u * g⁻¹) * (g * y * g⁻¹)⁻¹) =
          g * (y * u * y⁻¹ * (y * u * y⁻¹)) * g⁻¹ := by group
      _ = 1 := by rw [e2]; group
  · rw [hxy]
    calc g * u * g⁻¹ * (g * y * g⁻¹ * (g * u * g⁻¹) * (g * y * g⁻¹)⁻¹) =
          g * (u * (y * u * y⁻¹)) * g⁻¹ := by group
      _ = g * (y * u * y⁻¹ * u) * g⁻¹ := by rw [e3]
      _ = _ := by group
  · rw [hxy]
    calc g * y * g⁻¹ * (g * y * g⁻¹ * (g * u * g⁻¹) * (g * y * g⁻¹)⁻¹) * (g * y * g⁻¹)⁻¹ =
          g * (y * (y * u * y⁻¹) * y⁻¹) * g⁻¹ := by group
      _ = g * (u * (y * u * y⁻¹)) * g⁻¹ := by rw [e4]
      _ = _ := by group
  · rw [hxy]
    intro e
    apply e5
    have e' : g * (y * u * y⁻¹) * g⁻¹ = g * u * g⁻¹ := by
      rw [← e]
      group
    calc y * u * y⁻¹ = g⁻¹ * (g * (y * u * y⁻¹) * g⁻¹) * g := by group
      _ = g⁻¹ * (g * u * g⁻¹) * g := by rw [e']
      _ = u := by group

theorem card_j2R : Nat.card j2R = 1209600 :=
  ctuc_j2_normalizing_involution_permutation_model.2.2.2.2.2.2.2.2.1

theorem closure_σ0_le : closure (σ0 '' {i | i < G0.length}) ≤ j2R := by
  rw [closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact σ0_memR (by simpa [G0] using hi)

theorem card_cent_conj {k : Equiv.Perm (Fin 315)} (hk : k ∈ j2R) (w : Equiv.Perm (Fin 315)) :
    Nat.card ↥(j2R ⊓ centralizer ({k⁻¹ * w * k} : Set (Equiv.Perm (Fin 315)))) =
      Nat.card ↥(j2R ⊓ centralizer ({w} : Set (Equiv.Perm (Fin 315)))) := by
  have e := inf_centralizer_conj j2R (j2R.inv_mem hk) w
  rw [inv_inv] at e
  rw [e, Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective]

theorem card_le_of_orb {z : ℕ} {Z : Equiv.Perm (Fin 315)} (hz : PRep z Z) {pts : List ℕ}
    (hp : ∀ p ∈ pts, p < 315) {R : List (ℕ × List ℕ)} {m : ℕ}
    (h : orbOK G0 Gi0 z pts R m = true) :
    Nat.card ↥(j2R ⊓ centralizer ({Z} : Set (Equiv.Perm (Fin 315)))) * m ≤ 1209600 := by
  unfold orbOK at h
  rw [bAnd_eq, strictB_eq', Bool.and_eq_true, Nat.beq_eq, lenR_eq] at h
  obtain ⟨hl, hc⟩ := h
  have h1 := conjOK_sound (G := G0) (Gi := Gi0) σ0 Z rfl hG0 hGi0 hz hp hc
  have h2 : Nat.card {y | ∃ k ∈ closure (σ0 '' {i | i < G0.length}), y = k⁻¹ * Z * k} ≤
      Nat.card {y | ∃ k ∈ j2R, y = k⁻¹ * Z * k} := by
    apply Nat.card_mono (Set.toFinite _)
    rintro y ⟨k, hk, rfl⟩
    exact ⟨k, closure_σ0_le hk, rfl⟩
  rw [← card_j2R, ← hl]
  exact card_cent_le j2R (h1.trans h2)

theorem part5 : ∃ S : Subgroup (Equiv.Perm (Fin 315)), S ≤ j2P ∧ Nat.card S = 25 ∧
    ∀ y ∈ S, y ≠ 1 → ¬ 8 ∣ Nat.card ↥(j2R ⊓ centralizer ({y} : Set (Equiv.Perm (Fin 315)))) := by
  have h := ck5_ok
  unfold ck5 at h
  rw [bAnd_eq, bAnd_eq, strictB_eq', strictB_eq', bAnd_eq, bAnd_eq, strictB_eq', strictB_eq',
    bAnd_eq, bAnd_eq, strictB_eq'] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h0, h1, hg, hab, hconj, hl3, ht⟩ := h
  rw [bAnd_eq, bAnd_eq, bIf_eq] at ht
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht
  obtain ⟨ht3, ht1, htc⟩ := ht
  obtain ⟨hmem, hcard, -, hrep, hi0, hx0⟩ :=
    grpOK_sound (sv s5) (hS h0 h1) (hpts (by decide +kernel)) hg
  have hlen : x5.length = 25 := by decide +kernel
  set S := closure (sv s5 '' {j | j < [wordN G0 (getW s5 0), wordN G0 (getW s5 1)].length})
    with hSdef
  have hSP : S ≤ j2P := closure_sv_le h0 h1
  have hSR : S ≤ j2R := hSP.trans le_sup_left
  have p0 := hS h0 h1 0 (by simp)
  have p1 := hS h0 h1 1 (by simp)
  have hcomm : sv s5 0 * sv s5 1 = sv s5 1 * sv s5 0 :=
    (prep_eq (prep_pm p0 p1) (prep_pm p1 p0)).1 hab
  have hcen : ∀ z ∈ S, S ≤ centralizer ({z} : Set (Equiv.Perm (Fin 315))) := by
    have hgen : ∀ j < 2, ∀ j' < 2, sv s5 j * sv s5 j' = sv s5 j' * sv s5 j := by
      intro j hj j' hj'
      interval_cases j <;> interval_cases j' <;> first | rfl | exact hcomm | exact hcomm.symm
    have hS1 : S ≤ centralizer (sv s5 '' {j | j < 2}) := by
      rw [hSdef, closure_le]
      rintro _ ⟨j, hj, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_iff]
      rintro _ ⟨j', hj', rfl⟩
      exact hgen j' hj' j (by simpa using hj)
    intro z hz
    rw [hSdef, closure_le]
    rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact mem_centralizer_iff.1 (hS1 hz) (sv s5 j) ⟨j, by simpa using hj, rfl⟩
  have hzA : zA < x5.length := by decide +kernel
  have hzC : zC < x5.length := by decide +kernel
  set A := wordP (sv s5) (x5.getD zA []) with hA
  set Cc := wordP (sv s5) (x5.getD zC []) with hC
  have hAS : A ∈ S := (hmem A).2 ⟨zA, hzA, rfl⟩
  have hCS : Cc ∈ S := (hmem Cc).2 ⟨zC, hzC, rfl⟩
  have hdvd : ∀ z ∈ S, 25 ∣ Nat.card ↥(j2R ⊓ centralizer ({z} : Set (Equiv.Perm (Fin 315)))) :=
    fun z hz => by
      have := Subgroup.card_dvd_of_le (le_inf hSR (hcen z hz))
      rwa [hcard, hlen] at this
  have hpos : ∀ z : Equiv.Perm (Fin 315),
      0 < Nat.card ↥(j2R ⊓ centralizer ({z} : Set (Equiv.Perm (Fin 315)))) :=
    fun z => Nat.card_pos
  have hAle : Nat.card ↥(j2R ⊓ centralizer ({A} : Set (Equiv.Perm (Fin 315)))) * 2017 ≤
      1209600 := card_le_of_orb (hrep zA hzA) (hpts (by decide +kernel)) orbA_ok
  have hCle : Nat.card ↥(j2R ⊓ centralizer ({Cc} : Set (Equiv.Perm (Fin 315)))) * 6049 ≤
      1209600 := card_le_of_orb (hrep zC hzC) (hpts (by decide +kernel)) orbC_ok
  have hT := wordN_rep hG0 (w := t3) (fun a ha => by
    have := (letOK_iff _ _).1 hl3 a ha
    simpa [G0] using this)
  have hPA := hrep zA hzA
  have hT3 : wordP σ0 t3 * (wordP σ0 t3 * wordP σ0 t3) = 1 :=
    (prep_eq (prep_pm hT (prep_pm hT hT)) prep_one).1 ht3
  have hT1 : wordP σ0 t3 ≠ 1 := fun e => by
    rw [(prep_eq hT prep_one).2 e] at ht1
    exact Bool.false_ne_true ht1.symm
  have hTA : wordP σ0 t3 * A = A * wordP σ0 t3 := (prep_eq (prep_pm hT hPA) (prep_pm hPA hT)).1 htc
  have h3 : 3 ∣ Nat.card ↥(j2R ⊓ centralizer ({A} : Set (Equiv.Perm (Fin 315)))) := by
    have hTR : wordP σ0 t3 ∈ j2R :=
      wordP_mem j2R (fun i hi => σ0_memR hi) (fun a ha => (letOK_iff _ _).1 hl3 a ha)
    have hTC : wordP σ0 t3 ∈ j2R ⊓ centralizer ({A} : Set (Equiv.Perm (Fin 315))) :=
      mem_inf.2 ⟨hTR, mem_centralizer_singleton_iff.2 hTA⟩
    have ho : orderOf (wordP σ0 t3) = 3 := by
      apply orderOf_eq_prime
      · rw [pow_succ, pow_two, mul_assoc]
        exact hT3
      · exact hT1
    have := orderOf_dvd_natCard (⟨_, hTC⟩ : ↥(j2R ⊓ centralizer ({A} : Set _)))
    rwa [orderOf_mk, ho] at this
  have hAok : ¬ 8 ∣ Nat.card ↥(j2R ⊓ centralizer ({A} : Set (Equiv.Perm (Fin 315)))) := by
    intro h8
    have := hdvd A hAS
    have := hpos A
    omega
  have hCok : ¬ 8 ∣ Nat.card ↥(j2R ⊓ centralizer ({Cc} : Set (Equiv.Perm (Fin 315)))) := by
    intro h8
    have := hdvd Cc hCS
    have := hpos Cc
    omega
  refine ⟨S, hSP, by rw [hcard, hlen], ?_⟩
  intro y hy hy1
  obtain ⟨i, hi, rfl⟩ := (hmem y).1 hy
  have hii : i ≠ id5 := by
    rintro rfl
    exact hy1 hx0
  have hc := CFSG.KS.allN_spec hconj i (by rw [lenW_eq]; exact hi)
  rw [bIf_true_eq] at hc
  simp only [Bool.or_eq_true, Nat.beq_eq, hii, false_or] at hc
  obtain ⟨hw, he⟩ := conjTo_sound hG0 rfl (hrep i hi) (hrep zA hzA) (hrep zC hzC) hc
  have hhR : wordP σ0 (getR h5 i).2 ∈ j2R :=
    wordP_mem j2R (fun i hi => σ0_memR hi) hw
  rw [← card_cent_conj hhR, he]
  split_ifs
  · exact hAok
  · exact hCok

theorem not_eight_dvd : ∀ x ∈ j2P, orderOf x = 5 →
    ¬ 8 ∣ Nat.card ↥(j2R ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 315)))) := by
  intro x hx ho
  obtain ⟨S, hSP, hS25, hK⟩ := part5
  obtain ⟨g, hg, hgS⟩ := exists_conj_mem Nat.prime_five hSP (k := 2) (m := 24192)
    (by norm_num [hS25]) (by norm_num [card_j2P]) (by norm_num) hx ho
  have hy1 : g⁻¹ * x * g ≠ 1 := by
    intro e
    have : x = 1 := by
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = 1 := by rw [e]; group
    rw [this, orderOf_one] at ho
    exact absurd ho (by norm_num)
  rw [← card_cent_conj ((le_sup_left : j2P ≤ j2R) hg)]
  exact hK _ hgS hy1

theorem facts : (∀ x ∈ j2P, orderOf x = 3 → ∃ u₁ ∈ j2P, ∃ u₂ ∈ j2P, u₁ * u₁ = 1 ∧
      u₂ * u₂ = 1 ∧ u₁ * u₂ = u₂ * u₁ ∧ x * u₁ * x⁻¹ = u₂ ∧ x * u₂ * x⁻¹ = u₁ * u₂ ∧
        u₂ ≠ u₁) ∧
    (∀ x ∈ j2P, orderOf x = 5 →
      ¬ 8 ∣ Nat.card ↥(j2R ⊓ centralizer ({x} : Set (Equiv.Perm (Fin 315))))) :=
  ⟨klein, not_eight_dvd⟩

end CFSG.KD.J2Five

end
