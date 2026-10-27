module

public import Certificates.Kernel.KsEight.Reps
public import Certificates.Kernel.KsEight.Cent
public import Certificates.Kernel.CU43Aut.SylGlue
public import Certificates.Kernel.CU43Aut.ModelFacts
public import CFSG.Certificates.Kernel.Spor.CentBoundPowSound
public import CFSG.Certificates.Kernel.Spor.PinvSSound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.Spor.RecGroup
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUKsCheck
public import CFSG.Certificates.Kernel.Spor.BaseMaskSound
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Contra
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB2Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.OutU43Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Stages
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKsEight.CentG8

open Subgroup CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.EvenSporadicStandard.Fin76b.U16
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.CentBound
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.LieType.Multipliers.U43
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut CertificateChecks.KernelKsEight
open CertificateChecks.KernelCU43Aut.CentG CertificateChecks.KernelCU43Aut.SylG

theorem pr_TK (k : Nat) : PR (TK k) (tP k) := Raw.Orb.prep_of_rep (rep_TK k)

theorem pr_TKI {k : Nat} (hk : k < 8) : PR (TKI k) (tP k)⁻¹ := Raw.Orb.prep_of_rep (rep_TKI hk)

theorem cK_TKI {k : Nat} (hk : k < 8) : cK (TKI k) = true := by
  refine CFSG.KS.PinvS.canonK_pinvS (kTK_spec hk).1 ⟨fun i hi => ?_, fun a ha b hb e => ?_⟩
  · have e : pg 10 (mask 10) (TK k) i = (tP k ⟨i, hi⟩ : Nat) := pr_TK k ⟨i, hi⟩
    rw [e]
    exact Fin.isLt _
  · have ea : pg 10 (mask 10) (TK k) a = (tP k ⟨a, ha⟩ : Nat) := pr_TK k ⟨a, ha⟩
    have eb : pg 10 (mask 10) (TK k) b = (tP k ⟨b, hb⟩ : Nat) := pr_TK k ⟨b, hb⟩
    rw [ea, eb] at e
    have := (tP k).injective (Fin.ext e)
    exact congrArg Fin.val this

theorem cK_pidn : cK (pidn 820 10) = true := base_facts.2.1

theorem cK_pc {p q : Nat} (hp : cK p = true) (hq : cK q = true) : cK (pc p q) = true :=
  CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem coset_pr {r k : Nat} (hk : k < 8) (hr : cK r = true) (hin : inPK (pc r (TKI k)) = true) :
    ∃ ρ, PR r ρ ∧ ρ * (tP k)⁻¹ ∈ P := by
  obtain ⟨γ, hγ, hγP⟩ := mem_P (cK_pc hr (cK_TKI hk)) hin
  exact ⟨γ * tP k, pr_of_pc_inv (pr_TKI hk) hγ, by rwa [mul_inv_cancel_right]⟩

theorem pr_conj {g r r1 : Nat} {γ ρ : Equiv.Perm (Fin 820)} (hg : PR g γ) (hr : PR r ρ)
    (e : pc g r = pc r1 g) : PR r1 (γ * ρ * γ⁻¹) := by
  intro y
  have h2 := pr_pc hg hr (γ⁻¹ y)
  rw [e] at h2
  have h1 : pg 10 (mask 10) (pc r1 g) (γ⁻¹ y) =
      pg 10 (mask 10) r1 (pg 10 (mask 10) g (γ⁻¹ y)) := PF.pg_pcomp (by norm_num) (γ⁻¹ y).2
  have e2 : γ (γ⁻¹ y) = y := by
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]
  rw [h1, hg (γ⁻¹ y), e2] at h2
  rw [h2]
  rfl

theorem ord8_facts {r : Nat} {ρ : Equiv.Perm (Fin 820)} (hc : cK r = true) (hr : PR r ρ)
    (h : ord8K r = true) : ρ ^ 8 = 1 ∧ ρ ^ 4 ≠ 1 := by
  unfold ord8K at h
  rw [Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h8, h4⟩ := h
  have p2 := pr_pc hr hr
  have p4 := pr_pc p2 p2
  have n4 : (4 : Nat) = 2 * 2 := rfl
  have n8 : (8 : Nat) = 2 * 2 * 2 := rfl
  have e4 : ρ ^ 4 = ρ * ρ * (ρ * ρ) := by rw [n4, pow_mul, pow_two, pow_two]
  refine ⟨?_, fun h1 => ?_⟩
  · have e8 : ρ ^ 8 = ρ * ρ * (ρ * ρ) * (ρ * ρ * (ρ * ρ)) := by
      rw [n8, pow_mul, pow_mul, pow_two, pow_two, pow_two]
    rw [e8]
    exact pr_eq (pr_pc p4 p4) pr_pidn (Nat.eq_of_beq_eq_true h8)
  · rw [e4] at h1
    rw [h1] at p4
    have hq := canon_eq (cK_pc (cK_pc hc hc) (cK_pc hc hc)) cK_pidn p4 pr_pidn
    rw [hq, Nat.beq_refl] at h4
    exact absurd h4 (by decide)

theorem coset_lt : ∀ j < 8, ks8Coset[j]! < 8 := by decide

theorem rho_ex (j : Nat) : ∃ ρ : Equiv.Perm (Fin 820), j < 8 →
    PR (RK j) ρ ∧ ρ * (tP ks8Coset[j]!)⁻¹ ∈ P ∧ ρ ^ 8 = 1 ∧ ρ ^ 4 ≠ 1 := by
  by_cases hj : j < 8
  · have h := Raw.Orb.allN_iff.1 ksRep j hj
    unfold repK at h
    simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨ρ, hρ, hρP⟩ := coset_pr (coset_lt j hj) h1 h2
    exact ⟨ρ, fun _ => ⟨hρ, hρP, ord8_facts h1 hρ h3⟩⟩
  · exact ⟨1, fun h => absurd h hj⟩

@[expose] noncomputable def rK (j : Nat) : Equiv.Perm (Fin 820) := (rho_ex j).choose

theorem rK_spec {j : Nat} (hj : j < 8) :
    PR (RK j) (rK j) ∧ rK j * (tP ks8Coset[j]!)⁻¹ ∈ P ∧ rK j ^ 8 = 1 ∧ rK j ^ 4 ≠ 1 :=
  (rho_ex j).choose_spec hj

theorem bind_RK {j : Nat} (hj : j < 8) : bindListK 820 10 (RK j) (ks8Reps[j]!).toList = true := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := ksBind
  interval_cases j
  · exact b0
  · exact b1
  · exact b2
  · exact b3
  · exact b4
  · exact b5
  · exact b6
  · exact b7

theorem rep_ks {j : Nat} (hj : j < 8) : Rep 820 ks8Reps[j]! (rK j) := by
  rw [arr_of_bind (bind_RK hj)]
  exact Raw.Orb.rep_unpack (rK_spec hj).1

theorem count_coset {k : Nat} {r : Array Nat} {ρ : Equiv.Perm (Fin 820)} (hr : Rep 820 r ρ) :
    countW (commW (tArr k) [r]) blocks [] =
      Nat.card {g : ↥P // (g : Equiv.Perm (Fin 820)) * tP k * ρ = ρ * (g * tP k)} := by
  classical
  rw [card_eq_countW_P (f := commW (tArr k) [r]) (Pr := fun g => g * tP k * ρ = ρ * (g * tP k))]
  intro w g hw _
  have hH : RepW 820 (tArr k :: w) (g * tP k) := RepW.cons (rep_tArr k) hw
  simp only [commW, List.all_cons, List.all_nil, Bool.and_true]
  exact allLt_comm_iff hH hr

theorem card_coset_cent {k : Nat} {ρ w : Equiv.Perm (Fin 820)} (hw : w * (tP k)⁻¹ ∈ P)
    (hwc : Commute w ρ) :
    Nat.card {g : ↥P // (g : Equiv.Perm (Fin 820)) * tP k * ρ = ρ * (g * tP k)} =
      Nat.card ↥(P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820)))) := by
  refine Nat.card_congr
    { toFun := fun g => ⟨(g.1 : Equiv.Perm (Fin 820)) * tP k * w⁻¹,
        mem_inf.2 ⟨?_, mem_centralizer_singleton_iff.2 ?_⟩⟩
      invFun := fun c => ⟨⟨c.1 * w * (tP k)⁻¹, ?_⟩, ?_⟩
      left_inv := fun g => by
        apply Subtype.ext
        apply Subtype.ext
        change (g.1 : Equiv.Perm (Fin 820)) * tP k * w⁻¹ * w * (tP k)⁻¹ = g.1
        group
      right_inv := fun c => by
        apply Subtype.ext
        change c.1 * w * (tP k)⁻¹ * tP k * w⁻¹ = c.1
        group }
  · have e : (g.1 : Equiv.Perm (Fin 820)) * tP k * w⁻¹ = g.1 * (w * (tP k)⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem g.1.2 (inv_mem hw)
  · exact Commute.mul_left (g.2 : Commute ((g.1 : Equiv.Perm (Fin 820)) * tP k) ρ) hwc.inv_left
  · rw [mul_assoc]
    exact mul_mem (mem_inf.1 c.2).1 hw
  · change Commute (c.1 * w * (tP k)⁻¹ * tP k) ρ
    rw [inv_mul_cancel_right]
    exact Commute.mul_left (mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).2) hwc

theorem witness {j e : Nat} (hj : j < 8) (he : e < 2) :
    ∃ w : Equiv.Perm (Fin 820), w * (tP (2 + 3 * e))⁻¹ ∈ P ∧ Commute w (rK j) := by
  have h := Raw.Orb.allN_iff.1 (Raw.Orb.allN_iff.1 kcW j hj) e he
  unfold cwK at h
  simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨ω, hω, hωP⟩ := coset_pr (k := 2 + 3 * e) (by omega) h1 h3
  have hr := (rK_spec hj).1
  exact ⟨ω, hωP, pr_eq (pr_pc hω hr) (pr_pc hr hω) (Nat.eq_of_beq_eq_true h2)⟩

theorem centKs_eq {j : Nat} (hj : j < 8) :
    centKs ks8Reps[j]! = 4 * Nat.card ↥(P ⊓ centralizer ({rK j} : Set (Equiv.Perm (Fin 820)))) := by
  obtain ⟨w2, hw2, hc2⟩ := witness hj (e := 0) (by norm_num)
  obtain ⟨w5, hw5, hc5⟩ := witness hj (e := 1) (by norm_num)
  have hw7 : w2 * w5 * (tP 7)⁻¹ ∈ P := by
    have e27 : tP 2 * tP 5 = tP 7 := by rw [tP_mul_eq (by norm_num) (by norm_num)]; rfl
    have hN := (mem_normalizer_iff.1 (tP_mem_normalizer 2) (w5 * (tP 5)⁻¹)).1 hw5
    have e : w2 * w5 * (tP 7)⁻¹ = (w2 * (tP 2)⁻¹) * (tP 2 * (w5 * (tP 5)⁻¹) * (tP 2)⁻¹) *
        (tP 2 * tP 5 * (tP 7)⁻¹) := by group
    rw [e, e27, mul_inv_cancel, mul_one]
    exact mul_mem hw2 hN
  have hw0 : (1 : Equiv.Perm (Fin 820)) * (tP 0)⁻¹ ∈ P := by
    rw [tP_zero, inv_one, one_mul]
    exact one_mem _
  have hr := rep_ks hj
  simp only [centKs, vIxL, List.foldl_cons, List.foldl_nil, zero_add]
  rw [count_coset hr, count_coset hr, count_coset hr, count_coset hr,
    card_coset_cent hw0 (Commute.one_left _), card_coset_cent hw2 hc2,
    card_coset_cent hw5 hc5, card_coset_cent hw7 (hc2.mul_left hc5)]
  ring

theorem conj_data {j : Nat} (hj : j < 5) : ∃ γ ∈ P,
    ∀ l < 3, PR (RSj j l) ((γ * rK j * γ⁻¹) ^ (2 ^ l)) := by
  have h := Raw.Orb.allN_iff.1 ksConj j hj
  unfold conjK at h
  simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨hg1, hg2, -, he, e2, e4⟩ := h
  obtain ⟨γ, hγ, hγP⟩ := mem_P hg1 hg2
  have p1 := pr_conj hγ (rK_spec (by omega : j < 8)).1 (Nat.eq_of_beq_eq_true he)
  have p2 : PR (CR (Nat.add (Nat.mul 3 j) 1)) ((γ * rK j * γ⁻¹) * (γ * rK j * γ⁻¹)) := by
    rw [Nat.eq_of_beq_eq_true e2]
    exact pr_pc p1 p1
  have p4 : PR (CR (Nat.add (Nat.mul 3 j) 2)) ((γ * rK j * γ⁻¹) * (γ * rK j * γ⁻¹) *
      ((γ * rK j * γ⁻¹) * (γ * rK j * γ⁻¹))) := by
    rw [Nat.eq_of_beq_eq_true e4]
    exact pr_pc p2 p2
  refine ⟨γ, hγP, fun l hl => ?_⟩
  interval_cases l
  · rw [pow_zero, pow_one]
    exact p1
  · rw [pow_one, pow_two]
    exact p2
  · have e : (γ * rK j * γ⁻¹) ^ 2 ^ 2 = (γ * rK j * γ⁻¹) * (γ * rK j * γ⁻¹) *
        ((γ * rK j * γ⁻¹) * (γ * rK j * γ⁻¹)) := by
      have n4 : (2 : Nat) ^ 2 = 2 * 2 := rfl
      rw [n4, pow_mul, pow_two, pow_two]
    rw [e]
    exact p4

theorem card_le_ub {j c : Nat} {ρ : Equiv.Perm (Fin 820)}
    (hr : ∀ l < 3, PR (RSj j l) (ρ ^ (2 ^ l))) (hu : ubPowOK j c = true) :
    Nat.card ↥(P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820)))) ≤ c := by
  unfold ubPowOK at hu
  rw [Raw.Orb.bAnd_eq, Bool.and_eq_true] at hu
  obtain ⟨hu1, hu2⟩ := hu
  have hup := ubPowK_sound (NS := 13) (CH := 64) KernelU43B.binds C.head C.hl (by norm_num) C.hs
    P_eq_Gen hr hu1
  rw [Nat.eq_of_beq_eq_true hu2] at hup
  refine le_trans (Subgroup.card_le_of_le fun x hx => ?_) hup
  obtain ⟨hxP, hxC⟩ := mem_inf.1 hx
  refine mem_inf.2 ⟨hxP, mem_centralizer_iff.2 ?_⟩
  rintro _ ⟨l, -, rfl⟩
  have hcx : Commute x ρ := mem_centralizer_singleton_iff.1 hxC
  exact (hcx.pow_right _).eq.symm

theorem card_ge_tow {r : Nat} {ρ : Equiv.Perm (Fin 820)} (hr : PR r ρ) {G L : Nat → Nat}
    {nh nl c : Nat} (hl : lbTowK r G L nh nl c = true) :
    c ≤ Nat.card ↥(P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820)))) := by
  unfold lbTowK at hl
  rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, Raw.Orb.bAnd_eq, Bool.and_eq_true] at hl
  obtain ⟨hg, ht, hc⟩ := hl
  have hex : ∀ l, ∃ γ : Equiv.Perm (Fin 820), l < nh →
      PR (G l) γ ∧ γ ∈ P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820))) := by
    intro l
    by_cases hlt : l < nh
    · have hx := Raw.Orb.allN_iff.1 hg l hlt
      unfold inCentK at hx
      rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, Raw.Orb.bAnd_eq, Bool.and_eq_true] at hx
      obtain ⟨h1, h2, h3⟩ := hx
      obtain ⟨γ, hγ, hγP⟩ := mem_P h1 h2
      refine ⟨γ, fun _ => ⟨hγ, mem_inf.2 ⟨hγP, mem_centralizer_singleton_iff.2 ?_⟩⟩⟩
      exact pr_eq (pr_pc hγ hr) (pr_pc hr hγ) (Nat.eq_of_beq_eq_true h3)
    · exact ⟨1, fun h => absurd h hlt⟩
  choose h hh using hex
  have hlow := towerProdK_sound (h := h) (fun l hl => (hh l hl).1) ht
  rw [Nat.eq_of_beq_eq_true hc] at hlow
  have hle : closure (h '' {l | l < nh}) ≤ P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820))) := by
    rw [closure_le]
    rintro _ ⟨l, hl, rfl⟩
    exact (hh l hl).2
  exact hlow.trans (Subgroup.card_le_of_le hle)

theorem card_of_conj {j c : Nat} (hj : j < 5) (hu : ubPowOK j c = true)
    (hlow : ∀ ρ : Equiv.Perm (Fin 820), PR (RSj j 0) ρ →
      c ≤ Nat.card ↥(P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820))))) :
    Nat.card ↥(P ⊓ centralizer ({rK j} : Set (Equiv.Perm (Fin 820)))) = c := by
  obtain ⟨γ, hγP, hr⟩ := conj_data hj
  rw [← card_inf_centralizer_conj hγP]
  have h0 := hr 0 (by norm_num)
  rw [pow_zero, pow_one] at h0
  exact le_antisymm (card_le_ub hr hu) (hlow _ h0)

theorem card_Q {ρ : Equiv.Perm (Fin 820)} (hr : PR (CR 12) ρ) :
    16 ∣ Nat.card ↥(P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820)))) := by
  have hk := kcQ
  rw [Raw.Orb.bAnd_eq, Bool.and_eq_true] at hk
  obtain ⟨hg, he⟩ := hk
  have hex : ∀ a, ∃ γ : Equiv.Perm (Fin 820), a < 3 →
      cK (QG a) = true ∧ PR (QG a) γ ∧ γ ∈ P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820))) := by
    intro a
    by_cases ha : a < 3
    · have hx := Raw.Orb.allN_iff.1 hg a ha
      unfold inCentK at hx
      rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, Raw.Orb.bAnd_eq, Bool.and_eq_true] at hx
      obtain ⟨h1, h2, h3⟩ := hx
      obtain ⟨γ, hγ, hγP⟩ := mem_P h1 h2
      refine ⟨γ, fun _ => ⟨h1, hγ, mem_inf.2 ⟨hγP, mem_centralizer_singleton_iff.2 ?_⟩⟩⟩
      exact pr_eq (pr_pc hγ hr) (pr_pc hr hγ) (Nat.eq_of_beq_eq_true h3)
    · exact ⟨1, fun h => absurd h ha⟩
  choose g hgs using hex
  have hq : ∀ i < 16, (i = 0 → QE i = pidn 820 10) ∧
      (0 < i → QP i / 3 < i ∧ QE i = pc (QE (QP i / 3)) (QG (QP i % 3))) ∧
      (∀ a < 3, QX (3 * i + a) < 16 ∧ pc (QE i) (QG a) = QE (QX (3 * i + a))) ∧
      ∀ k < i, QE i ≠ QE k := by
    intro i hi
    have h := Raw.Orb.allN_iff.1 he i hi
    unfold qElK at h
    simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Raw.Orb.allN_iff] at h
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨fun hi0 => ?_, fun hi0 => ?_, fun a ha => ?_, fun k hk e => ?_⟩
    · subst hi0
      rw [Raw.Orb.bIf_eq, if_pos (Nat.beq_refl 0)] at h1
      exact Nat.eq_of_beq_eq_true h1
    · rw [Raw.Orb.bIf_eq, if_neg (by rw [Raw.Orb.beq_zero_false hi0]; decide), Bool.and_eq_true,
        Nat.blt_eq] at h1
      exact ⟨h1.1, Nat.eq_of_beq_eq_true h1.2⟩
    · have := h2 a ha
      simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at this
      exact ⟨this.1, Nat.eq_of_beq_eq_true this.2⟩
    · have := h3 k hk
      rw [Raw.Orb.bIf_eq, if_pos (by rw [e]; exact Nat.beq_refl _)] at this
      exact absurd this (by decide)
  have hx : ∀ i, ∃ x : Equiv.Perm (Fin 820), i < 16 → cK (QE i) = true ∧ PR (QE i) x := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      by_cases hi : i < 16
      · rcases Nat.eq_zero_or_pos i with rfl | hi0
        · refine ⟨1, fun _ => ?_⟩
          rw [(hq 0 (by norm_num)).1 rfl]
          exact ⟨cK_pidn, pr_pidn⟩
        · obtain ⟨hp, e⟩ := (hq i hi).2.1 hi0
          obtain ⟨y, hy⟩ := ih _ hp
          obtain ⟨hy1, hy2⟩ := hy (by omega)
          obtain ⟨hga, hgp, -⟩ := hgs (QP i % 3) (Nat.mod_lt _ (by norm_num))
          refine ⟨y * g (QP i % 3), fun _ => ?_⟩
          rw [e]
          exact ⟨cK_pc hy1 hga, pr_pc hy2 hgp⟩
      · exact ⟨1, fun h => absurd h hi⟩
  choose xs hxs using hx
  have hcard : Nat.card ↥(closure (g '' {a | a < 3})) = 16 := by
    refine CFSG.KS.RecGroup.card_closure_of_right_record (x := xs) (by norm_num) ?_ ?_ ?_ ?_
    · exact pr_eq (hxs 0 (by norm_num)).2 pr_pidn ((hq 0 (by norm_num)).1 rfl)
    · intro i hi0 hi
      obtain ⟨hp, e⟩ := (hq i hi).2.1 hi0
      refine ⟨QP i / 3, hp, QP i % 3, Nat.mod_lt _ (by norm_num), ?_⟩
      exact pr_eq (hxs i hi).2 (pr_pc (hxs _ (by omega)).2
        (hgs (QP i % 3) (Nat.mod_lt _ (by norm_num))).2.1) e
    · intro i hi a ha
      obtain ⟨hq1, hq2⟩ := (hq i hi).2.2.1 a ha
      exact ⟨_, hq1, pr_eq (hxs _ hq1).2 (pr_pc (hxs i hi).2 (hgs a ha).2.1) hq2.symm⟩
    · intro a ha b hb e
      have e2 := canon_eq (hxs a ha).1 (hxs b hb).1 (hxs a ha).2 (e ▸ (hxs b hb).2)
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact (hq b hb).2.2.2 a h e2.symm
      · exact (hq a ha).2.2.2 b h e2
  have hle : closure (g '' {a | a < 3}) ≤ P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820))) := by
    rw [closure_le]
    rintro _ ⟨a, ha, rfl⟩
    exact (hgs a ha).2.2
  rw [← hcard]
  exact Subgroup.card_dvd_of_le hle

theorem card_E3 {ρ : Equiv.Perm (Fin 820)} (hr : PR (CR 12) ρ) :
    3 ∣ Nat.card ↥(P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820)))) := by
  have h := kcE3
  rw [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Raw.Orb.bAnd_eq,
    Bool.and_eq_true] at h
  obtain ⟨hc, h3, h1⟩ := h
  unfold inCentK at hc
  rw [Raw.Orb.bAnd_eq, Bool.and_eq_true, Raw.Orb.bAnd_eq, Bool.and_eq_true] at hc
  obtain ⟨c1, c2, c3⟩ := hc
  obtain ⟨γ, hγ, hγP⟩ := mem_P c1 c2
  have hmem : γ ∈ P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820))) :=
    mem_inf.2 ⟨hγP, mem_centralizer_singleton_iff.2
      (pr_eq (pr_pc hγ hr) (pr_pc hr hγ) (Nat.eq_of_beq_eq_true c3))⟩
  have hp3 : γ ^ 3 = 1 := by
    have n3 : (3 : Nat) = 2 + 1 := rfl
    have e : γ ^ 3 = γ * (γ * γ) := by rw [n3, pow_succ', pow_two]
    rw [e]
    exact pr_eq (pr_pc hγ (pr_pc hγ hγ)) pr_pidn (Nat.eq_of_beq_eq_true h3)
  have hne : γ ≠ 1 := by
    intro e1
    rw [e1] at hγ
    have := canon_eq c1 cK_pidn hγ pr_pidn
    rw [this, Nat.beq_refl] at h1
    exact absurd h1 (by decide)
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have ho : orderOf γ = 3 := orderOf_eq_prime hp3 hne
  rw [← ho, ← Nat.card_zpowers]
  exact Subgroup.card_dvd_of_le ((zpowers_le).2 hmem)

theorem card_delta {i : Nat} (hi : i < 3) :
    Nat.card ↥(P ⊓ centralizer ({rK (i + 5)} : Set (Equiv.Perm (Fin 820)))) =
      Nat.card ↥(P ⊓ centralizer ({rK (i + 2)} : Set (Equiv.Perm (Fin 820)))) := by
  have h := Raw.Orb.allN_iff.1 kcD i hi
  unfold dwK at h
  simp only [Raw.Orb.strictB_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨γ, hγ, hγP⟩ := mem_P h1 h2
  have r2 := (rK_spec (j := i + 2) (by omega)).1
  have r5 := (rK_spec (j := i + 5) (by omega)).1
  have e := pr_eq (pr_pc hγ (pr_pc pr_dP r2)) (pr_pc r5 (pr_pc hγ pr_dP))
    (Nat.eq_of_beq_eq_true h3)
  have e2 : rK (i + 5) = γ * (dP * rK (i + 2) * dP⁻¹) * γ⁻¹ := by
    calc rK (i + 5) = rK (i + 5) * (γ * dP) * (γ * dP)⁻¹ := by group
      _ = γ * (dP * rK (i + 2)) * (γ * dP)⁻¹ := by rw [← e]
      _ = γ * (dP * rK (i + 2) * dP⁻¹) * γ⁻¹ := by group
  rw [e2, card_inf_centralizer_conj hγP, card_cent_conj_norm dP_mem_normalizer]

theorem four_dvd {ρ : Equiv.Perm (Fin 820)} (hρP : ρ * ρ ∈ P) (h8 : ρ ^ 8 = 1) (h4 : ρ ^ 4 ≠ 1) :
    4 ∣ Nat.card ↥(P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820)))) := by
  have hmem : ρ * ρ ∈ P ⊓ centralizer ({ρ} : Set (Equiv.Perm (Fin 820))) :=
    mem_inf.2 ⟨hρP, mem_centralizer_singleton_iff.2 (mul_assoc ρ ρ ρ)⟩
  have ho : orderOf (ρ * ρ) = 4 := by
    have e : ρ * ρ = ρ ^ 2 := (pow_two ρ).symm
    rw [e]
    have hpow : (ρ ^ 2) ^ 2 ^ 2 = 1 := by rw [← pow_mul]; exact h8
    have hne : (ρ ^ 2) ^ 2 ^ 1 ≠ 1 := by rw [← pow_mul]; exact h4
    have := orderOf_eq_prime_pow (p := 2) (n := 1) hne hpow
    rw [this]
    rfl
  rw [← ho, ← Nat.card_zpowers]
  exact Subgroup.card_dvd_of_le ((zpowers_le).2 hmem)

theorem card_cent0 : Nat.card ↥(P ⊓ centralizer ({rK 0} : Set (Equiv.Perm (Fin 820)))) = 8 :=
  card_of_conj (by norm_num) kcU0 fun _ hρ => card_ge_tow hρ kcL0

theorem card_cent1 : Nat.card ↥(P ⊓ centralizer ({rK 1} : Set (Equiv.Perm (Fin 820)))) = 8 :=
  card_of_conj (by norm_num) kcU1 fun _ hρ => card_ge_tow hρ kcL1

theorem card_cent3 : Nat.card ↥(P ⊓ centralizer ({rK 3} : Set (Equiv.Perm (Fin 820)))) = 16 :=
  card_of_conj (by norm_num) kcU3 fun _ hρ => card_ge_tow hρ kcL3

theorem card_cent4 : Nat.card ↥(P ⊓ centralizer ({rK 4} : Set (Equiv.Perm (Fin 820)))) = 48 := by
  obtain ⟨γ, hγP, hr⟩ := conj_data (j := 4) (by norm_num)
  rw [← card_inf_centralizer_conj hγP]
  have h0 := hr 0 (by norm_num)
  rw [pow_zero, pow_one] at h0
  have hub := card_le_ub hr kcU4
  have h16 := card_Q h0
  have h3 := card_E3 h0
  have h48 : 48 ∣ Nat.card ↥(P ⊓ centralizer ({γ * rK 4 * γ⁻¹} : Set (Equiv.Perm (Fin 820)))) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h16 h3
  have hpos := Nat.card_pos (α := ↥(P ⊓ centralizer ({γ * rK 4 * γ⁻¹} : Set (Equiv.Perm (Fin 820)))))
  obtain ⟨m, hm⟩ := h48
  rw [hm] at hub hpos ⊢
  have : m = 1 := by omega
  rw [this]

theorem card_cent_two :
    (Nat.card ↥(P ⊓ centralizer ({rK 2} : Set (Equiv.Perm (Fin 820)))) = 4 ∨
      Nat.card ↥(P ⊓ centralizer ({rK 2} : Set (Equiv.Perm (Fin 820)))) = 8) ∧
    Nat.card ↥(P ⊓ centralizer ({rK 5} : Set (Equiv.Perm (Fin 820)))) =
      Nat.card ↥(P ⊓ centralizer ({rK 2} : Set (Equiv.Perm (Fin 820)))) := by
  refine ⟨?_, card_delta (i := 0) (by norm_num)⟩
  obtain ⟨γ, hγP, hr⟩ := conj_data (j := 2) (by norm_num)
  rw [← card_inf_centralizer_conj hγP]
  have hub := card_le_ub hr kcU2
  obtain ⟨-, hc0, h8, h4⟩ := rK_spec (j := 2) (by norm_num)
  have e5 : ks8Coset[2]! = 5 := by decide
  rw [e5] at hc0
  have hc : rK 2 * (tP 5)⁻¹ ∈ P := hc0
  have hsq : rK 2 * rK 2 ∈ P := by
    have hN := (mem_normalizer_iff.1 (tP_mem_normalizer 5) (rK 2 * (tP 5)⁻¹)).1 hc
    have e22 : tP 5 * tP 5 = 1 := by rw [tP_mul_eq (by norm_num) (by norm_num)]; rfl
    have e : rK 2 * rK 2 = (rK 2 * (tP 5)⁻¹) * (tP 5 * (rK 2 * (tP 5)⁻¹) * (tP 5)⁻¹) *
        (tP 5 * tP 5) := by group
    rw [e, e22, mul_one]
    exact mul_mem hc hN
  have hc2 : (γ * rK 2 * γ⁻¹) * (γ * rK 2 * γ⁻¹) ∈ P := by
    have e : (γ * rK 2 * γ⁻¹) * (γ * rK 2 * γ⁻¹) = γ * (rK 2 * rK 2) * γ⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hγP hsq) (inv_mem hγP)
  have h8' : (γ * rK 2 * γ⁻¹) ^ 8 = 1 := by rw [conj_pow, h8, mul_one, mul_inv_cancel]
  have h4' : (γ * rK 2 * γ⁻¹) ^ 4 ≠ 1 := by
    rw [conj_pow]
    intro e
    apply h4
    have := congrArg (fun x => γ⁻¹ * x * γ) e
    simpa [mul_assoc] using this
  obtain ⟨m, hm⟩ := four_dvd hc2 h8' h4'
  have hpos := Nat.card_pos (α := ↥(P ⊓ centralizer ({γ * rK 2 * γ⁻¹} : Set (Equiv.Perm (Fin 820)))))
  rw [hm] at hub hpos ⊢
  omega

theorem ks8Check_of (h2 : Nat.card ↥(P ⊓ centralizer ({rK 2} : Set (Equiv.Perm (Fin 820)))) = 4) :
    ks8Check () = true := by
  have hc : ∀ j < 8, 4 * Nat.card ↥(P ⊓ centralizer ({rK j} : Set (Equiv.Perm (Fin 820)))) =
      ks8Cent[j]! := by
    intro j hj
    have h5 := card_cent_two.2
    have h6 := card_delta (i := 1) (by norm_num)
    have h7 := card_delta (i := 2) (by norm_num)
    interval_cases j
    · rw [card_cent0]; rfl
    · rw [card_cent1]; rfl
    · rw [h2]; rfl
    · rw [card_cent3]; rfl
    · rw [card_cent4]; rfl
    · rw [h5, h2]; rfl
    · rw [h6, card_cent3]; rfl
    · rw [h7, card_cent4]; rfl
  simp only [ks8Check, List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
    beq_iff_eq]
  intro j hj
  obtain ⟨-, hP, h8, h4⟩ := rK_spec hj
  have hr := rep_ks hj
  have hk := coset_lt j hj
  refine ⟨⟨⟨⟨isInvA_of_rep hr (rep_invCand hr), ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact (inP_iff (rep_compA hr (rep_tArr_inv hk))).2 hP
  · exact (eqA_iff (rep_powA hr 8) rep_idA).2 h8
  · cases e : eqA 820 (powA 820 ks8Reps[j]! 4) (idA 820)
    · rfl
    · exact absurd ((eqA_iff (rep_powA hr 4) rep_idA).1 e) h4
  · rw [centKs_eq hj, hc j hj]

end CertificateChecks.KernelKsEight.CentG8

end
