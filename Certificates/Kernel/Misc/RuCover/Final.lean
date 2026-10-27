module

public import Certificates.Kernel.Misc.RuCover.Checks
public import CFSG.Certificates.Kernel.Misc.RuCoverSound
public import CFSG.Quasithin.Vol2.KGFactC31RuCoverLift
public import CFSG.Quasithin.Vol2.KGFactC31RuBase
public import CFSG.Sporadic.Schreier.RuCentersMain
public import CFSG.Certificates.Kernel.SporSch.ChainKPack
public import Certificates.Kernel.CosetJ.RhoRu
public import Certificates.Kernel.CosetJ.RhoCover
public import Certificates.Kernel.CosetJ.RhoPerm
public import Certificates.Kernel.SporSch.Ru.Gens
public import Certificates.Kernel.SporSch.Ru.B1E
public import Certificates.Certificate15024
public import Certificates.Certificate15025
public import Certificates.Certificate15026
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Sporadic.Recognition.RuMultiplierInputs
import all CFSG.Sporadic.Presentation.RuExactInputs
import all CFSG.LieType.Multipliers.CoverWords
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.FactsB2Inputs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.Faithful
public import CFSG.Quasithin.Vol2.KGFactC31RuBaseBase
public import CFSG.Quasithin.Vol2.KGFactC31RuRefK
public import CFSG.Sporadic.Schreier.RuLGroup
public import CFSG.Sporadic.Schreier.RuPair
public import CFSG.Sporadic.Schreier.TitsOther
public import Certificates.Certificate7233Base

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelMisc.RuCover

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.Tits CFSG.Sporadic.Recognition.RuMultiplier
  CFSG.Sporadic.RuSchreier CFSG.EvenSporadicStandard.TwoRu CFSG.Sporadic.J4.QT
  CFSG.Sporadic.SmallF2 CFSG.Quasithin.KGC31.RuCover CFSG.Quasithin.KGC31.Ru
  CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Certificates.CosetEnumeration
  CFSG.KC.Misc.RuCover CFSG.KC.MiscCoset CFSG.KC.Misc.RuInv CFSG.KS.Raw.Orb
  CertificateChecks.KernelSporSch CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuScan

theorem ne_of_notB {a b : ℕ} (h : Act.notB (Nat.beq a b) = true) : a ≠ b := by
  intro hab
  subst hab
  rw [Nat.beq_refl] at h
  exact Bool.false_ne_true h

@[expose] noncomputable def ch4060 (P : Nat) (w : List Int) : Bool :=
  Act.allR (nat_lit 0) (nat_lit 4) fun b =>
    Nat.beq (apP P (walkP RuG.A0I (RuT4060.L 0) RuG.A1I (RuT4060.L 1) w b)) b

theorem ch4060E : ∀ k < 7, ch4060 (RuB1K.EA k) (etaW (eCode.getD k 0) 3) = true := by
  decide +kernel

theorem ch4060N : ch4060 RuG.Ns0 (nW.getD 0 []) = true ∧ ch4060 RuG.Ns1 (nW.getD 1 []) = true := by
  decide +kernel

theorem letters_eW : ∀ i < 3, Native.lettersOK 2 (eW.getD i []) = true := by decide +kernel

theorem letters_nW : ∀ j < 2, Native.lettersOK 2 (nW.getD j []) = true := by decide +kernel

theorem letters_pairs : ∀ k < 12, Native.lettersOK 2 (eqPair k).1 = true ∧
    Native.lettersOK 2 (eqPair k).2 = true := by decide +kernel

theorem letters_etaW : ∀ c < 8, Native.lettersOK 2 (etaW c 3) = true := by decide +kernel

theorem letters_etaE : ∀ k < 7, Native.lettersOK 2 (etaW (eCode.getD k 0) 3) = true := by
  decide +kernel

theorem gc_eq' : gc = 3 := by decide

theorem ruP1_eq : ruP1 = toLetters gc KernelCosetJ.RuSurjT.W.toArray[1]! := by
  have h := CFSG.KC.SurjK.wordsK_sound KernelCosetJ.RhoRu.surj_words
  rw [← KernelCosetJ.RuSurjT.eq] at h
  have e : CFSG.Sporadic.Bridge.SurjD.Native.ruSpec.surjWords =
      CFSG.Sporadic.Bridge.SurjD.Native.parseWords
        CFSG.Sporadic.Bridge.SurjD.Native.ruSurjText := rfl
  rw [ruP1, e, h]

theorem q0 : ruP0.map letterCode = Q0 := by
  rw [KernelCosetJ.RhoRu.ruP0_eq]
  decide +kernel

theorem q0i : (FreeGroup.invRev ruP0).map letterCode = Q0I := by
  rw [KernelCosetJ.RhoRu.ruP0_eq]
  decide +kernel

theorem q1 : ruP1.map letterCode = Q1 := by
  rw [ruP1_eq]
  decide +kernel

theorem q1i : (FreeGroup.invRev ruP1).map letterCode = Q1I := by
  rw [ruP1_eq]
  decide +kernel

theorem letters_p0 : Native.lettersOK gc (zword ruP0) = true := by
  rw [KernelCosetJ.RhoRu.ruP0_eq]
  decide +kernel

theorem letters_p1 : Native.lettersOK gc (zword ruP1) = true := by
  rw [ruP1_eq]
  decide +kernel

theorem rep_A (hRho : ruRhoCheck = true) : ∃ σ : Fin 3 → Equiv.Perm (Fin 16240),
    Act.Rep CFSG.KAct.RuRho.A 3 16240 σ ∧ ∀ g : Fin 3, ruRhoGen g = (σ g)⁻¹ := by
  have hpt := Act.coverPointOK_of_allR CFSG.KAct.RuRho.all
  have hpt' : ∀ x < 16240, Act.coverPointOK CFSG.KAct.RuRho.A CFSG.KAct.RuRho.B gc 16240
      CFSG.KAct.RuRho.R CFSG.KAct.RuRho.W x = true := by
    rw [gc_eq']
    exact hpt
  obtain ⟨σ, hσ, -⟩ := KernelCosetJ.RhoCover.cover_trivial _ ruCommWord [] KernelCosetJ.RhoRu.hR
    KernelCosetJ.RhoRu.hW hpt'
  have hb := Act.allR_spec KernelCosetJ.RhoRu.bind
  have hrep : ∀ g (hg : g < 3), Rep 16240 ruRhoArrs[g]! (σ ⟨g, gc_eq' ▸ hg⟩)⁻¹ := by
    intro g hg x
    have hx := hb x.val (Nat.zero_le _) (by simp)
    simp only [Act.andB_eq, Bool.and_eq_true] at hx
    rw [KernelCosetJ.RhoRu.ruRhoArrs_get hg, unpack, getElem!_ofFn_nat _ x.2]
    have hr := (hσ ⟨g, gc_eq' ▸ hg⟩ x).2
    simp only [gc_eq'] at hr
    interval_cases g
    · exact (Nat.eq_of_beq_eq_true hx.1).symm.trans hr
    · exact (Nat.eq_of_beq_eq_true hx.2.1).symm.trans hr
    · exact (Nat.eq_of_beq_eq_true hx.2.2).symm.trans hr
  refine ⟨σ, hσ, fun g => ?_⟩
  have h1 := rep_of_allPermsOK (rho_facts hRho).1 (j := g.val) (by
    have : ruRhoArrs.size = 3 := rfl
    omega)
  exact h1.unique (hrep g.val g.2)

theorem eta_congr' {G : Type*} [Group G] {u u' : ℕ → G} (c : ℕ) :
    ∀ m, (∀ j < m, u j = u' j) → eta u m c = eta u' m c
  | 0, _ => by simp [eta]
  | m + 1, h => by
    rw [eta_succ, eta_succ, eta_congr' c m fun j hj => h j (by omega), h m (by omega)]

theorem pElt_append (u v : List ℤ) : pElt (u ++ v) = pElt u * pElt v := wordIn_append _ _ _ _

theorem pElt_nil : pElt [] = 1 := by simp [pElt, wordIn, toLetters]

theorem pElt_etaW (c : ℕ) : ∀ m, pElt (etaW c m) = eta (fun i => pElt (eW.getD i [])) m c
  | 0 => by
    rw [show etaW c 0 = [] from rfl, pElt_nil]
    simp [eta]
  | m + 1 => by
    rw [etaW_succ, pElt_append, pElt_etaW c m, eta_succ]
    cases h : c.testBit m
    · simp [pElt_nil]
    · simp

theorem pElt_11 : pElt [1, 1] = ruP0E ^ 2 := by
  rw [show ([1, 1] : List ℤ) = [1] ++ [1] from rfl, pElt_append, pow_two]
  have e : pElt [1] = ruP0E := by
    rw [pElt, wordIn_cons1, ← pElt, pElt_nil, mul_one]
    simp [pGen]
  rw [e]

section Main


theorem prep_A0 : PRep 4060 12 (RuT4060.L 0) ruA0 := by
  have h : Rep 4060 (unpack 4060 12 RuG.A0) ruA0 := by rw [← RuG.a0_eq]; exact rep_ruA0
  exact prep_of_rep h

theorem prep_A1 : PRep 4060 12 (RuT4060.L 1) ruA1 := by
  have h : Rep 4060 (unpack 4060 12 RuG.A1) ruA1 := by rw [← RuG.a1_eq]; exact rep_ruA1
  exact prep_of_rep h

theorem prep_A0I : PRep 4060 12 RuG.A0I ruA0⁻¹ :=
  CFSG.KS.SporSch.MOC.prep_inv_of_permOK prep_A0 RuG.pA0

theorem prep_A1I : PRep 4060 12 RuG.A1I ruA1⁻¹ :=
  CFSG.KS.SporSch.MOC.prep_inv_of_permOK prep_A1 RuG.pA1

theorem eq_of_base {q h : Equiv.Perm (Fin 4060)} (hq : q ∈ ruP) (hh : h ∈ ruP)
    (hb : ∀ b : Fin 4060, b.val < 4 → q (h⁻¹ b) = b) : q = h := by
  have h1 := ruJoin_baseFaithful (q * h⁻¹) (ruP.mul_mem hq (ruP.inv_mem hh)) (fun x hx => by
    have hlt : ∀ y ∈ ruJoinBase, y < 4 := by decide
    have hx' : x.val < 4 := hlt _ hx
    rw [Equiv.Perm.mul_apply]
    exact hb x hx')
  exact mul_inv_eq_one.mp h1

noncomputable abbrev gP : CFSG.Sporadic.Recognition.RuMultiplier.RuCover →* Equiv.Perm (Fin 4060) :=
  ruJtoP.comp (ruπ Certificates.certificate15024)

theorem gP_mem (x : CFSG.Sporadic.Recognition.RuMultiplier.RuCover) : gP x ∈ ruP := by
  rw [← ruJtoP_range]
  exact ⟨_, rfl⟩

theorem walkP_gP : ∀ w : List ℤ, Native.lettersOK 2 w = true → ∀ x : Fin 4060,
    walkP RuG.A0I (RuT4060.L 0) RuG.A1I (RuT4060.L 1) w x.val = ((gP (pElt w))⁻¹ x).val := by
  have hTab : RuTabFact := Certificates.certificate15024
  have e0 : gP (pGen 0) = ruA0 := ruJtoP_p0 hTab
  have e1 : gP (pGen 1) = ruA1 := ruJtoP_p1 hTab
  intro w hw x
  have h := walkP_sound (f := fun h => gP (pGen h)) (P₀ := RuG.A0I) (P₁ := RuT4060.L 0)
    (P₂ := RuG.A1I) (P₃ := RuT4060.L 1) (by simp only [e0]; exact prep_A0I)
    (by simp only [e0]; exact prep_A0) (by simp only [e1]; exact prep_A1I)
    (by simp only [e1]; exact prep_A1) w hw x
  rw [h, pElt, map_wordIn]
  rfl

theorem walkW_rho : ∀ w : List ℤ, Native.lettersOK 2 w = true → ∀ x : Fin 16240,
    walkW CFSG.KAct.RuRho.A Q0 Q0I Q1 Q1I w x.val =
      ((ruRho' Certificates.certificate15025 (pElt w))⁻¹ x).val := by
  have hRho : ruRhoCheck = true := Certificates.certificate15025
  obtain ⟨σ, hσ, hgen⟩ := rep_A hRho
  have hs : ∀ u : List (Fin gc × Bool), ruRho' hRho (ruWE u) =
      signedProd (fun g => (σ g)⁻¹) u := by
    intro u
    rw [ruRho'_ruWE, ← CFSG.Sporadic.Recognition.CoverTransfer.lift_mk_eq_wordIn,
      lift_mk_eq_signedProd]
    congr 1
    funext g
    exact hgen g
  have h0 : ruRho' hRho (pGen 0) = signedProd (fun g => (σ g)⁻¹) ruP0 := by
    rw [← hs, pGen, if_pos rfl]
    rfl
  have h1 : ruRho' hRho (pGen 1) = signedProd (fun g => (σ g)⁻¹) ruP1 := by
    rw [← hs, pGen, if_neg one_ne_zero]
  exact walkW_sound hσ (ruRho' hRho) (gs := pGen) h0 h1 q0 q0i q1 q1i

theorem eq_of_walks {x y : List ℤ} (hx : Native.lettersOK 2 x = true)
    (hy : Native.lettersOK 2 y = true) (h : eqOK CFSG.KAct.RuRho.A Q0 Q0I Q1 Q1I RuG.A0I
      (RuT4060.L 0) RuG.A1I (RuT4060.L 1) x y = true) : pElt x = pElt y := by
  have hTab : RuTabFact := Certificates.certificate15024
  have hRho : ruRhoCheck = true := Certificates.certificate15025
  have hL0 := Certificates.certificate15026
  obtain ⟨hfin, hle⟩ := card_ruCover_le hTab hL0
  unfold eqOK at h
  rw [Act.andB_eq, Bool.and_eq_true] at h
  obtain ⟨h16, h4⟩ := h
  have hb := Act.allR_spec h4
  have hg : gP (pElt y) = gP (pElt x) := by
    refine eq_of_base (gP_mem _) (gP_mem _) fun b hb4 => ?_
    have e := Nat.eq_of_beq_eq_true (hb b.val (Nat.zero_le _) (by omega))
    rw [walkP_gP x hx b, walkP_gP y hy b] at e
    rw [Fin.ext e]
    simp
  have hπ : ruπ hTab (pElt x) = ruπ hTab (pElt y) := ruJtoP_injective hg.symm
  have hz : ruπ hTab (ruP0E ^ 2) = 1 := by rw [map_pow, ruπ_ruP0E, a_sq]
  have hzp : ruRho' hRho (ruP0E ^ 2) 0 ≠ 0 := by
    intro h0
    have hne : wW [1, 1] 0 ≠ 0 := ne_of_notB ch7257z
    have e := walkW_rho [1, 1] (by decide) 0
    rw [pElt_11] at e
    have h0' : (ruRho' hRho (ruP0E ^ 2))⁻¹ 0 = 0 := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact h0.symm
    rw [h0'] at e
    exact hne e
  have hcard : Nat.card CFSG.Sporadic.Recognition.RuMultiplier.RuCover ≤
      2 * Nat.card (J ruVec) := by
    rw [CFSG.Sporadic.Bridge.Ru.card_J]
    omega
  refine eq_of_onePoint (ruπ hTab) (coverMap_surjective _ _) hcard hz
    (ruP0E_sq_ne_one hRho) (ruRho' hRho) hzp hπ ?_
  have e := Nat.eq_of_beq_eq_true h16
  exact Fin.ext ((walkW_rho x hx 0).symm.trans (e.trans (walkW_rho y hy 0)))

theorem eta_bits {G : Type*} [Group G] (u : ℕ → G) (c : ℕ) :
    eta u 3 c = (if c.testBit 0 then u 0 else 1) * (if c.testBit 1 then u 1 else 1) *
      (if c.testBit 2 then u 2 else 1) := by
  rw [eta_succ, eta_succ, eta_succ]
  simp [eta]

noncomputable abbrev pE (i : ℕ) : CFSG.Sporadic.Recognition.RuMultiplier.RuCover :=
  pElt (eW.getD i [])

noncomputable abbrev pN (j : ℕ) : CFSG.Sporadic.Recognition.RuMultiplier.RuCover :=
  pElt (nW.getD j [])

theorem pair_eq : ∀ k < 12, pElt (eqPair k).1 = pElt (eqPair k).2 := by
  intro k hk
  have hc : ch7257e k = true := by
    interval_cases k
    exacts [ch7257e0, ch7257e1, ch7257e2, ch7257e3, ch7257e4, ch7257e5, ch7257e6, ch7257e7,
      ch7257e8, ch7257e9, ch7257e10, ch7257e11]
  exact eq_of_walks (letters_pairs k hk).1 (letters_pairs k hk).2 hc

theorem pE_sq : ∀ i < 3, pE i * pE i = 1 := by
  intro i hi
  interval_cases i
  · have h := pair_eq 0 (by norm_num)
    have e : eqPair 0 = (eW.getD 0 [] ++ eW.getD 0 [], []) := rfl
    rw [e, pElt_append, pElt_nil] at h
    exact h
  · have h := pair_eq 1 (by norm_num)
    have e : eqPair 1 = (eW.getD 1 [] ++ eW.getD 1 [], []) := rfl
    rw [e, pElt_append, pElt_nil] at h
    exact h
  · have h := pair_eq 2 (by norm_num)
    have e : eqPair 2 = (eW.getD 2 [] ++ eW.getD 2 [], []) := rfl
    rw [e, pElt_append, pElt_nil] at h
    exact h

theorem pE_comm : ∀ i < 3, ∀ j < 3, pE i * pE j = pE j * pE i := by
  have c01 : pE 0 * pE 1 = pE 1 * pE 0 := by
    have h := pair_eq 3 (by norm_num)
    have e : eqPair 3 = (eW.getD 0 [] ++ eW.getD 1 [], eW.getD 1 [] ++ eW.getD 0 []) := rfl
    rw [e, pElt_append, pElt_append] at h
    exact h
  have c02 : pE 0 * pE 2 = pE 2 * pE 0 := by
    have h := pair_eq 4 (by norm_num)
    have e : eqPair 4 = (eW.getD 0 [] ++ eW.getD 2 [], eW.getD 2 [] ++ eW.getD 0 []) := rfl
    rw [e, pElt_append, pElt_append] at h
    exact h
  have c12 : pE 1 * pE 2 = pE 2 * pE 1 := by
    have h := pair_eq 5 (by norm_num)
    have e : eqPair 5 = (eW.getD 1 [] ++ eW.getD 2 [], eW.getD 2 [] ++ eW.getD 1 []) := rfl
    rw [e, pElt_append, pElt_append] at h
    exact h
  intro i hi j hj
  interval_cases i <;> interval_cases j
  all_goals
    first
    | rfl
    | exact c01
    | exact c01.symm
    | exact c02
    | exact c02.symm
    | exact c12
    | exact c12.symm

theorem pN_conj_of {k j i : ℕ} (hk : k < 12)
    (e : eqPair k = (nW.getD j [] ++ eW.getD i [], etaW (tabCode j i) 3 ++ nW.getD j [])) :
    pN j * pE i * (pN j)⁻¹ = eta pE 3 ((tabC.getD j []).getD i 0) := by
  have h := pair_eq k hk
  rw [e, pElt_append, pElt_append, pElt_etaW] at h
  rw [mul_inv_eq_iff_eq_mul]
  exact h

theorem pN_conj : ∀ j < 2, ∀ i < 3,
    pN j * pE i * (pN j)⁻¹ = eta pE 3 ((tabC.getD j []).getD i 0) := by
  intro j hj i hi
  interval_cases j <;> interval_cases i
  · exact pN_conj_of (k := 6) (by norm_num) rfl
  · exact pN_conj_of (k := 7) (by norm_num) rfl
  · exact pN_conj_of (k := 8) (by norm_num) rfl
  · exact pN_conj_of (k := 9) (by norm_num) rfl
  · exact pN_conj_of (k := 10) (by norm_num) rfl
  · exact pN_conj_of (k := 11) (by norm_num) rfl

theorem rho_eta_ne : ∀ c < 8, ruRho' Certificates.certificate15025 (eta pE 3 c) ≠
    ruRho' Certificates.certificate15025 (ruP0E ^ 2) := by
  intro c hc h
  have hn : ch7257n c = true := by
    interval_cases c
    exacts [ch7257n0, ch7257n1, ch7257n2, ch7257n3, ch7257n4, ch7257n5, ch7257n6, ch7257n7]
  have hne : wW (etaW c 3) 0 ≠ wW [1, 1] 0 := ne_of_notB hn
  have e1 := walkW_rho (etaW c 3) (letters_etaW c hc) 0
  have e2 := walkW_rho [1, 1] (by decide) 0
  rw [pElt_etaW] at e1
  rw [pElt_11] at e2
  rw [h] at e1
  exact hne (e1.trans e2.symm)

theorem gP_etaW : ∀ k < 7, gP (pElt (etaW (eCode.getD k 0) 3)) = ruEElt k := by
  intro k hk
  have hc := Act.allR_spec (ch4060E k hk)
  have hP : PRep 4060 12 (RuB1K.EA k) (ruEElt k) := by
    have h : Rep 4060 (unpack 4060 12 (RuB1K.EA k)) (ruEElt k) := by
      rw [← RuB1K.e_eq hk]
      exact rep_ruEElt hk
    exact prep_of_rep h
  refine (eq_of_base (ruC_le (ruEElt_memC hk)) (gP_mem _) fun b hb => ?_).symm
  have h1 := Nat.eq_of_beq_eq_true (hc b.val (Nat.zero_le _) (by omega))
  rw [walkP_gP _ (letters_etaE k hk) b, apP_eq hP] at h1
  exact Fin.ext h1

theorem gP_pN_of {j : ℕ} {P : ℕ} {q : Equiv.Perm (Fin 4060)} (hj : j < 2) (hq : q ∈ ruP)
    (hP : PRep 4060 12 P q) (hc : ch4060 P (nW.getD j []) = true) : gP (pN j) = q := by
  have hc' := Act.allR_spec hc
  refine (eq_of_base hq (gP_mem _) fun b hb => ?_).symm
  have h1 := Nat.eq_of_beq_eq_true (hc' b.val (Nat.zero_le _) (by omega))
  rw [walkP_gP _ (letters_nW j hj) b, apP_eq hP] at h1
  exact Fin.ext h1

theorem gP_pN0 : gP (pN 0) = ruNs0 := by
  have h : Rep 4060 (unpack 4060 12 RuG.Ns0) ruNs0 := by
    rw [← RuG.ns0_eq]
    exact rep_ruNs0
  exact gP_pN_of (by norm_num) ruNs0_mem (prep_of_rep h) ch4060N.1

theorem gP_pN1 : gP (pN 1) = ruNs1 := by
  have h : Rep 4060 (unpack 4060 12 RuG.Ns1) ruNs1 := by
    rw [← RuG.ns1_eq]
    exact rep_ruNs1
  exact gP_pN_of (by norm_num) ruNs1_mem (prep_of_rep h) ch4060N.2

theorem gP_pE : ∀ i < 3, gP (pE i) = ruEElt i := by
  have tb1 : (1 : ℕ).testBit 0 = true ∧ (1 : ℕ).testBit 1 = false ∧ (1 : ℕ).testBit 2 = false :=
    by decide
  have tb2 : (2 : ℕ).testBit 0 = false ∧ (2 : ℕ).testBit 1 = true ∧ (2 : ℕ).testBit 2 = false :=
    by decide
  have tb4 : (4 : ℕ).testBit 0 = false ∧ (4 : ℕ).testBit 1 = false ∧ (4 : ℕ).testBit 2 = true :=
    by decide
  intro i hi
  have h := gP_etaW i (by omega)
  rw [pElt_etaW, eta_bits] at h
  interval_cases i
  · have e : eCode.getD 0 0 = 1 := rfl
    rw [e, tb1.1, tb1.2.1, tb1.2.2] at h
    simpa only [if_true, if_false, Bool.false_eq_true, mul_one, one_mul] using h
  · have e : eCode.getD 1 0 = 2 := rfl
    rw [e, tb2.1, tb2.2.1, tb2.2.2] at h
    simpa only [if_true, if_false, Bool.false_eq_true, mul_one, one_mul] using h
  · have e : eCode.getD 2 0 = 4 := rfl
    rw [e, tb4.1, tb4.2.1, tb4.2.2] at h
    simpa only [if_true, if_false, Bool.false_eq_true, mul_one, one_mul] using h

theorem ruEElt_eta : ∀ k < 7, ruEElt k = eta ruEElt 3 (eCode.getD k 0) := by
  intro k hk
  rw [← gP_etaW k hk, pElt_etaW, map_eta]
  exact eta_congr' _ 3 fun j hj => gP_pE j hj

theorem rep_pGen' : ∀ h < 2, Rep 16240 (pA ())[h]!
    (ruRho' Certificates.certificate15025 (pGen h)) := by
  intro h hh
  interval_cases h
  · rw [pA_get0]
    exact rep_ruRho_ruWE _ letters_p0
  · rw [pA_get1]
    exact rep_ruRho_ruWE _ letters_p1

theorem rep_pElt' {w : List ℤ} (hw : Native.lettersOK 2 w = true) :
    Rep 16240 (wordArr 16240 (pA ()) w) (ruRho' Certificates.certificate15025 (pElt w)) := by
  rw [ruRho'_pElt]
  exact rep_wordArr (k := 2) (by decide) rep_pGen'
    (fun i hi => KernelCosetJ.RhoPerm.isInvA_of_rep (rep_pGen' i hi)) hw

theorem rep_pElt4060' {w : List ℤ} (hw : Native.lettersOK 2 w = true) :
    Rep 4060 (wordArr 4060 (aA ()) w) (gP (pElt w)) := by
  have hTab : RuTabFact := Certificates.certificate15024
  have e : gP (pElt w) = wordIn 2 (fun h => ruJtoP (ruπ hTab (pGen h))) w := by
    rw [pElt, map_wordIn]
    rfl
  rw [e]
  have hg : ∀ h < 2, Rep 4060 (aA ())[h]! (ruJtoP (ruπ hTab (pGen h))) := by
    intro h hh
    interval_cases h
    · rw [aA_get0, ruJtoP_p0 hTab]
      exact rep_ruA0
    · rw [aA_get1, ruJtoP_p1 hTab]
      exact rep_ruA1
  exact rep_wordArr (k := 2) (by decide) hg
    (fun i hi => KernelCosetJ.RhoPerm.isInvA_of_rep (hg i hi)) hw

theorem coverChk_true : coverChk () = true := by
  have hTab : RuTabFact := Certificates.certificate15024
  set ρ := ruRho' Certificates.certificate15025 with hρ
  have rE : ∀ i < 3, Rep 16240 (eArr ())[i]! (ρ (pE i)) := fun i hi => by
    rw [eArr_get i hi]
    exact rep_pElt' (letters_eW i hi)
  have rN : ∀ j < 2, Rep 16240 (nArr ())[j]! (ρ (pN j)) := fun j hj => by
    rw [nArr_get j hj]
    exact rep_pElt' (letters_nW j hj)
  have h3 : allPermsOK 16240 (pA ()) = true := by
    unfold allPermsOK
    rw [allLt_iff]
    intro i hi
    have hs : (pA ()).size = 2 := rfl
    exact KernelCosetJ.RhoPerm.isInvA_of_rep (rep_pGen' i (by omega))
  have h6 : allPermsOK 16240 (nArr ()) = true := by
    unfold allPermsOK
    rw [allLt_iff]
    intro i hi
    have hs : (nArr ()).size = 2 := rfl
    exact KernelCosetJ.RhoPerm.isInvA_of_rep (rN i (by omega))
  have hP : ∀ c, Rep 16240 (prodA 16240 (eArr ()) c) (eta (fun i => ρ (pE i)) 3 c) :=
    rep_prodA rE
  have rz : Rep 16240 (zA ()) (ρ (ruP0E ^ 2)) := by
    have h0 := rep_pGen' 0 (by norm_num)
    have e : ruP0E ^ 2 = pGen 0 * pGen 0 := by rw [pow_two, pGen, if_pos rfl]
    rw [e, map_mul]
    exact rep_compA h0 h0
  have p16 : coverChk16240 () = true := by
    unfold coverChk16240
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true']
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨letters_p0, letters_p1⟩, h3⟩, letters_eW⟩, letters_nW⟩, h6⟩, ?_⟩, ?_⟩, ?_⟩,
      ?_⟩
    · intro i hi
      refine (eqA_iff (rep_compA (rE i hi) (rE i hi)) rep_idA).2 ?_
      rw [← map_mul, pE_sq i hi, map_one]
    · intro i hi j hj
      refine (eqA_iff (rep_compA (rE i hi) (rE j hj)) (rep_compA (rE j hj) (rE i hi))).2 ?_
      rw [← map_mul, ← map_mul, pE_comm i hi j hj]
    · intro c hc
      cases h : eqA 16240 (prodA 16240 (eArr ()) c) (zA ())
      · rfl
      · exfalso
        have e := (eqA_iff (hP c) rz).1 h
        rw [← map_eta] at e
        exact rho_eta_ne c hc e
    · intro j hj i hi
      have hinv := rep_inv_of_isInvA (rN j hj)
        (isInvA_of_allPermsOK h6 (by have : (nArr ()).size = 2 := rfl; omega))
      refine (eqA_iff (rep_compA (rep_compA (rN j hj) (rE i hi)) hinv) (hP _)).2 ?_
      rw [← map_inv, ← map_mul, ← map_mul, pN_conj j hj i hi, map_eta]
  have p4060 : coverChk4060 () = true := by
    unfold coverChk4060
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
    have g1 : allPermsOK 4060 (aA ()) = true := by
      unfold allPermsOK
      rw [allLt_iff]
      intro i hi
      have hs : (aA ()).size = 2 := rfl
      have hi2 : i < 2 := by omega
      interval_cases i
      · rw [aA_get0]
        exact KernelCosetJ.RhoPerm.isInvA_of_rep rep_ruA0
      · rw [aA_get1]
        exact KernelCosetJ.RhoPerm.isInvA_of_rep rep_ruA1
    refine ⟨⟨⟨⟨g1, fun i hi => ?_⟩, ?_⟩, ?_⟩, fun k hk => ?_⟩
    · exact (eqA_iff (rep_pElt4060' (letters_eW i hi)) (rep_ruEElt (by omega))).2 (gP_pE i hi)
    · exact (eqA_iff (rep_pElt4060' (letters_nW 0 (by norm_num))) rep_ruNs0).2 gP_pN0
    · exact (eqA_iff (rep_pElt4060' (letters_nW 1 (by norm_num))) rep_ruNs1).2 gP_pN1
    · refine (eqA_iff (rep_ruEElt hk) (rep_prodA (fun j hj => ?_) _)).2 (ruEElt_eta k hk)
      interval_cases j
      · exact rep_ruEElt (by norm_num)
      · exact rep_ruEElt (by norm_num)
      · exact rep_ruEElt (by norm_num)
  unfold coverChk
  rw [p16, p4060]
  rfl

end Main

end CertificateChecks.KernelMisc.RuCover

end
