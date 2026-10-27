module

public import Certificates.Kernel.SporSch.HeThree.Checks
public import Certificates.Kernel.SporSch.HeThree.Count
public import Certificates.Kernel.SporSch.HeT.CntGlue
public import CFSG.Certificates.Kernel.SporSch.NfGroupSound
public import CFSG.Certificates.Kernel.HexArrsSound
public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3SylowCrit
public import CFSG.RankThree.PartTwo.KFacts.K426Kit
public import CFSG.Monster.B.Mathieu.Order
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.H13.J4Words
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier CFSG.Sporadic.HeldB
open CertificateChecks.KernelSporSch CertificateChecks.KernelSpor CertificateChecks.KernelSporSch.HeO16
open CertificateChecks.KernelSporSch.HeCn CFSG.HardMathSupport.Solomon.Coordinator.B3S3
open Subgroup

noncomputable abbrev yP (c : Nat) : Equiv.Perm (Fin 8330) := permOfArr 8330 heS3CaseX[c]!


theorem baseF : BaseFaithful heP bsH := by
  rw [heP_eq_originalSubgroup]
  exact he_baseFaithful

theorem bs_lt : ∀ b ∈ bsH, b < 8330 := by decide

theorem codes : Codes heP evH vldH E := fun _ hF =>
  ⟨E_rep hF, heP_eq_originalSubgroup ▸ E_mem hF⟩

theorem xcN : XC.N = 2 := rfl

theorem bindX : (heS3CaseX).size = 2 ∧ ∀ c < 2, heS3CaseX[c]! = unpack 8330 14 (XC.F c) := by
  have h := CFSG.KC.HexArrs.hexArrs_sound XC.all
  rw [← XC.eq, xcN] at h
  exact h

theorem ry_all (c : Nat) (hc : c < 2) : ∀ x < 8330,
    pmR (RY c) x = pm (XC.F c) x ∧ pmR (RY c) x = HeTc.nfp (G c) x := by
  intro x hx
  have hs : ∀ s < 49, ry c s = true := by
    intro s hs
    interval_cases c
    · exact RY0c.all s hs
    · exact RY1c.all s hs
  have h1 := allN_spec (hs (x / 170) (by omega)) (x % 170) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (x / 170) 170) (x % 170) = x := by
    change x / 170 * 170 + x % 170 = x
    exact Nat.div_add_mod' x 170
  rw [strictB_val, e, bAnd_iff] at h1
  exact ⟨Nat.eq_of_beq_eq_true h1.1, Nat.eq_of_beq_eq_true h1.2⟩

theorem gValid (c : Nat) (hc : c < 2) : vldH (G c) = true := by
  interval_cases c
  · exact kG0
  · exact kG1

theorem yP_eq (c : Nat) (hc : c < 2) : yP c = E (G c) := by
  have hE := E_rep (gValid c hc)
  have hrep : Rep 8330 heS3CaseX[c]! (E (G c)) := by
    rw [(bindX.2 c hc)]
    refine rep_of_repF fun x hx => ?_
    have := ry_all c hc x hx
    rw [← hE x hx]
    exact this.1.symm.trans this.2
  exact CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep hrep

theorem yP_mem (c : Nat) (hc : c < 2) : yP c ∈ heP := by
  rw [yP_eq c hc]
  exact (codes _ (gValid c hc)).2

theorem yP_rep (c : Nat) (hc : c < 2) : RepF 8330 (pmR (RY c)) (yP c) := by
  rw [yP_eq c hc]
  intro x hx
  rw [(ry_all c hc x hx).2]
  exact E_rep (gValid c hc) x hx

theorem rx_parts (c : Nat) (hc : c < 2) :
    rbAll (RX c) (X c) = true ∧ pmR (RX c) 0 = 0 ∧ pmR (RX c) 1 = 2 := by
  have h : rx c = true := by
    interval_cases c
    · exact kRX0
    · exact kRX1
  unfold rx at h
  rw [bAnd_iff, bAnd_iff] at h
  exact ⟨h.1, Nat.eq_of_beq_eq_true h.2.1, Nat.eq_of_beq_eq_true h.2.2⟩

theorem card_cent_eq (c : Nat) (hc : c < 2) :
    Nat.card {g : heP // yP c * (g : Equiv.Perm (Fin 8330)) = g * yP c} = sumN 8330 (V c) := by
  obtain ⟨hrb, hx0, hx1⟩ := rx_parts c hc
  have hperm : permOK 8330 14 (mask 14) (8330 * 14) (X c) (XI c) = true := by
    interval_cases c
    · exact kXP0
    · exact kXP1
  have hX : RepF 8330 (pmR (RX c)) (permOfArr 8330 (unpack 8330 14 (X c))) :=
    repF_of_rb hrb (rep_pm hperm)
  have hY := yP_rep c hc
  have hF : nfValidK 5 HeC.LR (F c) = true := by
    interval_cases c
    · exact kF0
    · exact kF1
  have hcj : ∀ s < 49, cjB (RX c) (RY c) (F c) s = true := by
    intro s hs
    interval_cases c
    · exact CJ0c.all s hs
    · exact CJ1c.all s hs
  have hV : ∀ s < 49, orB (RX c) (RY c) (V c) (Rc c) (Zc c) 8330 s = true := by
    intro s hs
    interval_cases c
    · exact OR0c.all s hs
    · exact OR1c.all s hs
  exact cent_of_or hX hY hF hcj hx0 hx1 (hxy_of_mem hX hY hF hcj (yP_mem c hc)) (e := 8330)
    (fun h => absurd h (by norm_num)) hV

theorem card_cent_inf (c : Nat) (hc : c < 2) :
    Nat.card ↥(centralizer {yP c} ⊓ heP) = sumN 8330 (V c) := by
  rw [← card_cent_eq c hc]
  refine Nat.card_congr
    { toFun := fun g => ⟨⟨g, g.2.2⟩, (mem_centralizer_singleton_iff.1 g.2.1).symm⟩
      invFun := fun g => ⟨g.1, mem_centralizer_singleton_iff.2 g.2.symm, g.1.2⟩
      left_inv := fun g => rfl
      right_inv := fun g => rfl }

theorem card_cent0 : Nat.card ↥(centralizer {yP 0} ⊓ heP) = 7560 := by
  rw [card_cent_inf 0 (by norm_num)]
  exact Nat.eq_of_beq_eq_true kSum0

theorem card_cent1 : Nat.card ↥(centralizer {yP 1} ⊓ heP) = 504 := by
  rw [card_cent_inf 1 (by norm_num)]
  exact Nat.eq_of_beq_eq_true kSum1

theorem lg_mem_eq {L : Nat → Nat} {i : Nat} (hv : vldH (L i) = true) {f : Nat → Nat}
    {g : Equiv.Perm (Fin 8330)} (hf : RepF 8330 f g) (hg : g ∈ heP)
    (h : eqOnL bsH (evH (L i)) f = true) : E (L i) = g :=
  eq_of_eqOnL baseF (codes _ hv).1 hf (codes _ hv).2 hg h

theorem exists_conj (x : Equiv.Perm (Fin 8330)) (hx : x ∈ heP) (hxo : orderOf x = 3) :
    ∃ c < 2, ∃ k ∈ heP, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ x = k * yP c ^ e * k⁻¹ := by
  have hQ := kQ
  have hQP : lgSub baseF bs_lt codes hQ (by norm_num) ≤ heP :=
    lgSub_le baseF bs_lt codes hQ (by norm_num)
  have hQc : Nat.card (lgSub baseF bs_lt codes hQ (by norm_num)) =
      3 ^ (Nat.card heP).factorization 3 := by
    rw [card_lgSub baseF bs_lt codes hQ (by norm_num), card_heP,
      show (4030387200 : ℕ) = 3 ^ 3 * 149273600 by norm_num,
      CFSG.RankThree.PartOne.factorization_pow_mulG Nat.prime_three (by norm_num)]
    norm_num
  obtain ⟨hv, -, -, -, -⟩ := lgOK_parts hQ
  have hlines : ∀ g ∈ lgSub baseF bs_lt codes hQ (by norm_num), g ^ 3 = 1 →
      g = 1 ∨ ∃ j < 13, ∃ e < 3, g = E (LN j) ^ e := by
    rintro _ ⟨i, hi, rfl⟩ -
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact Or.inl (lg_one baseF bs_lt codes hQ (by norm_num))
    · right
      have h := allN_spec kQL (i - 1) (by omega)
      have ei : Nat.add (i - 1) 1 = i := Nat.sub_add_cancel hi0
      rw [strictB_val, ei, bAnd_iff, bAnd_iff, bAnd_iff,
        Nat.blt_eq, Nat.blt_eq, Nat.blt_eq] at h
      obtain ⟨hj, ⟨-, he⟩, heq⟩ := h
      have hLv : vldH (LN (QJ i)) = true := (bAnd_iff _ _).1 (allN_spec kQH _ hj) |>.1
      refine ⟨QJ i, hj, QE i, he, ?_⟩
      exact lg_mem_eq (hv i hi) ((codes _ hLv).1.powF _) (heP.pow_mem (codes _ hLv).2 _) heq
  have htrans : ∀ j < 13, E (HN j) ∈ heP ∧ E (HN j) * yP (RC j) * (E (HN j))⁻¹ = E (LN j) := by
    intro j hj
    have h := allN_spec kQH j hj
    rw [bAnd_iff, bAnd_iff, bAnd_iff, Nat.blt_eq] at h
    obtain ⟨hL, hH, hr, heq⟩ := h
    have hHm := (codes _ hH).2
    refine ⟨hHm, ?_⟩
    have e := eq_of_eqOnL baseF ((codes _ hH).1.comp (yP_rep _ hr)) ((codes _ hL).1.comp (codes _ hH).1)
      (heP.mul_mem hHm (yP_mem _ hr)) (heP.mul_mem (codes _ hL).2 hHm) heq
    rw [e, mul_inv_cancel_right]
  obtain ⟨k, hk, j, hj, e, he, rfl⟩ := CFSG.RankThree.PartTwo.KFacts.K426.exists_conj_rep hQP hQc
    (fun j => E (LN j)) yP (fun j => E (HN j)) RC hlines htrans hx hxo
  have hr : RC j < 2 := by
    have h := allN_spec kQH j hj
    rw [bAnd_iff, bAnd_iff, bAnd_iff, Nat.blt_eq] at h
    exact h.2.2.1
  exact ⟨RC j, hr, k, hk, e, he, rfl⟩

theorem kQlg : lgOK evH vldH bsH QL QT QI 27 = true := kQ

theorem sOK_lg {c p m e : Nat} (h : sOK c p m e = true) :
    lgOK evH vldH bsH (SL c p m) (ST c p m) (SI c p m) m = true := by
  unfold sOK at h
  exact ((bAnd_iff _ _).1 h).1

theorem gparts : (vldH 0 = true ∧ E 0 = 1) ∧
    (∀ i < 2, vldH (QG i) = true ∧ E (QG i) = E (QL (i + 1))) ∧
    (∀ i < 3, vldH (CG i) = true ∧ E (CG i) ∈ centralizer {yP 0} ⊓ heP) := by
  have h := kGW
  unfold gOK at h
  simp only [bAnd_iff] at h
  obtain ⟨h0, hid, hq, hc⟩ := h
  have hv := (lgOK_parts kQlg).1
  refine ⟨⟨h0, (fixL_iff baseF bs_lt (codes _ h0).1 (codes _ h0).2).1 hid⟩, fun i hi => ?_,
    fun i hi => ?_⟩
  · have hi' := allN_spec hq i hi
    rw [bAnd_iff] at hi'
    exact ⟨hi'.1, lg_mem_eq hi'.1 (codes _ (hv _ (by omega))).1 (codes _ (hv _ (by omega))).2
      hi'.2⟩
  · have hi' := allN_spec hc i hi
    rw [bAnd_iff] at hi'
    exact ⟨hi'.1, mem_centralizer_singleton_iff.2 (comL_sound baseF codes (yP_rep 0 (by norm_num))
      (yP_mem 0 (by norm_num)) hi'.1 hi'.2), (codes _ hi'.1).2⟩

theorem gb_all : ∀ x < 8330, (∀ i < 2, pm (QGX.F i) x = evH (QG i) x) ∧
    (∀ i < 3, pm (CGX.F i) x = evH (CG i) x) := by
  intro x hx
  have hs : ∀ s < 49, gb s = true := fun s hs => GBc.all s hs
  have h1 := allN_spec (hs (x / 170) (by omega)) (x % 170) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (x / 170) 170) (x % 170) = x := by
    change x / 170 * 170 + x % 170 = x
    exact Nat.div_add_mod' x 170
  rw [strictB_val, e, bAnd_iff] at h1
  exact ⟨fun i hi => Nat.eq_of_beq_eq_true (allN_spec h1.1 i hi),
    fun i hi => Nat.eq_of_beq_eq_true (allN_spec h1.2 i hi)⟩

theorem qgN : QGX.N = 2 := rfl
theorem cgN : CGX.N = 3 := rfl

theorem bindQ : heS3QGens.size = 2 ∧ ∀ i < 2, heS3QGens[i]! = unpack 8330 14 (QGX.F i) := by
  have h := CFSG.KC.HexArrs.hexArrs_sound QGX.all
  rw [← QGX.eq, qgN] at h
  exact h

theorem bindC : heS3C0Gens.size = 3 ∧ ∀ i < 3, heS3C0Gens[i]! = unpack 8330 14 (CGX.F i) := by
  have h := CFSG.KC.HexArrs.hexArrs_sound CGX.all
  rw [← CGX.eq, cgN] at h
  exact h

theorem qperm (i : Nat) (hi : i < 2) :
    Rep 8330 heS3QGens[i]! (E (QG i)) ∧ permOfArr 8330 heS3QGens[i]! = E (QG i) := by
  have hv := (gparts.2.1 i hi).1
  have hr : Rep 8330 heS3QGens[i]! (E (QG i)) := by
    rw [bindQ.2 i hi]
    refine rep_of_repF fun x hx => ?_
    change pm (QGX.F i) x = _
    rw [(gb_all x hx).1 i hi]
    exact E_rep hv x hx
  exact ⟨hr, CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep hr⟩

theorem cperm (i : Nat) (hi : i < 3) : permOfArr 8330 heS3C0Gens[i]! = E (CG i) := by
  have hv := (gparts.2.2 i hi).1
  have hr : Rep 8330 heS3C0Gens[i]! (E (CG i)) := by
    rw [bindC.2 i hi]
    refine rep_of_repF fun x hx => ?_
    change pm (CGX.F i) x = _
    rw [(gb_all x hx).2 i hi]
    exact E_rep hv x hx
  exact CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep hr

theorem qg_valid (j : Nat) : vldH (QG j) = true := by
  by_cases hj : j < 2
  · exact (gparts.2.1 j hj).1
  · have : QG j = 0 := by
      unfold QG
      rw [blt_false hj]
    rw [this]
    exact gparts.1.1

theorem cg_valid (j : Nat) : vldH (CG j) = true := by
  by_cases hj : j < 3
  · exact (gparts.2.2 j hj).1
  · have : CG j = 0 := by
      unfold CG
      rw [blt_false hj]
    rw [this]
    exact gparts.1.1

theorem qg_mem (j : Nat) : E (QG j) ∈ closure (CFSG.RankThree.Native.permsA 8330 heS3QGens) := by
  by_cases hj : j < 2
  · rw [← (qperm j hj).2]
    exact subset_closure ⟨j, by rw [Set.mem_setOf_eq, bindQ.1]; exact hj, rfl⟩
  · have : QG j = 0 := by
      unfold QG
      rw [blt_false hj]
    rw [this, gparts.1.2]
    exact one_mem _

theorem cg_mem (j : Nat) : E (CG j) ∈ closure (CFSG.RankThree.Native.permsA 8330 heS3C0Gens) := by
  by_cases hj : j < 3
  · rw [← cperm j hj]
    exact subset_closure ⟨j, by rw [Set.mem_setOf_eq, bindC.1]; exact hj, rfl⟩
  · have : CG j = 0 := by
      unfold CG
      rw [blt_false hj]
    rw [this, gparts.1.2]
    exact one_mem _

theorem qclos : closure (CFSG.RankThree.Native.permsA 8330 heS3QGens) =
    lgSub baseF bs_lt codes kQlg (by norm_num) := by
  have hv := (lgOK_parts kQlg).1
  refine le_antisymm ((closure_le _).2 ?_) ?_
  · rintro _ ⟨k, hk, rfl⟩
    have hk' : k < 2 := by rw [Set.mem_setOf_eq, bindQ.1] at hk; exact hk
    dsimp only
    rw [(qperm k hk').2, (gparts.2.1 k hk').2]
    exact ⟨k + 1, by omega, rfl⟩
  · rintro _ ⟨i, hi, rfl⟩
    rw [wordsOK_sound baseF codes qg_valid hv kQW i hi]
    exact wElt_mem _ qg_mem 40 _

theorem c0clos : closure (CFSG.RankThree.Native.permsA 8330 heS3C0Gens) =
    centralizer {yP 0} ⊓ heP := by
  have hle : closure (CFSG.RankThree.Native.permsA 8330 heS3C0Gens) ≤ centralizer {yP 0} ⊓ heP := by
    refine (closure_le _).2 ?_
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k < 3 := by rw [Set.mem_setOf_eq, bindC.1] at hk; exact hk
    dsimp only
    rw [cperm k hk']
    exact (gparts.2.2 k hk').2
  have hcw := kCW
  unfold cwOK at hcw
  simp only [bAnd_iff] at hcw
  obtain ⟨w2, w5, w7, w3⟩ := hcw
  have hdvd : ∀ {L T I : Nat → Nat} {W : Nat → Nat} {m : Nat}
      (h : lgOK evH vldH bsH L T I m = true) (hm : 0 < m) (hw : wordsOK evH bsH CG L W m = true),
      m ∣ Nat.card ↥(closure (CFSG.RankThree.Native.permsA 8330 heS3C0Gens)) := by
    intro L T I W m h hm hw
    rw [← card_lgSub baseF bs_lt codes h hm]
    refine Subgroup.card_dvd_of_le ?_
    rintro _ ⟨i, hi, rfl⟩
    rw [wordsOK_sound baseF codes cg_valid (lgOK_parts h).1 hw i hi]
    exact wElt_mem _ cg_mem 40 _
  have h8 := hdvd (sOK_lg kS00) (by norm_num) w2
  have h5 := hdvd (sOK_lg kS05) (by norm_num) w5
  have h7 := hdvd (sOK_lg kS07) (by norm_num) w7
  have h27 := hdvd kS3 (by norm_num) w3
  have h216 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h27
  have h1080 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h216 h5
  have h7560 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h1080 h7
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_cent0]
  exact Nat.le_of_dvd Nat.card_pos h7560

theorem orderOf_yP (c : Nat) (hc : c < 2) : orderOf (yP c) = 3 := by
  have h : ordPL bsH (pmR (RY c)) 3 = true := by
    interval_cases c
    · exact kO0
    · exact kO1
  exact (ordPL_iff baseF bs_lt (yP_rep c hc) (yP_mem c hc) Nat.prime_three).1 h

theorem pow_eq_one_of_not_dvd {C : Subgroup (Equiv.Perm (Fin 8330))} {k e : ℕ}
    (hC : Nat.card C = 3 ^ k * e) {z : Equiv.Perm (Fin 8330)} (hz : z ∈ C)
    (h3 : ¬ 3 ∣ orderOf z) : z ^ e = 1 := by
  have hd : orderOf z ∣ 3 ^ k * e := hC ▸ Subgroup.orderOf_dvd_natCard C hz
  have hcop : Nat.Coprime (orderOf z) (3 ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_three).2 h3)))
  exact orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_left hd)

theorem syl_parts (c p m e : Nat) (hc : c < 2) (hm : 0 < m) (h : sOK c p m e = true)
    (hp : p.Prime) (hord : ∀ z ∈ centralizer {yP c} ⊓ heP, ¬ 3 ∣ orderOf z → z ^ e = 1) :
    ∃ S : Subgroup (Equiv.Perm (Fin 8330)), S ≤ centralizer {yP c} ⊓ heP ∧ Nat.card S = m ∧
      ∀ s ∈ S, orderOf s = p → ∃ u ∈ centralizer {yP c} ⊓ heP, 3 ∣ orderOf (s * (u * s * u⁻¹)) := by
  unfold sOK at h
  rw [bAnd_iff] at h
  obtain ⟨hlg, hall⟩ := h
  obtain ⟨hv, -, -, -, -⟩ := lgOK_parts hlg
  have hY := yP_rep c hc
  have hYm := yP_mem c hc
  have hcent : ∀ a, vldH a = true → comL evH bsH (pmR (RY c)) a = true →
      E a ∈ centralizer {yP c} ⊓ heP := fun a ha hco =>
    ⟨mem_centralizer_singleton_iff.2 (comL_sound baseF codes hY hYm ha hco), (codes a ha).2⟩
  refine ⟨lgSub baseF bs_lt codes hlg hm, ?_, card_lgSub baseF bs_lt codes hlg hm, ?_⟩
  · rintro _ ⟨i, hi, rfl⟩
    have hi' := allN_spec hall i hi
    unfold sEl at hi'
    rw [bAnd_iff] at hi'
    exact hcent _ (hv i hi) hi'.1
  · rintro _ ⟨i, hi, rfl⟩ hso
    have hi' := allN_spec hall i hi
    unfold sEl at hi'
    rw [bAnd_iff] at hi'
    obtain ⟨-, hw⟩ := hi'
    cases hf : Nat.beq (SF c p m i) 1
    · rw [hf, bNot_iff] at hw
      exact absurd ((ordPL_iff baseF bs_lt (codes _ (hv i hi)).1 (codes _ (hv i hi)).2 hp).2 hso) hw
    · rw [hf] at hw
      simp only [bAnd_iff] at hw
      obtain ⟨hu, hvv, hco, hwt⟩ := hw
      obtain ⟨huv, hne⟩ := wtL_sound baseF bs_lt codes (hv i hi) hu hvv hwt
      have hvinv : E (SV c p m i) = (E (SU c p m i))⁻¹ := eq_inv_of_mul_eq_one_right huv
      have huC := hcent _ hu hco
      refine ⟨E (SU c p m i), huC, ?_⟩
      by_contra h3
      have hsC := hcent _ (hv i hi) ((bAnd_iff _ _).1 (allN_spec hall i hi)).1
      have hz : E (SL c p m i) * (E (SU c p m i) * E (SL c p m i) * (E (SU c p m i))⁻¹) ∈
          centralizer {yP c} ⊓ heP :=
        Subgroup.mul_mem _ hsC (Subgroup.mul_mem _ (Subgroup.mul_mem _ huC hsC)
          (Subgroup.inv_mem _ huC))
      apply hne
      rw [hvinv]
      have := hord _ hz h3
      simpa only [mul_assoc] using this

theorem prime_dvd_7560 {p : ℕ} (hp : p.Prime) (hd : p ∣ 7560) : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  have hle : p ≤ 7560 := Nat.le_of_dvd (by norm_num) hd
  have h : p ∣ 2 ^ 3 * 3 ^ 3 * 5 * 7 := by norm_num; exact hd
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
          (hp.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h)))

theorem core0 : CFSG.Open.GLAPPrimeCoreOf 3 (centralizer {yP 0} ⊓ heP) = ⊥ := by
  have hord : ∀ z ∈ centralizer {yP 0} ⊓ heP, ¬ 3 ∣ orderOf z → z ^ 280 = 1 :=
    fun z hz h3 => pow_eq_one_of_not_dvd (k := 3) (by rw [card_cent0]; norm_num) hz h3
  obtain ⟨S2, h2C, h2c, h2w⟩ := syl_parts 0 2 8 280 (by norm_num) (by norm_num) kS00
    Nat.prime_two hord
  obtain ⟨S5, h5C, h5c, h5w⟩ := syl_parts 0 5 5 280 (by norm_num) (by norm_num) kS05
    (by norm_num) hord
  obtain ⟨S7, h7C, h7c, h7w⟩ := syl_parts 0 7 7 280 (by norm_num) (by norm_num) kS07
    (by norm_num) hord
  refine CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_three_eq_bot_of_sylow
    (fun p => if p = 2 then S2 else if p = 5 then S5 else S7) fun p hp hd h3 => ?_
  rw [card_cent0] at hd ⊢
  rcases prime_dvd_7560 hp hd with rfl | rfl | rfl | rfl
  · refine ⟨h2C, ?_, h2w⟩
    rw [if_pos rfl, h2c, show (7560 : ℕ) = 2 ^ 3 * 945 by norm_num,
      CFSG.RankThree.PartOne.factorization_pow_mulG Nat.prime_two (by norm_num)]
    norm_num
  · exact absurd rfl h3
  · refine ⟨h5C, ?_, h5w⟩
    rw [if_neg (by norm_num), if_pos rfl, h5c, show (7560 : ℕ) = 5 ^ 1 * 1512 by norm_num,
      CFSG.RankThree.PartOne.factorization_pow_mulG (by norm_num) (by norm_num)]
    norm_num
  · refine ⟨h7C, ?_, h7w⟩
    rw [if_neg (by norm_num), if_neg (by norm_num), h7c, show (7560 : ℕ) = 7 ^ 1 * 1080 by norm_num,
      CFSG.RankThree.PartOne.factorization_pow_mulG (by norm_num) (by norm_num)]
    norm_num

theorem core1 : CFSG.Open.GLAPPrimeCoreOf 3 (centralizer {yP 1} ⊓ heP) = ⊥ := by
  have hord : ∀ z ∈ centralizer {yP 1} ⊓ heP, ¬ 3 ∣ orderOf z → z ^ 56 = 1 :=
    fun z hz h3 => pow_eq_one_of_not_dvd (k := 2) (by rw [card_cent1]; norm_num) hz h3
  obtain ⟨S2, h2C, h2c, h2w⟩ := syl_parts 1 2 8 56 (by norm_num) (by norm_num) kS12
    Nat.prime_two hord
  obtain ⟨S7, h7C, h7c, h7w⟩ := syl_parts 1 7 7 56 (by norm_num) (by norm_num) kS17
    (by norm_num) hord
  refine CFSG.HardMathSupport.Solomon.Coordinator.gLAPPrimeCoreOf_three_eq_bot_of_sylow
    (fun p => if p = 2 then S2 else S7) fun p hp hd h3 => ?_
  rw [card_cent1] at hd ⊢
  have hd' : p ∣ 7560 := hd.trans (by norm_num)
  rcases prime_dvd_7560 hp hd' with rfl | rfl | rfl | rfl
  · refine ⟨h2C, ?_, h2w⟩
    rw [if_pos rfl, h2c, show (504 : ℕ) = 2 ^ 3 * 63 by norm_num,
      CFSG.RankThree.PartOne.factorization_pow_mulG Nat.prime_two (by norm_num)]
    norm_num
  · exact absurd rfl h3
  · exact absurd hd (by norm_num)
  · refine ⟨h7C, ?_, h7w⟩
    rw [if_neg (by norm_num), h7c, show (504 : ℕ) = 7 ^ 1 * 72 by norm_num,
      CFSG.RankThree.PartOne.factorization_pow_mulG (by norm_num) (by norm_num)]
    norm_num

theorem facts :
    (∀ x ∈ heP, orderOf x = 3 → ∃ c < 2, ∃ k ∈ heP, ∃ e : ℕ, (e = 1 ∨ e = 2) ∧
      x = k * yP c ^ e * k⁻¹) ∧
    (∀ c < 2, yP c ∈ heP ∧ orderOf (yP c) = 3 ∧
      CFSG.Open.GLAPPrimeCoreOf 3 (centralizer {yP c} ⊓ heP) = ⊥) ∧
    Nat.card ↥(centralizer {yP 0} ⊓ heP) = 7560 ∧
    Nat.card ↥(centralizer {yP 1} ⊓ heP) = 504 ∧
    closure (CFSG.RankThree.Native.permsA 8330 heS3C0Gens) = centralizer {yP 0} ⊓ heP ∧
    closure (CFSG.RankThree.Native.permsA 8330 heS3QGens) ≤ heP ∧
    Nat.card ↥(closure (CFSG.RankThree.Native.permsA 8330 heS3QGens)) = 27 ∧
    ∀ i < 2, Rep 8330 heS3QGens[i]! (permOfArr 8330 heS3QGens[i]!) := by
  refine ⟨exists_conj, fun c hc => ⟨yP_mem c hc, orderOf_yP c hc, ?_⟩, card_cent0, card_cent1,
    c0clos, ?_, ?_, fun i hi => ?_⟩
  · interval_cases c
    · exact core0
    · exact core1
  · rw [qclos]
    exact lgSub_le baseF bs_lt codes kQlg (by norm_num)
  · rw [qclos]
    exact card_lgSub baseF bs_lt codes kQlg (by norm_num)
  · rw [(qperm i hi).2]
    exact (qperm i hi).1

end CertificateChecks.KernelSporSch.HeThree

end
