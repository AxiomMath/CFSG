module

public import Certificates.Kernel.Fi23Five.Glue
public import Certificates.Kernel.Fi23Five.MooreChk
public import Certificates.Kernel.Fi23Five.MooreFam
public import Certificates.Kernel.Fi23K.OrbEq
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveSylow
import Certificates.Kernel.Fi23Five.Small
public import CFSG.Sporadic.SchreierLemmas.MooreChain
public import Certificates.Data.Fi23Moore
import Mathlib
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporAssemble
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43Rest
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiRefine
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
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
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRowFusion
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.J4OrderBase
public import CFSG.Quasithin.H13.J4Words
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.Native.Fi22FiveCheckInputs
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.Fi22
public import CFSG.Sporadic.FischerOddCore.Fi23T2Card
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Schreier.RuLocal
public import CFSG.Sporadic.SchreierLemmas.FrattiniProfile
public import CFSG.Sporadic.ThSchreier.ThSchreierCase
public import CFSG.Walter.JRFacts
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate10027
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate131101Base
public import Certificates.Certificate13620Base
public import Certificates.Certificate16018
public import Certificates.Certificate2323
public import Certificates.Certificate6006
public import Certificates.Certificate9124

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelFi23Five

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23Five CFSG.KD.Fi23K CFSG.KD.Fi23Five
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native CertificateChecks.KernelFi23M
  CertificateChecks.KernelFi23R CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24MooreNative

theorem extendChain_congr {c c' : Nat → Nat → Bool} {F : List Nat}
    (h : ∀ i ∈ F, ∀ j ∈ F, c i j = c' i j) :
    ∀ (n : Nat) (p : List Nat), (∀ x ∈ p, x ∈ F) → extendChain c F n p = extendChain c' F n p
  | 0, _, _ => rfl
  | n + 1, p, hp => by
    simp only [extendChain]
    apply findSome_mem_congr
    intro v hv
    have e2 : (p.drop 1).all (fun u => c u v) = (p.drop 1).all (fun u => c' u v) := by
      have hu : ∀ u ∈ p.drop 1, c u v = c' u v := fun u hu =>
        h u (hp u (List.mem_of_mem_drop hu)) v hv
      rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
      exact ⟨fun H u hu' => hu u hu' ▸ H u hu', fun H u hu' => (hu u hu').symm ▸ H u hu'⟩
    have e3 : extendChain c F n (v :: p) = extendChain c' F n (v :: p) :=
      extendChain_congr h n (v :: p) fun x hx => by
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hv
        · exact hp x hx
    cases hh : p.head? with
    | none => simp only [e2, e3]
    | some a => simp only [e2, e3, h a (hp a (List.mem_of_head? hh)) v hv]

end CertificateChecks.KernelFi23Five

namespace CertificateChecks.KernelFi23Five

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23Five CFSG.KD.Fi23K CFSG.KD.Fi23Five
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native CertificateChecks.KernelFi23M
  CertificateChecks.KernelFi23R CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24MooreNative

section


theorem moore_chain :
    mooreChain23 orbLit (dTable orbLit) (genTables orbLit (-2)) (eTab orbLit) 6 = mooreP := by
  have hfix : fixList (eTab orbLit) = lE := fixList_of (fun i hi => by
    rw [rw_e.ap hi, wv_cons, wv_nil, tb_e hi]) fixE_ok
  have hc := ch10137chain
  unfold chainOf at hc
  unfold mooreChain23 chainOf
  rw [hfix, extendChain_congr (c' := cmK G) (fun i hi j hj => commB_eq (lt_lE hi) (lt_lE hj)) 6 []
    (fun x hx => absurd hx List.not_mem_nil)]
  exact hc

theorem fix_e_lit : fixList (eTab orbLit) = lE := fixList_of (fun i hi => by
    rw [rw_e.ap hi, wv_cons, wv_nil, tb_e hi]) fixE_ok


set_option maxRecDepth 400000 in
open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th in
theorem moore_ok : fi23FiveMooreOK (orbitData ()) = true := by
  have hn : (31671 : ℕ) < 2 ^ 32 := by norm_num
  have horb : orb = orbLit := CFSG.KD.Fi23K.orbitData_eq'
  have hlt : ∀ i < 6, mooreP[i]! < 31671 := by decide
  have hcomm : ∀ i < 6, ∀ j < 6,
      (commB orb (dTable orb) (genTables orb (-2)) mooreP[i]! mooreP[j]! = cmK G mooreP[i]! mooreP[j]!) :=
    fun i hi j hj => by rw [horb]; exact commB_eq (hlt i hi) (hlt j hj)
  have hP : mooreChain23 orb (dTable orb) (genTables orb (-2)) (eTab orb) 6 = mooreP := by
    rw [horb]; exact moore_chain
  have rE : CFSG.Sporadic.Th.Rep 31671 (eTab orb) (wordG CFSG.Sporadic.Fi23.genG eLetters) :=
    CFSG.Sporadic.Th.Rep.wordT (by norm_num) eLetters fun l _ => CFSG.Sporadic.Fi23.rep_gen l
  set E := wordG CFSG.Sporadic.Fi23.genG eLetters with hE
  set s : ℕ → CFSG.Sporadic.Fi23.J := fun i => CFSG.Sporadic.Fi23.conjPt mooreP[i]! with hs_def
  have hD : ∀ i < 6, IsConj CFSG.Sporadic.Fi23.d (s i) := fun i hi =>
    (isConj_d_iff (s i)).2 ⟨⟨mooreP[i]!, hlt i hi⟩, by rw [hs_def]⟩
  have hnc : ∀ i, i + 1 < 6 → s i * s (i + 1) ≠ s (i + 1) * s i := by
    intro i hi h
    have h1 := (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five.commB_iff (hlt i (by omega)) (hlt (i + 1) hi)).2 h
    rw [hcomm i (by omega) (i + 1) hi, ch10137nc i (by omega)] at h1
    exact absurd h1 (by decide)
  have hc : ∀ i j, i + 2 ≤ j → j < 6 → s i * s j = s j * s i := by
    intro i j hij hj
    refine (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five.commB_iff (hlt i (by omega)) (hlt j hj)).1 ?_
    rw [hcomm i (by omega) j hj]
    exact ch10137c i (by omega) j hj hij
  obtain ⟨hfam, hm1'⟩ := Fi23Moore10137.moore_fam s hD hnc hc
  set m : ℕ → CFSG.Sporadic.Fi23.J := fun j =>
    ((mooreWord mooreP j).map CFSG.Sporadic.Fi23.conjPt).prod with hm_def
  have hm : ∀ j, Rep 31671 (mooreTab23 orb (dTable orb) (genTables orb (-2)) mooreP j) (m j) :=
    fun j => CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five.rep_starWordTab_dTable (mooreWord mooreP j)
  have hmj : ∀ j, m j = CFSG.Sporadic.SchreierLemmas.mooreOfChain s j := by
    intro j
    simp only [hm_def, hs_def]
    unfold CFSG.Sporadic.SchreierLemmas.mooreOfChain mooreWord
    by_cases hj : j = 1
    · subst hj
      simp only [beq_self_eq_true, if_true, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one]
    · have hb : (j == 1) = false := beq_false_of_ne hj
      simp only [hb, hj, Bool.false_eq_true, if_false, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
  have hfixO : fixList (eTab orb) = lE := by rw [horb]; exact fix_e_lit
  have hsE : ∀ i < 6, s i * E = E * s i := fun i hi =>
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five.mem_fixList_iff rE (hlt i hi)).1 (by rw [hfixO]; exact ch10137sub i hi)
  have hmE : ∀ j, 1 ≤ j → j < 6 → m j * E = E * m j := by
    intro j hj1 hj6
    have h0 := hsE 0 (by norm_num)
    rw [hmj j]
    unfold CFSG.Sporadic.SchreierLemmas.mooreOfChain
    split_ifs with h
    · exact (Commute.mul_left h0 (hsE 1 (by norm_num))).eq
    · exact (Commute.mul_left h0 (hsE j hj6)).eq
  have hm1 : m 1 ≠ 1 := by
    rw [hmj 1]
    unfold CFSG.Sporadic.SchreierLemmas.mooreOfChain
    rw [if_pos rfl]
    exact hm1'
  have rel : ∀ {T : Table} {g : CFSG.Sporadic.Fi23.J}, CFSG.Sporadic.Th.Rep 31671 T g → g = 1 →
      eqTab T (idT 31671) = true := fun hT hg =>
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five.eqTab_of_rep hT
      (by rw [hg]; exact CFSG.Sporadic.Th.Rep.idT hn)
  change fi23FiveMooreOK orb = true
  unfold fi23FiveMooreOK mooreAt23OK mooreRelOK23
  dsimp only
  rw [hP]
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, Bool.not_eq_true']
  refine ⟨⟨⟨⟨by decide, by decide⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩, ?_⟩, ?_⟩
  · exact rel ((hm 1).powT hn 3) (by rw [hmj 1]; exact hfam.cube_one)
  · intro j hj
    by_cases h2 : j < 2
    · exact Or.inl h2
    · have e1 : m j ^ 2 = 1 := by
        rw [hmj j]
        exact hfam.sq_eq_one j (by omega) (by omega)
      have e2 : (m (j - 1) * m j) ^ 3 = 1 := by
        rw [hmj, hmj]
        exact hfam.cube_adjacent j (by omega) (by omega)
      exact Or.inr ⟨rel ((hm j).powT hn 2) e1, rel (((hm (j - 1)).compT (hm j)).powT hn 3) e2⟩
  · intro i hi j hj
    by_cases h : i < 1 ∨ j < i + 2
    · exact Or.inl h
    · refine Or.inr (rel (((hm i).compT (hm j)).powT hn 2) ?_)
      rw [hmj, hmj]
      exact hfam.sq_distant i j (by omega) (by omega) (by omega)
  · cases e : eqTab (mooreTab23 orb (dTable orb) (genTables orb (-2)) mooreP 1) (idT 31671)
    · rfl
    · exact absurd (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five.eq_of_eqTab (hm 1) (Rep.idT hn) e) hm1
  · intro j hj
    by_cases h : j < 1
    · exact Or.inl h
    · exact Or.inr (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five.eqTab_of_rep ((hm j).compT rE)
        (by rw [hmE j (by omega) hj]; exact rE.compT (hm j)))

end

end CertificateChecks.KernelFi23Five
