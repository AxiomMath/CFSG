module

public import Certificates.Kernel.Sporadic.Fi23Br.Rels
public import Certificates.Kernel.Sporadic.Fi23Fu.Checks
import Certificates.Kernel.Sporadic.Fi23Br.Checks
import Certificates.Kernel.Sporadic.Fi23Fu.R0
import Certificates.Kernel.Sporadic.Fi23Fu.R1
import Certificates.Kernel.Sporadic.Fi23Fu.R2
import Certificates.Kernel.Sporadic.Fi23Fu.R3
import Certificates.Kernel.Sporadic.Fi23Fu.R4
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Reps
import CFSG.Certificates.Kernel.Spor.OrdSound
import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23SylowBase
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiRefine
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.OuterRowFusion
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
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
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.Co2Schreier.ThirdChain
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
public import Certificates.Certificate8026Base
public import Certificates.Certificate9124

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Fi23Fu

#kc_forall_chunks R.all (fun r => relC r = true) 14 CFSG.KD.Fi23Fu.relC 1

end CFSG.KD.Fi23Fu

namespace CertificateChecks.KernelSpor.Fi23Fu

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.RelSeg CFSG.KD.Fi23Fu
open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th

noncomputable abbrev Mt (Y : Nat) : Matrix (Fin 253) (Fin 253) (ZMod 3) := ordMat 3 253 11 2783 Y

noncomputable abbrev N (g : Nat) : Matrix (Fin 253) (Fin 253) (ZMod 3) := Mt (RF g)

noncomputable abbrev mulF : Nat → Nat → Nat :=
  mulR (nat_lit 3) (nat_lit 11) (nat_lit 2783) (nat_lit 253) (nat_lit 8) CFSG.KD.BrFi23.L
    CFSG.KD.BrFi23.H CFSG.KD.BrFi23.CM CFSG.KD.BrFi23.RM

theorem all_rel : ∀ r < lenRels relsF,
    relOK RF mulF relsF (nat_lit 24) CFSG.KD.BrFi23.ONE r = true := by
  intro r hr
  rw [Nat.eq_of_beq_eq_true relN] at hr
  exact R.all r hr

theorem facts : (∀ g < 24, N (g + 1) * N (24 + 1 + g) = 1) ∧
    ∀ v ∈ relsF, (v.map fun x => Mt (letM RF 24 x)).prod = 1 :=
  rels_sound CFSG.KD.BrFi23.consts rfl hroots hinv relB fun r hr => Or.inl (all_rel r hr)

theorem invF {g : Nat} (hg : g < 24) : (N (g + 1))⁻¹ = N (24 + 1 + g) :=
  Matrix.inv_eq_right_inv (facts.1 g hg)

theorem bounded : ∀ v ∈ relsF, ∀ x ∈ v, x.1 < 24 := relsBounded_spec relB

theorem letF {x : Nat × Bool} (hx : x.1 < 24) :
    Mt (letM RF 24 x) = if x.2 then N (x.1 + 1) else (N (x.1 + 1))⁻¹ := by
  obtain ⟨g, s⟩ := x
  cases s
  · rw [invF hx]
    rfl
  · rfl

theorem N_br {k : Nat} (hk : k < 12) : N (k + 1) = Fi23Rels.M (k + 1) := by
  interval_cases k <;> rfl

theorem mat_list_prod (l : List CFSG.Sporadic.Fi23.J) : mat l.prod = (l.map mat).prod := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.prod_cons, mat_mul, ih, List.map_cons, List.prod_cons]

theorem mat_inv (g : CFSG.Sporadic.Fi23.J) : mat g⁻¹ = (mat g)⁻¹ := by
  simp [mat, Matrix.coe_units_inv]

theorem mat_genG (z : Int) : mat (genG z) =
    if z = 1 then mA else if z = -1 then mA⁻¹ else if z = 2 then mB else mB⁻¹ := by
  unfold genG
  split_ifs <;> simp only [mat_inv, mat_a, mat_b]

theorem mat_img {k : Nat} (hk : k < 10) :
    mat (CFSG.Sporadic.Bridge.Fi23.img k) = Fi23Rels.M (k + 1) := by
  have hk' : k < CFSG.KD.BrFi23.IT.W.length := by rw [Fi23Rels.IT_len]; exact hk
  have e : (CFSG.Sporadic.Bridge.Fi23GPL.Native.imgWords ())[k]! = CFSG.KD.BrFi23.IT.W[k] := by
    rw [Fi23Rels.img_eq, getElem!_pos CFSG.KD.BrFi23.IT.W.toArray k
      (by rw [List.size_toArray]; exact hk'), List.getElem_toArray]
  rw [← Fi23Rels.word_eq (by omega) (Fi23Rels.img_mem hk), List.map_map]
  unfold CFSG.Sporadic.Bridge.Fi23.img
  rw [wordG, mat_list_prod, List.map_map, e]
  congr 1
  apply List.map_congr_left
  intro z _
  simp only [Function.comp_apply]
  rw [Fi23Rels.seedL_mat, mat_genG]

@[expose] noncomputable def genJ (g : Nat) : CFSG.Sporadic.Fi23.J :=
  if g < 10 then CFSG.Sporadic.Bridge.Fi23.img g else if g = 10 then a else if g = 11 then b
  else gs (g - 12)

@[expose] noncomputable def letJ (x : Nat × Bool) : CFSG.Sporadic.Fi23.J := if x.2 then genJ x.1 else (genJ x.1)⁻¹

theorem chainWords_letters : ∀ j < 12, ∀ z ∈ (CFSG.Sporadic.Fi23.Native.chainWords ())[j]!,
    z ≠ 0 ∧ (z.natAbs ≤ 2 ∨ z.natAbs - 3 < j) := by
  decide

theorem chainWords_size : (CFSG.Sporadic.Fi23.Native.chainWords ()).size = 12 := by
  decide

theorem chain_mem {j : Nat} (hj : j < 12) :
    (CFSG.Sporadic.Fi23.Native.chainWords ())[j]!.map chainL ++ [(j + 12, false)] ∈ relsF := by
  unfold relsF
  apply List.mem_append_left
  rw [List.mem_map]
  have hs : j < (CFSG.Sporadic.Fi23.Native.chainWords ()).size := by
    rw [chainWords_size]
    exact hj
  refine ⟨((CFSG.Sporadic.Fi23.Native.chainWords ())[j], j),
    List.mem_zipIdx_iff_getElem?.2 (by simp [hs]), ?_⟩
  rw [getElem!_pos (CFSG.Sporadic.Fi23.Native.chainWords ()) j hs]

theorem word_eqF {u : List (Nat × Bool)} {g : Nat} (hg : g < 24) (hu : u ++ [(g, false)] ∈ relsF) :
    (u.map fun x => Mt (letM RF 24 x)).prod = N (g + 1) := by
  have h := facts.2 _ hu
  rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton] at h
  have e : Mt (letM RF 24 (g, false)) = (N (g + 1))⁻¹ := by
    rw [letF hg]
    rfl
  rw [e] at h
  have hinv : (N (g + 1))⁻¹ * N (g + 1) = 1 := by
    rw [invF hg]
    exact Fi23Rels.mul_comm_one (facts.1 g hg)
  calc (u.map fun x => Mt (letM RF 24 x)).prod
      = (u.map fun x => Mt (letM RF 24 x)).prod * ((N (g + 1))⁻¹ * N (g + 1)) := by
        rw [hinv, mul_one]
    _ = N (g + 1) := by rw [← mul_assoc, h, one_mul]

theorem N_A : N 11 = mA := by
  rw [Fi23Rels.mA_eq]
  exact N_br (k := 10) (by decide)

theorem N_B : N 12 = mB := by
  rw [Fi23Rels.mB_eq]
  exact N_br (k := 11) (by decide)

theorem N_gs : ∀ j < 12, N (j + 12 + 1) = mat (gs j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rw [← word_eqF (by omega) (chain_mem hj), gs, slpG_eq, wordG, mat_list_prod, List.map_map,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro z hz
    obtain ⟨hz0, hzl⟩ := chainWords_letters j hj z hz
    have hlt : (chainL z).1 < 24 := by
      unfold chainL
      rcases hzl with h | h <;> simp only <;> omega
    simp only [Function.comp_apply]
    rw [letF hlt]
    unfold chainL
    simp only [decide_eq_true_eq]
    by_cases h2 : z.natAbs ≤ 2
    · rw [if_pos h2, mat_genG]
      have hz4 : z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2 := by omega
      rcases hz4 with rfl | rfl | rfl | rfl <;> norm_num [N_A, N_B]
    · have h3 : z.natAbs - 3 < j := by omega
      rw [if_neg h2, if_pos h3]
      have e : z.natAbs + 9 + 1 = (z.natAbs - 3) + 12 + 1 := by omega
      rw [e, ih _ h3 (by omega)]
      by_cases hp : 0 < z
      · rw [if_pos hp, if_pos hp]
        rfl
      · rw [if_neg hp, if_neg hp, mat_inv]
        rfl

theorem N_gen {g : Nat} (hg : g < 24) : N (g + 1) = mat (genJ g) := by
  unfold genJ
  by_cases h10 : g < 10
  · rw [if_pos h10, mat_img h10]
    exact N_br (by omega)
  · rw [if_neg h10]
    by_cases ha : g = 10
    · subst ha
      rw [if_pos rfl, mat_a]
      exact N_A
    · rw [if_neg ha]
      by_cases hb : g = 11
      · subst hb
        rw [if_pos rfl, mat_b]
        exact N_B
      · rw [if_neg hb]
        have e : g + 1 = (g - 12) + 12 + 1 := by omega
        rw [e]
        exact N_gs (g - 12) (by omega)

theorem letF_J {x : Nat × Bool} (hx : x.1 < 24) : Mt (letM RF 24 x) = mat (letJ x) := by
  rw [letF hx, letJ, N_gen hx]
  cases x.2
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, mat_inv]
  · rw [if_pos rfl, if_pos rfl]

theorem relJ {v : List (Nat × Bool)} (hv : v ∈ relsF) : (v.map letJ).prod = 1 := by
  apply mat_injective
  rw [mat_list_prod, mat_one, List.map_map, ← facts.2 v hv]
  congr 1
  apply List.map_congr_left
  intro x hx
  exact (letF_J (bounded v hv x hx)).symm

@[expose] def invW (l : List (Nat × Bool)) : List (Nat × Bool) :=
  (l.map fun x => (x.1, !x.2)).reverse

theorem letJ_flip (x : Nat × Bool) : letJ (x.1, !x.2) = (letJ x)⁻¹ := by
  obtain ⟨g, s⟩ := x
  cases s <;> simp [letJ]

theorem prod_invW (l : List (Nat × Bool)) : ((invW l).map letJ).prod = ((l.map letJ).prod)⁻¹ := by
  induction l with
  | nil => simp [invW]
  | cons x l ih =>
    have e : invW (x :: l) = invW l ++ [(x.1, !x.2)] := by simp [invW]
    rw [e, List.map_append, List.prod_append, ih, List.map_singleton, List.prod_singleton,
      letJ_flip, List.map_cons, List.prod_cons, mul_inv_rev]

@[expose] noncomputable def wJ : CFSG.Sporadic.Fi23.J := (wW.map letJ).prod

@[expose] noncomputable def uJ : CFSG.Sporadic.Fi23.J := wJ ^ 4

@[expose] noncomputable def vJ : CFSG.Sporadic.Fi23.J := (vW.map letJ).prod

theorem wJ_eq : wJ = CFSG.Sporadic.Bridge.Fi23.img 1 * CFSG.Sporadic.Bridge.Fi23.img 2 *
    CFSG.Sporadic.Bridge.Fi23.img 3 * CFSG.Sporadic.Bridge.Fi23.img 4 *
    CFSG.Sporadic.Bridge.Fi23.img 7 * CFSG.Sporadic.Bridge.Fi23.img 8 := by
  simp [wJ, wW, letJ, genJ, mul_assoc]

theorem vJ_eq : vJ = CFSG.Sporadic.Bridge.Fi23.img 2 * CFSG.Sporadic.Bridge.Fi23.img 9 * CFSG.Sporadic.Fi23.b⁻¹ *
    CFSG.Sporadic.Bridge.Fi23.img 1 * CFSG.Sporadic.Fi23.a * CFSG.Sporadic.Fi23.b * CFSG.Sporadic.Bridge.Fi23.img 6 *
    CFSG.Sporadic.Bridge.Fi23.img 4 * CFSG.Sporadic.Bridge.Fi23.img 5 *
    CFSG.Sporadic.Bridge.Fi23.img 1 := by
  simp [vJ, vW, letJ, genJ, mul_assoc]

theorem uInvW_eq : uInvW = invW (wW ++ wW ++ wW ++ wW) := by decide

theorem vInvW_eq : vInvW = invW vW := by decide

theorem kleinZW_eq : kleinZW = CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native.kleinZ :=
  rfl

theorem letJ_kleinL {l : Nat} (hl : l < 24) : letJ (kleinL l) = CFSG.Perm.pairG gs l := by
  unfold letJ kleinL genJ CFSG.Perm.pairG
  have h1 : ¬ l / 2 + 12 < 10 := by omega
  have h2 : l / 2 + 12 ≠ 10 := by omega
  have h3 : l / 2 + 12 ≠ 11 := by omega
  simp only [if_neg h1, if_neg h2, if_neg h3, Nat.add_sub_cancel]
  by_cases hp : l % 2 = 0
  · rw [if_pos hp, if_pos (by rw [hp]; rfl)]
  · rw [if_neg hp, if_neg (by intro h; exact hp (Nat.eq_of_beq_eq_true h))]

theorem rel12_mem : kleinZW.map kleinL ++ vW ++ uInvW ++ vInvW ∈ relsF := by
  unfold relsF
  apply List.mem_append_right
  exact List.mem_cons_self

theorem rel13_mem : wW ++ wW ++ wW ++ wW ++ wW ++ wW ++ wW ++ wW ++ wW ++ wW ++ wW ++ wW ∈ relsF := by
  unfold relsF
  apply List.mem_append_right
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem t3_one_eq : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.t3 1 =
    vJ * uJ * vJ⁻¹ := by
  have h := relJ rel12_mem
  rw [uInvW_eq, vInvW_eq, List.map_append, List.map_append, List.map_append, List.prod_append,
    List.prod_append, List.prod_append, prod_invW, prod_invW, List.map_append, List.map_append,
    List.map_append, List.prod_append, List.prod_append, List.prod_append] at h
  have hz : (kleinZW.map kleinL).map letJ =
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native.kleinZ.map (CFSG.Perm.pairG gs) := by
    rw [List.map_map, kleinZW_eq]
    apply List.map_congr_left
    intro l hl
    have hl' : l < 24 := by
      rw [← kleinZW_eq] at hl
      revert l
      decide
    exact letJ_kleinL hl'
  rw [hz] at h
  have hu : (wW.map letJ).prod * (wW.map letJ).prod * (wW.map letJ).prod * (wW.map letJ).prod =
      uJ := by
    rw [uJ, wJ]
    simp only [pow_succ, pow_zero, one_mul]
  rw [← vJ, hu] at h
  change CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.zJ * vJ * uJ⁻¹ * vJ⁻¹ = 1 at h
  have e : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.t3 1 =
      CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.zJ := rfl
  rw [e]
  calc CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.zJ
      = CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.zJ * vJ * uJ⁻¹ * vJ⁻¹ *
          (vJ * uJ * vJ⁻¹) := by group
    _ = vJ * uJ * vJ⁻¹ := by rw [h, one_mul]

theorem uJ_cube : uJ ^ 3 = 1 := by
  have h := relJ rel13_mem
  simp only [List.map_append, List.prod_append] at h
  rw [← wJ] at h
  rw [uJ, ← pow_mul]
  calc wJ ^ (4 * 3) = wJ * wJ * wJ * wJ * wJ * wJ * wJ * wJ * wJ * wJ * wJ * wJ := by
        simp only [Nat.reduceMul, pow_succ, pow_zero, one_mul]
    _ = 1 := h

theorem isConj_uJ : IsConj uJ (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23.t3 1) := by
  rw [t3_one_eq]
  exact isConj_iff.2 ⟨vJ, rfl⟩

end CertificateChecks.KernelSpor.Fi23Fu

end
