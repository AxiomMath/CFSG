module

public import Certificates.Kernel.LyGlue.Facts2
public import Certificates.Kernel.LyGlue.Flat
public import Certificates.Kernel.LyGlue.KStep0
public import Certificates.Kernel.LyGlue.KStep1
public import Certificates.Kernel.LyGlue.KStep2
public import Certificates.Kernel.LyGlue.KStep3
public import Certificates.Kernel.LyGlue.KConj
public import CFSG.Certificates.Kernel.LyGlue.SlpSound
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Sporadic.Recognition.LyonsAmalgam
public import CFSG.Certificates.Kernel.LyGlue.WordSound
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.Statements
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitThm47Statement
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Sporadic.Recognition.CoverTransferWords
public import CFSG.Sporadic.Recognition.LyonsAmalgamModelYAut
public import CFSG.Sporadic.Recognition.LyonsModelBorel
public import CFSG.Sporadic.Recognition.McLASThreeCount
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CertificateChecks.KernelLy

open CFSG.KC.Enum CFSG.KS CFSG.KC.LyGlue CFSG.Sporadic.Recognition.LyonsSims Equiv
  CFSG.Sporadic.Recognition

#kc_forall_tree st_all (fun k => CertificateChecks.KernelLy.stepK k = true) 20
  CertificateChecks.KernelLy.st

#kc_forall_tree cj_all (fun k => CertificateChecks.KernelLy.conjK k = true) 13
  CertificateChecks.KernelLy.cj

@[expose] noncomputable def baseP (k : Nat) : Perm (Fin Ly0.deg) :=
  if k = 1 then Ly0.cG else if k = 2 then Ly0.dG else 1

theorem steps_all : ∀ s ∈ prog2, stepPt 66825 tl2 s = true := by
  intro s hs
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hs
  have hk' : k < 20 := by rw [prog2_length] at hk; exact hk
  have := st_all k hk'
  unfold stepK at this
  rwa [List.getD_eq_getElem _ _ hk] at this

theorem tl_base (h : Ly0.tabCheck = true) : ∀ k < 3, ∀ a : Fin Ly0.deg, tl k a = baseP k a := by
  intro k hk a
  interval_cases k
  · rfl
  · exact cL_eq h a
  · exact dL_eq h a

theorem tl_target (h : Ly0.tabCheck = true) {j : Nat} (hj : j < 15) (a : Fin Ly0.deg) :
    tl (tIdx j) a = (prodP baseP (expect.getD j []) a : Nat) := by
  have hB : ∀ k < 3, ∀ a : Fin Ly0.deg, tl2 k a = baseP k a :=
    fun k hk a => (tl2_lo hk a).trans (tl_base h k hk a)
  rw [← tl2_hi (tIdx_ge j hj) a, ← flat2_ok j hj]
  exact slp_sound hB (by simp [baseP]) (by norm_num) prog2_ok steps_all 23 (tIdx j + 3)
    (by have := tIdx_lt j hj; omega) (Or.inr (tIdx2_def j hj)) a

theorem baseP_one : baseP 1 = Ly0.cG := by simp [baseP]

theorem baseP_two : baseP 2 = Ly0.dG := by simp [baseP]

theorem prodP_single (k : Nat) : prodP baseP [k] = baseP k := by
  simp [prodP]

theorem prodP_cdE (h : Ly0.tabCheck = true) :
    ∀ w : List Int, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 2) →
      prodP baseP (cdE w) = Ly0.wG Ly0.gens0 w
  | [], _ => by rw [Ly0.wG_nil]; rfl
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    have ih := prodP_cdE h w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    have e : cdE (l :: w) = cdIdx l ++ cdE w := by simp only [cdE, List.flatMap_cons]
    rw [e, prodP_append, ih, Ly0.wG_cons]
    refine congrArg (· * Ly0.wG Ly0.gens0 w) ?_
    have hci : Ly0.cG⁻¹ = Ly0.cG := inv_eq_of_mul_eq_one_right (c2 h)
    have hdi : Ly0.dG⁻¹ = Ly0.dG * Ly0.dG :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact d3 h)
    have hcases : l = 1 ∨ l = -1 ∨ l = 2 ∨ l = -2 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · rw [show cdIdx 1 = [1] by decide +kernel, prodP_single, baseP_one,
        Ly0.letterG_pos _ (by norm_num), show ((1 : ℤ) - 1).toNat = 0 from rfl, Ly0.gens0_zero]
    · rw [show cdIdx (-1) = [1] by decide +kernel, prodP_single, baseP_one,
        Ly0.letterG_neg_of _ (by norm_num), show (-(-1 : ℤ) - 1).toNat = 0 from rfl,
        Ly0.gens0_zero, hci]
    · rw [show cdIdx 2 = [2] by decide +kernel, prodP_single, baseP_two,
        Ly0.letterG_pos _ (by norm_num), show ((2 : ℤ) - 1).toNat = 1 from rfl, Ly0.gens0_one]
    · rw [show cdIdx (-2) = [2, 2] by decide +kernel, Ly0.letterG_neg_of _ (by norm_num),
        show (-(-2 : ℤ) - 1).toNat = 1 from rfl, Ly0.gens0_one, hdi]
      simp [prodP, baseP_two]

theorem uWords_range' : ∀ k < 4, ∀ l ∈ Ly0.uWords.getD k [], l ≠ 0 ∧ l.natAbs ≤ 2 :=
  fun _ hk => uWords_range hk

theorem prodP_uE (h : Ly0.tabCheck = true) :
    ∀ w : List Int, (∀ l ∈ w, 0 < l ∧ l ≤ 4) →
      prodP baseP (uE w) = CFSG.Sporadic.Th.wordG (wordLetter Ly0.uG) w
  | [], _ => rfl
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    have ih := prodP_uE h w (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    have e : uE (l :: w) = (if l = 1 then [1] else cdE (Ly0.uWords.getD (l.toNat - 1) [])) ++
        uE w := by simp only [uE, List.flatMap_cons]
    rw [e, prodP_append, ih]
    change _ = wordLetter Ly0.uG l * CFSG.Sporadic.Th.wordG (wordLetter Ly0.uG) w
    refine congrArg (· * CFSG.Sporadic.Th.wordG (wordLetter Ly0.uG) w) ?_
    have hwl : wordLetter Ly0.uG l = Ly0.uG (l.toNat - 1) := by
      unfold wordLetter
      rw [if_pos hl.1]
    rw [hwl, Ly0.uG_def]
    by_cases h1 : l = 1
    · subst h1
      rw [if_pos rfl, prodP_single, baseP_one]
      change Ly0.cG = Ly0.wG Ly0.gens0 Ly0.wordU1
      rw [show Ly0.wordU1 = [1] by decide +kernel, Ly0.wG_cons, Ly0.wG_nil, mul_one,
        Ly0.letterG_pos _ (by norm_num), show ((1 : ℤ) - 1).toNat = 0 from rfl, Ly0.gens0_zero]
    · rw [if_neg h1]
      exact prodP_cdE h _ (uWords_range (by omega))

end CertificateChecks.KernelLy

end
