module

public import CFSG.Sporadic.Recognition.LyonsSimsEndgame
import Certificates.Kernel.W4RowLane.Ly
import CFSG.Certificates.Kernel.SporCov.OrdP
import CFSG.Certificates.Kernel.SporCov.Words
import Certificates.Kernel.Ly3085.Seed
import Certificates.Kernel.VecCert.WordProg
import CFSG.Certificates.Kernel.Fam.LySeed.Checks.K
import Mathlib
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.GSLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
public import CFSG.Permutation.AlternatingAutomorphism
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Sporadic.Th.OrbitSpec
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
public import Certificates.Certificate3085Base

public section

namespace CFSG.KD.W4RowLane.Ly

open CFSG.KC.SporCov CFSG.KD.SporCov CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub CFSG.Sporadic.Ly

private theorem wE_pW {G : Type} [Group G] (x y : G) :
    wE (fLn x y []) pW = x * ((y * x * y * x * y) * x * (y * x * y * x * y)⁻¹) := by
  simp [pW, cjK, invK, invL, cW, wE, fLn, f4]
  group

theorem orderOf_dih67 :
    orderOf (a * ((b * a * b * a * b) * a * (b * a * b * a * b)⁻¹)) = 67 := by
  have hc := CFSG.KD.FamLySeed.consts
  have hs : CertificateChecks.KernelHomG.LayoutSound
      (fun X => validM 5 147852 CFSG.KD.FamLySeed.L CFSG.KD.FamLySeed.H X = true)
      (ordMat 5 111 12 1332) mul (validM 5 147852 CFSG.KD.FamLySeed.L CFSG.KD.FamLySeed.H)
      CFSG.KD.FamLySeed.ONE :=
    ⟨fun _ _ hA hB => mul_sound' hc rfl hA hB, (one_sound' hc rfl).1, (one_sound' hc rfl).2,
      fun _ h => h⟩
  let ρ : J →* Matrix (Fin 111) (Fin 111) (ZMod 5) :=
    (Units.coeHom (Matrix (Fin 111) (Fin 111) (ZMod 5))).comp J.subtype
  have hρ : Function.Injective ρ := mat_injective
  have vB := CertificateChecks.KernelLy.s_v2
  have vBi := (CertificateChecks.KernelWP.powR_sound hs vB 4).1
  have hA : ordMat 5 111 12 1332 (CFSG.KD.FamLySeed.RW 1) = ρ a :=
    CertificateChecks.KernelLy.s_mA.symm
  have hB : ordMat 5 111 12 1332 (CFSG.KD.FamLySeed.RW 2) = ρ b :=
    CertificateChecks.KernelLy.s_mB.symm
  obtain ⟨mw, hk, hmw⟩ := kitLn_sound hc (nb := 147852) rfl CertificateChecks.KernelLy.s_v1
    CertificateChecks.KernelLy.s_v1 vB vBi hA hB Ck.ok
  have hk' : ordPK mul CFSG.KD.FamLySeed.ONE (mw pW) 67 = true := hk
  have h := ordPK_orderOf hc rfl hρ (by norm_num) (by norm_num) (hmw pW).1 (hmw pW).2 hk'
  rwa [wE_pW] at h

theorem ly_dih67 :
    ∀ t : CFSG.Blueprint.NativeSporadic.Ly, t * t = 1 → t ≠ 1 →
      ∃ c : CFSG.Blueprint.NativeSporadic.Ly, orderOf (t * (c * t * c⁻¹)) = 67 := by
  intro t ht2 ht1
  set t₀ : CFSG.Blueprint.NativeSporadic.Ly := lyEquivJ.symm a with ht₀
  set c₀ : CFSG.Blueprint.NativeSporadic.Ly := lyEquivJ.symm (b * a * b * a * b) with hc₀
  have h₀ : orderOf (t₀ * (c₀ * t₀ * c₀⁻¹)) = 67 := by
    rw [ht₀, hc₀, ← map_inv, ← map_mul, ← map_mul, ← map_mul, MulEquiv.orderOf_eq,
      orderOf_dih67]
  have ht₀2 : orderOf t₀ = 2 := by rw [ht₀, MulEquiv.orderOf_eq, orderOf_a]
  have ht2' : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  obtain ⟨h, hh⟩ := isConj_iff.1
    (CFSG.Sporadic.Recognition.LyonsSims.ly_isConj_of_involutions ht₀2 ht2')
  refine ⟨h * c₀ * h⁻¹, ?_⟩
  have e : t * ((h * c₀ * h⁻¹) * t * (h * c₀ * h⁻¹)⁻¹) =
      MulAut.conj h (t₀ * (c₀ * t₀ * c₀⁻¹)) := by
    rw [MulAut.conj_apply, ← hh]
    group
  rw [e, MulEquiv.orderOf_eq, h₀]

end CFSG.KD.W4RowLane.Ly

end
