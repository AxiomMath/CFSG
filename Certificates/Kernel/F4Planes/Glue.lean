module

public import Certificates.Kernel.F4Planes.Rows
public import CFSG.Certificates.Kernel.F4Planes.RowSound
public import CFSG.LieType.SeitzGeneration.ExcHighThree.Closing
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsCentModel
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldAut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
public import CFSG.LocalAnalysis.ComponentClassification.GSLitType
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrCentralSylowMaximality
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.CentralLiftSO.SplitTorusWeyl
public import CFSG.RankThree.Classical.SteinbergBJSymplecticSquareZeroCentralizer
public import CFSG.RankThree.PartOne.CTP.SeitzFineExc
public import CFSG.RankThree.PartOne.CTP.SeitzFineG2
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.UnitaryHigherCrossPrimeTorus
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneEndpoints
public import CFSG.RankThree.PartOne.S11d.OutExceptional
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.KC.F4Planes

open CFSG.LieType.Simplicity.TitsBits CFSG.RankThree.PartOne.SEITZX CFSG.KC.F4Salt
  CFSG.KC.F4Syl3 CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial

#kc_forall_tree ch14950plAll (fun k => CFSG.KC.F4Planes.rowK CFSG.KD.F4Planes.VT
  CFSG.KD.F4Planes.AT CFSG.KD.F4Planes.QT CFSG.KD.F4Planes.OM CFSG.KD.F4Planes.PR
  CFSG.KD.F4Syl3.reps CFSG.KD.F4Planes.rows k = true) 48 CFSG.KD.F4Planes.ch14950pl.r

#kc_forall_tree ch14950rwAll (fun r => CFSG.KC.F4Planes.rowP CFSG.KD.F4Planes.pS
  CFSG.KD.F4Planes.PR CFSG.KD.F4Planes.gens CFSG.KD.F4Planes.tgs r = true) 67
  CFSG.KD.F4Planes.ch14950rw.r

theorem exists_conj_le_of_card {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hP : Nat.card P = 3 ^ 6) (hidx : ¬ 3 ∣ P.index) {E : Subgroup G} (hE : Nat.card E = 3 ^ 2) :
    ∃ g : G, E.map (MulAut.conj g).toMonoidHom ≤ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card hP
  obtain ⟨S, hS⟩ := (IsPGroup.of_card hE).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S (hPp.toSylow hidx)
  refine ⟨g, ?_⟩
  have := congrArg (fun S : Sylow 3 G => (S : Subgroup G)) hg
  simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at this
  rw [← this, Subgroup.pointwise_smul_def]
  exact Subgroup.map_mono hS

section Final


variable (K : Type) [Field K]

noncomputable abbrev sF (i : Fin 4) : adjointGroup ReeTag.F4.tag K :=
  pathE K CFSG.KD.F4Planes.gw CFSG.KD.F4Planes.gl (CFSG.KD.F4Planes.paths.getD i [])

noncomputable abbrev q4F : adjointGroup ReeTag.F4.tag K :=
  pathE K CFSG.KD.F4Planes.gw CFSG.KD.F4Planes.gl (CFSG.KD.F4Planes.paths.getD 4 [])

noncomputable abbrev q5F : adjointGroup ReeTag.F4.tag K :=
  pathE K CFSG.KD.F4Planes.gw CFSG.KD.F4Planes.gl (CFSG.KD.F4Planes.paths.getD 5 [])

variable [CharP K 2]

theorem hasBitsS_sF (i : Fin 4) : HasBitsS K (sF K i) (CFSG.KD.F4Planes.pS.getD i 0) :=
  pins_sound CFSG.KD.F4Planes.pin_ok (by omega : i.val < 6)

theorem hasBitsS_q4F : HasBitsS K (q4F K) (CFSG.KD.F4Planes.pS.getD 4 0) :=
  pins_sound CFSG.KD.F4Planes.pin_ok (by decide : 4 < 6)

theorem hasBitsS_q5F : HasBitsS K (q5F K) (CFSG.KD.F4Planes.pS.getD 5 0) :=
  pins_sound CFSG.KD.F4Planes.pin_ok (by decide : 5 < 6)

theorem pres_F : Pres (sF K) (q4F K) (q5F K) :=
  pres_of_relP (hasBitsS_sF K) (hasBitsS_q4F K) (hasBitsS_q5F K) CFSG.KD.F4Planes.rel_ok

end Final


theorem planeCl_F42 (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2)
    (E : Subgroup (adjointGroup .F4 K)) (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE9 : Nat.card E = 3 ^ 2) :
    CFSG.LieType.SeitzGeneration.ExcHighThree.planeCl E = ⊤ := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (k := 1)
    (le_refl 1) (by simpa using hK)
  have hp := pres_F K
  have hm := modelOK_of_chk CFSG.KD.F4Syl3.model_ok
  set P := Subgroup.closure (gensP (sF K) (q4F K) (q5F K))
  have hP : Nat.card P = 3 ^ 6 := (card_P hp hm).trans (by norm_num)
  have hG : Nat.card (adjointGroup ReeTag.F4.tag K) = 3311126603366400 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := K)
    rw [hK] at h
    exact h.trans (by norm_num [CFSG.Open.ordF4])
  have hidx : ¬ 3 ∣ P.index := by
    intro hd
    have h := P.card_mul_index
    rw [hP, hG] at h
    omega
  obtain ⟨g, hg⟩ := exists_conj_le_of_card hP hidx hE9
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := fun a b h =>
    (MulAut.conj g).injective h
  have hE₁9 : Nat.card (E.map (MulAut.conj g).toMonoidHom) = 9 :=
    (Subgroup.card_map_of_injective hinj).trans hE9
  have hE₁3 : ∀ x ∈ E.map (MulAut.conj g).toMonoidHom, x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact (map_pow (MulAut.conj g).toMonoidHom x 3).symm.trans
      ((congrArg _ (hE3 x hx)).trans (map_one _))
  obtain ⟨r, hr, z, -, hz⟩ := plane_conj hp hm CFSG.KD.F4Syl3.cover_ok CFSG.KD.F4Planes.tab_ok
    CFSG.KD.F4Planes.om_ok CFSG.KD.F4Planes.rep_ok ch14950plAll hg hE₁3 hE₁9
  have hgen := rowP_sound hK (hasBitsS_sF K) (hasBitsS_q4F K) (hasBitsS_q5F K) (ch14950rwAll r hr)
  have h1 : Subgroup.closure (zSet (E.map (MulAut.conj g).toMonoidHom)) = ⊤ := by
    refine closure_zSet_eq_top_of_map z⁻¹ ?_ hgen
    rw [hz, Subgroup.map_map]
    have hid : (MulAut.conj z⁻¹).toMonoidHom.comp (MulAut.conj z).toMonoidHom =
        MonoidHom.id _ := by
      refine MonoidHom.ext fun w => ?_
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        MonoidHom.id_apply]
      group
    rw [hid, Subgroup.map_id]
  exact closure_zSet_eq_top_of_map g rfl h1

end CFSG.KC.F4Planes

end
