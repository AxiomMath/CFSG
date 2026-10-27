
module

public import Certificates.Kernel.J4Q.QT2A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2AInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Reps2B0
import Certificates.Kernel.J4Q.Strs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Inv
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Aux
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2CertBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2CoreBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2EVBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4FinalBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4HBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Parts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4PlanBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Reps2A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3StructureBasic
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.C1GNInputs
public import CFSG.Quasithin.Background.C1GNNotation
public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Sporadic.J4.QT2ARad
public import CFSG.Sporadic.J4.QT2LocCntMainBase
public import CFSG.Sporadic.J4.QT2LocEInterBase
public import CFSG.Sporadic.J4.QT2LocHMain
public import CFSG.Sporadic.J4.QT2LocMainBase
public import CFSG.Sporadic.J4.QT2LocRadMainBase
public import CFSG.Sporadic.J4.QT2LocUniqBase
public import CFSG.Sporadic.J4.QT2LocUniqCheck
public import CFSG.Sporadic.J4.QT2LocX0NMainBase
public import CFSG.Sporadic.J4.QT2LocZProof
public import CFSG.Sporadic.J4.QTOutChar
public import CFSG.Sporadic.J4.QTRankInvProof
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import Certificates.Certificate43

public section

set_option maxRecDepth 400000

#j4q_strs CFSG.KD.J4Q.A9W CFSG.QuasithinUnique.A5.a941Words
#j4q_strs CFSG.KD.J4Q.A8W CFSG.QuasithinUnique.A5.a85Words
#j4q_strs CFSG.KD.J4Q.B1W CFSG.QuasithinUnique.A5.b1344Words
#j4q_strs CFSG.KD.J4Q.A9Q CFSG.QuasithinUnique.A5.a941q
#j4q_strs CFSG.KD.J4Q.A8Q CFSG.QuasithinUnique.A5.a85q

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q

@[expose] noncomputable def d2A9W : List (List Int) := [
  w5K (List.flatten [A9W.s0, A9W.s1, A9W.s2, A9W.s3]),
  w5K (List.flatten [A9W.s4, A9W.s5, A9W.s6, A9W.s7]),
  w5K (List.flatten [A9W.s8, A9W.s9, A9W.s10, A9W.s11, A9W.s12, A9W.s13]),
  w5K (List.flatten [A9W.s14, A9W.s15, A9W.s16])]

@[expose] noncomputable def d2A8W : List (List Int) := [
  w5K (List.flatten [A8W.s0, A8W.s1, A8W.s2, A8W.s3, A8W.s4, A8W.s5, A8W.s6,
    A8W.s7, A8W.s8, A8W.s9, A8W.s10, A8W.s11, A8W.s12, A8W.s13,
    A8W.s14, A8W.s15]),
  w5K (List.flatten [A8W.s16, A8W.s17, A8W.s18, A8W.s19, A8W.s20, A8W.s21, A8W.s22,
    A8W.s23, A8W.s24, A8W.s25, A8W.s26, A8W.s27, A8W.s28, A8W.s29,
    A8W.s30, A8W.s31, A8W.s32, A8W.s33]),
  w5K (List.flatten [A8W.s34, A8W.s35, A8W.s36, A8W.s37, A8W.s38, A8W.s39, A8W.s40,
    A8W.s41, A8W.s42, A8W.s43, A8W.s44, A8W.s45, A8W.s46, A8W.s47,
    A8W.s48, A8W.s49, A8W.s50, A8W.s51]),
  w5K (List.flatten [A8W.s52, A8W.s53, A8W.s54, A8W.s55, A8W.s56, A8W.s57, A8W.s58,
    A8W.s59, A8W.s60, A8W.s61, A8W.s62, A8W.s63, A8W.s64, A8W.s65,
    A8W.s66, A8W.s67, A8W.s68, A8W.s69])]

@[expose] noncomputable def d2B1W : List (List Int) := [
  w5K (List.flatten [B1W.s0, B1W.s1, B1W.s2]),
  w5K (List.flatten [B1W.s3, B1W.s4, B1W.s5]),
  w5K (List.flatten [B1W.s6, B1W.s7, B1W.s8]),
  w5K (List.flatten [B1W.s9, B1W.s10, B1W.s11])]

@[expose] noncomputable def d2A9Q : List Int :=
  w5K (List.flatten [A9Q.s0, A9Q.s1, A9Q.s2, A9Q.s3, A9Q.s4, A9Q.s5, A9Q.s6,
    A9Q.s7, A9Q.s8, A9Q.s9, A9Q.s10, A9Q.s11, A9Q.s12, A9Q.s13,
    A9Q.s14, A9Q.s15, A9Q.s16, A9Q.s17, A9Q.s18, A9Q.s19, A9Q.s20,
    A9Q.s21, A9Q.s22, A9Q.s23, A9Q.s24, A9Q.s25, A9Q.s26, A9Q.s27,
    A9Q.s28, A9Q.s29, A9Q.s30, A9Q.s31, A9Q.s32, A9Q.s33, A9Q.s34,
    A9Q.s35, A9Q.s36, A9Q.s37, A9Q.s38, A9Q.s39, A9Q.s40])

@[expose] noncomputable def d2A8Q : List Int :=
  w5K (List.flatten [A8Q.s0, A8Q.s1, A8Q.s2, A8Q.s3, A8Q.s4, A8Q.s5, A8Q.s6,
    A8Q.s7, A8Q.s8, A8Q.s9, A8Q.s10, A8Q.s11, A8Q.s12, A8Q.s13,
    A8Q.s14, A8Q.s15])

end CertificateChecks.KernelJ4Q

end
