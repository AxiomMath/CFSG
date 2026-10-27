module

public import Certificates.Data.Kernel.LocalQT.CoreR
public import Certificates.Data.Kernel.LocalQT.PairsH
public import Certificates.Data.Kernel.LocalQT.ChainInj
public import Certificates.Data.Kernel.LocalQT.Nats
public import Certificates.Kernel.LocalQT.Core.D4119hexE
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M24Data
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Cover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
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
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import Certificates.Certificate43

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

#ks_chars CFSG.KD.LQT.C4119hexE.TR CFSG.QuasithinUnique.A5.Kc3M24Data.hexETree

public section

namespace CFSG.KD.LQT.C4119hexE

open CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.W CFSG.KC.LQT.L CFSG.KC.LQT.Syl

local notation "GL" => CFSG.KD.LQT.C4119hexE.GL

theorem hR : CFSG.KC.LQT.NP.natsOK TR.chars rTL = true := by quickRfl
theorem hE : eK 24 (eWL.map (evalWK 24 GL)) = true := by quickRfl
theorem hC : chainOK 24 C = true := by quickRfl
theorem hI : chainInj 24 C = true := by quickRfl
theorem hP : allL (nWL.map (evalWK 24 GL)) (permK 24) = true := by quickRfl
theorem hS : CFSG.KC.LQT.PH.grpS 24 C (chainF C) (nWL.map (evalWK 24 GL)) W 45 = true := by
  quickRfl
theorem hL : chainF C = 23040 := by decide +kernel
theorem hN : normK 24 (eWL.map (evalWK 24 GL)) (nWL.map (evalWK 24 GL)) = true := by quickRfl
theorem hO : orbN 24 GL (eWL.map (evalWK 24 GL)) rTL 23040 244823040 = true := by quickRfl

end CFSG.KD.LQT.C4119hexE

end
