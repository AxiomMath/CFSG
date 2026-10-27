module

public import Certificates.Kernel.LocalQT.Base.C4143H
public import CFSG.Certificates.Kernel.LocalQTBaseSSound
public import Certificates.Kernel.SporSch.Ru.Sig2251P
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoKernel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4143

open CFSG.KC.LQT.BT CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Ru.Native (ruData)

theorem n_eq : (ruData ()).n = 4060 := rfl

theorem ta_eq : ruTa = ta.toArray := by
  unfold ruTa ta
  rw [n_eq]
  exact congrArg List.toArray (List.map_congr_left fun i hi =>
    (CertificateChecks.KernelSporSch.RuSig.tables i (List.mem_range.1 hi)).1)

theorem tb_eq : ruTb = tb.toArray := by
  unfold ruTb tb
  rw [n_eq]
  exact congrArg List.toArray (List.map_congr_left fun i hi =>
    (CertificateChecks.KernelSporSch.RuSig.tables i (List.mem_range.1 hi)).2)

theorem cert : BaseCertS (ruData ()).n ruB ruSLP ruQp 154 187 191 189 193 ruEnum.1 ruEnum.2.1
    ruEnum.2.2 14 := by
  unfold ruEnum ruSLP
  rw [n_eq, ta_eq, tb_eq]
  exact CFSG.KC.LQT.BS.baseS_sound (by norm_num) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PG
    hd N.all S.all

end CFSG.KD.LQT.C4143

end
