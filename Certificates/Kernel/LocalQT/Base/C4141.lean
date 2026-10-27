module

public import Certificates.Kernel.LocalQT.Base.C4141H
public import CFSG.Certificates.Kernel.LocalQTBaseSSound
public import Certificates.Kernel.He4049.Orb
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
public import CFSG.Sporadic.Schreier.LyCheckSeven
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

set_option maxRecDepth 100000

public section

namespace CFSG.KD.LQT.C4141

open CFSG.KC.LQT.BT CFSG.QuasithinUnique.K1.SporadicPerm

theorem ta_eq : heTa = ta.toArray := CFSG.KD.He4049.heTa_eq

theorem tb_eq : heTb = tb.toArray := CFSG.KD.He4049.heTb_eq

theorem cert : BaseCertS 8330 heB heSLP heQp 170 249 253 251 255 heEnum.1 heEnum.2.1 heEnum.2.2
    10 := by
  unfold heEnum heSLP
  rw [ta_eq, tb_eq]
  exact CFSG.KC.LQT.BS.baseS_sound (by norm_num) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ PG
    hd N.all S.all

end CFSG.KD.LQT.C4141

end
