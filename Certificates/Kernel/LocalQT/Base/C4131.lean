module

public import CFSG.Certificates.Kernel.LocalQTRankFSound
public import Certificates.Kernel.LocalQT.Base.C4142
public import Certificates.Kernel.SporSch.Ru.RowsGen
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
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4131

open CFSG.KC.LQT.RF CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2

theorem hd : rankFH 315 9 7 C4142.ta C4142.tb j2Prog j2Qp 7 100000 128 55 7 5 = true := by
  quickRfl

@[expose] noncomputable def fam (j : Nat) : Bool :=
  rankFP 315 9 7 C4142.ta C4142.tb j2Prog j2Qp 3 128 55 (Nat.mul j 5) 5

end CFSG.KD.LQT.C4131

#kss_each CFSG.KD.LQT.C4131.P CFSG.KD.LQT.C4131.fam 7

namespace CFSG.KD.LQT.C4131

open CFSG.KC.LQT.RF CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Lin2

theorem cert : RankCert.RankCertS 315 (List.range 315) (slpTabsA j2ta.toArray j2tb.toArray j2Prog)
    j2Qp 4 j2Enum.1 j2Enum.2.1 j2Enum.2.2 7 := by
  have h := rankF_sound (by norm_num) _ _ _ _ _ 3 _ _ _ _ _ _ hd P.all
  rw [← C4142.ta_eq, ← C4142.tb_eq] at h
  exact h

end CFSG.KD.LQT.C4131

end
