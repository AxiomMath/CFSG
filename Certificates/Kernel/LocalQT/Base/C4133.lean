module

public import Certificates.Kernel.LocalQT.Base.C4133H
public import Certificates.Kernel.LocalQT.Base.C4133W
public import Certificates.Kernel.LocalQT.Base.C4133B
public import Certificates.Kernel.LocalQT.Base.C4133S
public import Certificates.Kernel.LocalQT.Base.C4133N
public import CFSG.Certificates.Kernel.LocalQTX1HSound
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

namespace CFSG.KD.LQT.C4133

open CFSG.KC.LQT.XH CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Setup.X1
open CFSG.Sporadic.HS.Native (hsData)

theorem ta'_eq : hsTa' = C4140.ta.toArray := C4140.ta_eq

theorem tb'_eq : hsTb' = C4140.tb.toArray := C4140.tb_eq

theorem valid : slpValidAux hsProg2 2 = true := by quickRfl

theorem wvalid : slpValidAux hsWprog 2 = true := by quickRfl

theorem cert : (slpValidAux hsProg2 2 = true)
    ∧ (slpValidAux hsWprog 2 = true)
    ∧ (qpOK hsData.n hsNT2 hsQp)
    ∧ (BaseEnumOK hsData.n (List.range hsData.n) hsGens2 hsGensI2 hsEnum2.1
          hsEnum2.2.1 hsEnum2.2.2)
    ∧ (hsEnum2.1.size = 2 ^ 9)
    ∧ (hsGn < hsNT2.size ∧ hsGin < hsNT2.size ∧ hsHn < hsNT2.size ∧
          hsHin < hsNT2.size ∧ hsAn < hsWNT.size ∧ hsBn < hsWNT.size)
    ∧ (invPairOK (Array.range hsData.n) hsNT2[hsGn]! hsNT2[hsGin]! = true)
    ∧ (invPairOK (Array.range hsData.n) hsNT2[hsHn]! hsNT2[hsHin]! = true)
    ∧ (normOK hsZ1 hsNT2[hsGn]! hsNT2[hsGin]! = true)
    ∧ (normOK hsQc hsNT2[hsHn]! hsNT2[hsHin]! = true)
    ∧ (notNormOK hsQc hsNT2[hsGn]! hsNT2[hsGin]! = true)
    ∧ (notNormOK hsZ1 hsNT2[hsHn]! hsNT2[hsHin]! = true)
    ∧ (hsWNT[hsAn]! = hsTa')
    ∧ (hsWNT[hsBn]! = hsTb') := by
  have hs := x1H_sound (hw := by norm_num) (h := hd) (hb := B.all) (hs := S.all)
    (hcov := by norm_num) (hN := nd) (hW := wd)
  unfold hsZ1 hsQc hsRl hsEnum2 hsGens2 hsGensI2 hsWNT hsNT2
  rw [C4140.n_eq, ta'_eq, tb'_eq]
  exact ⟨valid, wvalid, hs⟩

end CFSG.KD.LQT.C4133

end
