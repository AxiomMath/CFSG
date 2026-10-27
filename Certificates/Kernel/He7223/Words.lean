module

public import Certificates.Kernel.Sporadic.IntWordsCmd
public import CFSG.Quasithin.Vol2.KGFactC31HeData
public meta import CFSG.Quasithin.Vol2.KGFactC31HeData
public meta import CFSG.Assembly.QuasithinDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public meta import CFSG.Foundations
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public meta import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public meta import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public meta import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public meta import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public meta import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Components
public meta import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public meta import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.C31Insp
public meta import CFSG.Quasithin.Background.C31Insp
public import CFSG.Quasithin.Vol2.KGFactC31Cover
public meta import CFSG.Quasithin.Vol2.KGFactC31Cover
public import CFSG.Sporadic.HeldB.Common
public meta import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.J4.Simple
public meta import CFSG.Sporadic.J4.Simple
public meta import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public meta import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.ImagePairs
public meta import CFSG.Sporadic.Schreier.ImagePairs
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
public meta import Certificates.Certificate43

public section

namespace CertificateChecks.KernelHe7223

open CFSG.Quasithin.KGC31.He

meta def eM : Array (List Int) := eW.toArray

meta def qM : Array (List Int) := qW.toArray

meta def gM : Array (List Int) :=
  #[nsW.getD 6 [], nsW.getD 11 [], n7W.getD 3 [], n7W.getD 9 [], njW.getD 0 [], njW.getD 1 [],
    y5W, sigmaW, t1W, c1W.getD 5 [], c1W.getD 10 []]

meta def lM : Array (List Int) := lsGenW.toArray

end CertificateChecks.KernelHe7223

#kc_intwords CertificateChecks.KernelHe7223.EB CertificateChecks.KernelHe7223.eM
#kc_intwords CertificateChecks.KernelHe7223.QB CertificateChecks.KernelHe7223.qM
#kc_intwords CertificateChecks.KernelHe7223.GW CertificateChecks.KernelHe7223.gM
#kc_intwords CertificateChecks.KernelHe7223.LG CertificateChecks.KernelHe7223.lM

end
