module

public import Certificates.Kernel.Sporadic.RawTreeGen
public import Certificates.Data.Kernel.Misc.M64Chain
public import CFSG.Quasithin.Vol2.KGFactC31RuConfCheck
public meta import CFSG.Quasithin.Vol2.KGFactC31RuConfCheck
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Assembly.QuasithinDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public meta import CFSG.Foundations
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public meta import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public meta import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public meta import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public meta import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public meta import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public meta import CFSG.Quasithin.Background.A3ComponentsAmbient
public meta import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Sporadic.HeldB.Common
public meta import CFSG.Sporadic.HeldB.Common
public meta import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public meta import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public meta import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
public meta import Certificates.Certificate43

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam.Ru7234

meta def baseX : Array Nat := #[0, 1, 2, 3]

end CertificateChecks.KernelSchreierFam.Ru7234

#ks_rawtree CertificateChecks.KernelSchreierFam.Ru7234X 4060 12 64 64 0
  CFSG.Quasithin.KGC31.Ru.m64S CertificateChecks.KernelSchreierFam.Ru7234.baseX 5
  CFSG.KC.Misc.M64.dM64

end
