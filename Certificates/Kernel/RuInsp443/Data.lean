module

public import Certificates.Kernel.SporSch.GenPerms
public import CFSG.Quasithin.Vol2.KGFactC31RuRefCheck
meta import CFSG.Quasithin.Vol2.KGFactC31RuRefCheck
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
meta import CFSG.Assembly.QuasithinDefs
meta import CFSG.Foundations
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
meta import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
meta import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
meta import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
meta import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
meta import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
meta import CFSG.LocalAnalysis.SectionRank.TitsCover
meta import CFSG.Quasithin.Background.A3Components
meta import CFSG.Quasithin.Background.A3ComponentsAmbient
meta import CFSG.Quasithin.Background.B2Thompson
meta import CFSG.Sporadic.J4.Simple
meta import CFSG.Sporadic.J4Base
meta import CFSG.Sporadic.Mathieu.M12
meta import CFSG.Sporadic.Mathieu.M24
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
meta import Certificates.Certificate43

public section

namespace CertificateChecks.KernelRuInsp

open CFSG.Quasithin.KGC31.Ru CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native

meta def xkM : Array (Array Nat) := #[xEA, ruInv xEA, ruInv ruKGensA[0]!]

meta def bvM : Array (Array Nat) := bV32EA.toArray

meta def beM : Array (Array Nat) := bEA.toArray

end CertificateChecks.KernelRuInsp

#kss_perms CertificateChecks.KernelRuInsp.XK 12 CertificateChecks.KernelRuInsp.xkM
#kss_perms CertificateChecks.KernelRuInsp.BV 12 CertificateChecks.KernelRuInsp.bvM
#kss_perms CertificateChecks.KernelRuInsp.BE 12 CertificateChecks.KernelRuInsp.beM

end
