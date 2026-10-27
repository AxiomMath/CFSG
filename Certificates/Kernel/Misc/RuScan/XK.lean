module

public import Certificates.Data.Kernel.Misc.RuScanC
public import Certificates.Kernel.Misc.RuScan.DataC
public import Certificates.Kernel.SporSch.Ru.Gens
public import CFSG.Quasithin.Vol2.KGFactC31RuRefData
import CFSG.Certificates.Kernel.Common.Each
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

public section

set_option Elab.async false

namespace CertificateChecks.KernelMisc.RuScan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuScan
  CertificateChecks.KernelSporSch CFSG.Quasithin.KGC31.Ru

@[expose] def refW (t : Nat) : List (List Int) :=
  [basisEW, basis64W, basis3W, basis16W, basis32W].getD t []

@[expose] noncomputable def word6 (wd : List Int) (r : Nat) : Bool :=
  wordEqK 4060 12 (mask 12) (pidn 4060 12)
    (gen6 RuG.A0 RuG.A1 RuG.C0 RuG.C1 RuG.Ns0 RuG.Ns1)
    (gen6 RuG.A0I RuG.A1I RuG.C0I RuG.C1I RuG.Ns0I RuG.Ns1I) 6 wd r

@[expose] noncomputable def ch7230xk_ (g : Nat) : Bool :=
  bAnd(word6 (candData.flatten.getD g (0, [])).2 (XP (Nat.mul 2 g)),
    invEqK 4060 12 (mask 12) (4060 * 12) (XP (Nat.mul 2 g)) (XP (Nat.succ (Nat.mul 2 g))))

@[expose] noncomputable def ch7230xb_ (t : Nat) : Bool :=
  allN (rk t) (fun k => word6 ((refW t).getD k []) (XP (Nat.add (Nat.add 46 (boff t)) k)))

end CertificateChecks.KernelMisc.RuScan

#kc_each CertificateChecks.KernelMisc.RuScan.ch7230xk_ 0 23
#kc_each CertificateChecks.KernelMisc.RuScan.ch7230xb_ 0 5

end
