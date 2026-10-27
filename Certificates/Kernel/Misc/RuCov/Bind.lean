module

public import Certificates.Data.Kernel.Misc.RuCovB
public import Certificates.Kernel.Misc.RuCov.Data
public import Certificates.Kernel.Misc.RuScan.Data
public import Certificates.Kernel.SporSch.Ru.Gens
public import CFSG.Quasithin.Vol2.KGFactC31RuRefData
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
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

namespace CertificateChecks.KernelMisc.RuCov

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuCov
  CertificateChecks.KernelSporSch CFSG.Quasithin.KGC31.Ru

theorem ch7229z : Nat.beq (HR 0) (KernelMisc.RuScan.HP 0) = true := by quickRfl

theorem ch7229a : Nat.beq (HR 1) RuG.A0 = true := by quickRfl

@[expose] noncomputable def ch7229c_ (r : Nat) : Bool :=
  cjEq (HR (Nat.add 2 r)) (KernelMisc.RuScan.HP (Nat.succ r)) (KernelMisc.RuScan.HP 0)

@[expose] noncomputable def ch7229d_ (r : Nat) : Bool :=
  cjEq (HR (Nat.add 7 r)) (KernelMisc.RuScan.HP (Nat.add 5 r)) RuG.A0

theorem ch7229o : wordEqK 4060 12 (mask 12) (pidn 4060 12)
    (gen6 RuG.A0 RuG.A1 RuG.C0 RuG.C1 RuG.Ns0 RuG.Ns1)
    (gen6 RuG.A0I RuG.A1I RuG.C0I RuG.C1I RuG.Ns0I RuG.Ns1I) 6 (otherZW.getD 0 []) (HR 6) =
      true := by
  quickRfl

theorem ch7229p : wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 RuG.A0 RuG.A1)
    (gen2 RuG.A0I RuG.A1I) 2 (otherAW.getD 0 []) (HR 12) = true := by
  quickRfl

theorem ch7229f : bAnd(Nat.beq (fixC (HR 6)) 0, Nat.beq (fixC (HR 12)) 92) = true := by quickRfl

end CertificateChecks.KernelMisc.RuCov

#kc_each CertificateChecks.KernelMisc.RuCov.ch7229c_ 0 4
#kc_each CertificateChecks.KernelMisc.RuCov.ch7229d_ 0 5

end
