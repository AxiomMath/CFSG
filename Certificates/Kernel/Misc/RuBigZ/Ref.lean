module

public import Certificates.Data.Kernel.Misc.RuBigZE
public import Certificates.Data.Kernel.Misc.RuScanC
public import Certificates.Kernel.Misc.RuBigZ.Data
public import Certificates.Kernel.Misc.RuBigZ.DataE
public import Certificates.Kernel.Misc.RuScan.DataC
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

namespace CertificateChecks.KernelMisc.RuBigZ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuScan
  CertificateChecks.KernelSporSch CFSG.Quasithin.KGC31.Ru CertificateChecks.KernelMisc.RuScan

@[expose] noncomputable def wd6 (wd : List Int) (r : Nat) : Bool :=
  wordEqK 4060 12 (mask 12) (pidn 4060 12)
    (gen6 RuG.A0 RuG.A1 RuG.C0 RuG.C1 RuG.Ns0 RuG.Ns1)
    (gen6 RuG.A0I RuG.A1I RuG.C0I RuG.C1I RuG.Ns0I RuG.Ns1I) 6 wd r

@[expose] noncomputable def ch7233rb : Bool :=
  allN 21 (fun k => Nat.beq (R k) (XP (Nat.add 46 k)))

@[expose] noncomputable def hiB (m : Nat) : Nat :=
  nIf(Nat.blt m 2, 0, nIf(Nat.blt m 4, 1, nIf(Nat.blt m 8, 2, 3)))

@[expose] noncomputable def ch7233rw : Bool :=
  bAnd(Nat.beq (R 21) idP, allN 15 (fun d => strictB (Nat.succ d) (fun m =>
    strictB (hiB m) (fun i =>
      Nat.beq (R (Nat.add 21 m))
        (mulP (R (Nat.add 12 i)) (R (Nat.add 21 (Nat.sub m (Nat.shiftLeft 1 i)))))))))

@[expose] def qd (k : Nat) : Nat := [1, 0, 2, 16, 12, 13, 5, 1].getD (k - 2) 0

@[expose] def qW (k : Nat) : List Int := [xEW, x16W, x32W, g16W].getD ((k - 10) / 2) []

@[expose] noncomputable def ch7233q_ (k : Nat) : Bool :=
  bIf(Nat.blt k 2, wd6 (basisV32EW.getD k []) (Q k),
  bIf(Nat.blt k 10, Nat.beq (Q k) (R (qd k)),
  bIf(Nat.beq (Nat.mod k 2) 0, wd6 (qW k) (Q k),
    invEqK 4060 12 (mask 12) (4060 * 12) (Q (Nat.sub k 1)) (Q k))))

end CertificateChecks.KernelMisc.RuBigZ

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233rb_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233rb = true := by quickRfl

theorem CertificateChecks.KernelMisc.RuBigZ.ch7233rw_ok :
    CertificateChecks.KernelMisc.RuBigZ.ch7233rw = true := by quickRfl

#kc_each CertificateChecks.KernelMisc.RuBigZ.ch7233q_ 0 18

end
