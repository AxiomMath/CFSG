module

public import Certificates.Data.Kernel.Misc.RuScanC
public import Certificates.Kernel.Misc.RuScan.Data
public import Certificates.Kernel.Misc.RuScan.DataL
public import Certificates.Kernel.Misc.RuScan.DataC
public import Certificates.Kernel.SporSch.Ru.CData
public import Certificates.Kernel.SporSch.Ru.LChain
public import Certificates.Kernel.SporSch.Ru.Text4060
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

namespace CertificateChecks.KernelMisc.RuScan

open CFSG.KC.Misc.RuScan CertificateChecks.KernelSporSch CFSG.Quasithin.KGC31.Ru

@[expose] def ctyp (i ci : Nat) : Nat := ((candData.getD i []).getD ci (0, [])).1

@[expose] def ncand (i : Nat) : Nat := (candData.getD i []).length

@[expose] def coff (i : Nat) : Nat := [0, 5, 16, 21, 22, 22, 22, 22, 22].getD i 0

@[expose] noncomputable def ch7230q0_ (c : Nat) : Bool :=
  candC3 RuCS.LR RuCS.TR DC K0 V0 XP (ctyp 0) (ncand 0) (coff 0) (HP 1) (HP 0) 245760 0
    (Nat.mul 8 c) 8

@[expose] noncomputable def ch7230q1_ (c : Nat) : Bool :=
  candC3 RuCS.LR RuCS.TR DC K1 V1 XP (ctyp 1) (ncand 1) (coff 1) (HP 2) (HP 0) 245760 136
    (Nat.mul 8 c) 8

@[expose] noncomputable def ch7230q2_ (c : Nat) : Bool :=
  candC3 RuCS.LR RuCS.TR DC K2 V2 XP (ctyp 2) (ncand 2) (coff 2) (HP 3) (HP 0) 245760 216
    (Nat.mul 8 c) 8

@[expose] noncomputable def ch7230q3_ (c : Nat) : Bool :=
  candC3 RuCS.LR RuCS.TR DC K3 V3 XP (ctyp 3) (ncand 3) (coff 3) (HP 4) (HP 0) 245760 232
    (Nat.mul 8 c) 8

theorem ch7230q8 : candC2 RuLS.LR RuLS.TR DC K8 V8 XP (ctyp 8) (ncand 8) (coff 8) (HP 9)
    (RuT4060.L 0) 116480 256 0 6 = true := by quickRfl

end CertificateChecks.KernelMisc.RuScan

#kc_each CertificateChecks.KernelMisc.RuScan.ch7230q0_ 0 17
#kc_each CertificateChecks.KernelMisc.RuScan.ch7230q1_ 0 10
#kc_each CertificateChecks.KernelMisc.RuScan.ch7230q2_ 0 2
#kc_each CertificateChecks.KernelMisc.RuScan.ch7230q3_ 0 3

end
