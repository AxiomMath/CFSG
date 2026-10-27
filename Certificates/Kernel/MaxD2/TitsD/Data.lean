module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Sporadic.RowsWCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.Kernel.MaxD2.Gen
meta import Certificates.Data.TitsFiveLocal
import Certificates.Data.Kernel.MaxD2.Gen
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Tactic.NormNum.GCD

namespace CertificateChecks.KernelMaxD2.TitsD

open CFSG.KS.MaxD2 Certificates.MaxD2Perm

meta def preM : Gen.Pre := Gen.pre titsDData 11

meta def ngiM : Array (Array Nat) := nGensI titsDData
meta def repM : Array (Array Nat) := preM.rep
meta def repiM : Array (Array Nat) := preM.repi
meta def ttM : Array (Array Nat) :=
  #[wT titsDData titsDData.tW, CFSG.PSL3Four.Native.invTab 1755 (wT titsDData titsDData.tW)]
meta def ptM : Array Nat := titsDData.fpPts.toArray
meta def fsM : Array Nat := Gen.fpSort preM
meta def ksM : Array Nat := Gen.fpKeys preM
meta def rbM : Array Nat := Gen.repImgs titsDData preM
meta def hM : Array Nat := Gen.hints titsDData 11 preM
meta def cnM : Array Nat := Gen.counts titsDData 11 preM
meta def chM : Array Nat := Gen.centHints titsDData preM
meta def nhM : Array Nat := Gen.normHints titsDData preM
meta def lM : Array Nat := Gen.labels titsDData
meta def mkM : Array Nat := Gen.mkeys titsDData 11 preM
meta def miscM : Array Nat :=
  #[Gen.torusPos titsDData preM, Gen.numLabels titsDData]

end CertificateChecks.KernelMaxD2.TitsD

public section

#kmisc_packarrs CertificateChecks.KernelMaxD2.TitsD.NGI CertificateChecks.KernelMaxD2.TitsD.ngiM 11
#kmisc_packarrs CertificateChecks.KernelMaxD2.TitsD.REP CertificateChecks.KernelMaxD2.TitsD.repM 11
#kmisc_packarrs CertificateChecks.KernelMaxD2.TitsD.REPI CertificateChecks.KernelMaxD2.TitsD.repiM 11
#kmisc_packarrs CertificateChecks.KernelMaxD2.TitsD.TT CertificateChecks.KernelMaxD2.TitsD.ttM 11
#krows CertificateChecks.KernelMaxD2.TitsD.PT CertificateChecks.KernelMaxD2.TitsD.ptM
#krows CertificateChecks.KernelMaxD2.TitsD.FS CertificateChecks.KernelMaxD2.TitsD.fsM
#krowsw CertificateChecks.KernelMaxD2.TitsD.KS 66 CertificateChecks.KernelMaxD2.TitsD.ksM
#krows CertificateChecks.KernelMaxD2.TitsD.RB CertificateChecks.KernelMaxD2.TitsD.rbM
#krows CertificateChecks.KernelMaxD2.TitsD.H CertificateChecks.KernelMaxD2.TitsD.hM
#krows CertificateChecks.KernelMaxD2.TitsD.CN CertificateChecks.KernelMaxD2.TitsD.cnM
#krows CertificateChecks.KernelMaxD2.TitsD.CH CertificateChecks.KernelMaxD2.TitsD.chM
#krows CertificateChecks.KernelMaxD2.TitsD.NH CertificateChecks.KernelMaxD2.TitsD.nhM
#krows CertificateChecks.KernelMaxD2.TitsD.L CertificateChecks.KernelMaxD2.TitsD.lM
#krowsw CertificateChecks.KernelMaxD2.TitsD.MK 512 CertificateChecks.KernelMaxD2.TitsD.mkM
#krows CertificateChecks.KernelMaxD2.TitsD.MISC CertificateChecks.KernelMaxD2.TitsD.miscM

end
