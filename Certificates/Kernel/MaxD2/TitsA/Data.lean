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

namespace CertificateChecks.KernelMaxD2.TitsA

open CFSG.KS.MaxD2 Certificates.MaxD2Perm

meta def preM : Gen.Pre := Gen.pre titsAData 11

meta def ngiM : Array (Array Nat) := nGensI titsAData
meta def repM : Array (Array Nat) := preM.rep
meta def repiM : Array (Array Nat) := preM.repi
meta def ttM : Array (Array Nat) :=
  #[wT titsAData titsAData.tW, CFSG.PSL3Four.Native.invTab 1755 (wT titsAData titsAData.tW)]
meta def ptM : Array Nat := titsAData.fpPts.toArray
meta def fsM : Array Nat := Gen.fpSort preM
meta def ksM : Array Nat := Gen.fpKeys preM
meta def rbM : Array Nat := Gen.repImgs titsAData preM
meta def hM : Array Nat := Gen.hints titsAData 11 preM
meta def cnM : Array Nat := Gen.counts titsAData 11 preM
meta def chM : Array Nat := Gen.centHints titsAData preM
meta def nhM : Array Nat := Gen.normHints titsAData preM
meta def lM : Array Nat := Gen.labels titsAData
meta def mkM : Array Nat := Gen.mkeys titsAData 11 preM
meta def miscM : Array Nat :=
  #[Gen.torusPos titsAData preM, Gen.numLabels titsAData]

end CertificateChecks.KernelMaxD2.TitsA

public section

#kmisc_packarrs CertificateChecks.KernelMaxD2.TitsA.NGI CertificateChecks.KernelMaxD2.TitsA.ngiM 11
#kmisc_packarrs CertificateChecks.KernelMaxD2.TitsA.REP CertificateChecks.KernelMaxD2.TitsA.repM 11
#kmisc_packarrs CertificateChecks.KernelMaxD2.TitsA.REPI CertificateChecks.KernelMaxD2.TitsA.repiM 11
#kmisc_packarrs CertificateChecks.KernelMaxD2.TitsA.TT CertificateChecks.KernelMaxD2.TitsA.ttM 11
#krows CertificateChecks.KernelMaxD2.TitsA.PT CertificateChecks.KernelMaxD2.TitsA.ptM
#krows CertificateChecks.KernelMaxD2.TitsA.FS CertificateChecks.KernelMaxD2.TitsA.fsM
#krowsw CertificateChecks.KernelMaxD2.TitsA.KS 66 CertificateChecks.KernelMaxD2.TitsA.ksM
#krows CertificateChecks.KernelMaxD2.TitsA.RB CertificateChecks.KernelMaxD2.TitsA.rbM
#krows CertificateChecks.KernelMaxD2.TitsA.H CertificateChecks.KernelMaxD2.TitsA.hM
#krows CertificateChecks.KernelMaxD2.TitsA.CN CertificateChecks.KernelMaxD2.TitsA.cnM
#krows CertificateChecks.KernelMaxD2.TitsA.CH CertificateChecks.KernelMaxD2.TitsA.chM
#krows CertificateChecks.KernelMaxD2.TitsA.NH CertificateChecks.KernelMaxD2.TitsA.nhM
#krows CertificateChecks.KernelMaxD2.TitsA.L CertificateChecks.KernelMaxD2.TitsA.lM
#krowsw CertificateChecks.KernelMaxD2.TitsA.MK 512 CertificateChecks.KernelMaxD2.TitsA.mkM
#krows CertificateChecks.KernelMaxD2.TitsA.MISC CertificateChecks.KernelMaxD2.TitsA.miscM

end
