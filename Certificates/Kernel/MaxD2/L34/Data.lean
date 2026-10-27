module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Sporadic.RowsWCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.Kernel.MaxD2.GenPair
meta import Certificates.Data.L34InnerLocal
import Certificates.Data.Kernel.MaxD2.GenPair

namespace CertificateChecks.KernelMaxD2.L34

open CFSG.KS.MaxD2 Certificates.MaxD2Perm

meta def preM : Gen.Pre := Gen.pre l34InnerData 6

meta def gpM : Array (Array Nat) := l34InnerData.gT
meta def gpiM : Array (Array Nat) := giT l34InnerData
meta def ngiM : Array (Array Nat) := nGensI l34InnerData
meta def repM : Array (Array Nat) := preM.rep
meta def repiM : Array (Array Nat) := preM.repi
meta def ttM : Array (Array Nat) :=
  #[wT l34InnerData l34InnerData.tW, CFSG.PSL3Four.Native.invTab 42 (wT l34InnerData l34InnerData.tW)]
meta def ptM : Array Nat := l34InnerData.fpPts.toArray
meta def fsM : Array Nat := Gen.fpSort preM
meta def ksM : Array Nat := Gen.fpKeys preM
meta def rbM : Array Nat := Gen.repImgs l34InnerData preM
meta def hM : Array Nat := Gen.hints l34InnerData 6 preM
meta def cnM : Array Nat := Gen.counts l34InnerData 6 preM
meta def chM : Array Nat := Gen.centHints l34InnerData preM
meta def nhM : Array Nat := Gen.normHints l34InnerData preM
meta def lM : Array Nat := Gen.labels l34InnerData
meta def mkM : Array Nat := Gen.mkeys l34InnerData 6 preM
meta def miscM : Array Nat :=
  #[Gen.torusPos l34InnerData preM, Gen.numLabels l34InnerData]
meta def rb2M : Array Nat := Gen.pairImgs l34InnerData preM
meta def h2M : Array Nat := Gen.pairHints l34InnerData 6 preM

end CertificateChecks.KernelMaxD2.L34

public section

#kmisc_packarrs CertificateChecks.KernelMaxD2.L34.GP CertificateChecks.KernelMaxD2.L34.gpM 6
#kmisc_packarrs CertificateChecks.KernelMaxD2.L34.GPI CertificateChecks.KernelMaxD2.L34.gpiM 6
#kmisc_packarrs CertificateChecks.KernelMaxD2.L34.NGI CertificateChecks.KernelMaxD2.L34.ngiM 6
#kmisc_packarrs CertificateChecks.KernelMaxD2.L34.REP CertificateChecks.KernelMaxD2.L34.repM 6
#kmisc_packarrs CertificateChecks.KernelMaxD2.L34.REPI CertificateChecks.KernelMaxD2.L34.repiM 6
#kmisc_packarrs CertificateChecks.KernelMaxD2.L34.TT CertificateChecks.KernelMaxD2.L34.ttM 6
#krows CertificateChecks.KernelMaxD2.L34.PT CertificateChecks.KernelMaxD2.L34.ptM
#krows CertificateChecks.KernelMaxD2.L34.FS CertificateChecks.KernelMaxD2.L34.fsM
#krowsw CertificateChecks.KernelMaxD2.L34.KS 12 CertificateChecks.KernelMaxD2.L34.ksM
#krows CertificateChecks.KernelMaxD2.L34.RB CertificateChecks.KernelMaxD2.L34.rbM
#krows CertificateChecks.KernelMaxD2.L34.H CertificateChecks.KernelMaxD2.L34.hM
#krows CertificateChecks.KernelMaxD2.L34.CN CertificateChecks.KernelMaxD2.L34.cnM
#krows CertificateChecks.KernelMaxD2.L34.CH CertificateChecks.KernelMaxD2.L34.chM
#krows CertificateChecks.KernelMaxD2.L34.NH CertificateChecks.KernelMaxD2.L34.nhM
#krows CertificateChecks.KernelMaxD2.L34.L CertificateChecks.KernelMaxD2.L34.lM
#krowsw CertificateChecks.KernelMaxD2.L34.MK 128 CertificateChecks.KernelMaxD2.L34.mkM
#krows CertificateChecks.KernelMaxD2.L34.MISC CertificateChecks.KernelMaxD2.L34.miscM
#krows CertificateChecks.KernelMaxD2.L34.RB2 CertificateChecks.KernelMaxD2.L34.rb2M
#krows CertificateChecks.KernelMaxD2.L34.H2 CertificateChecks.KernelMaxD2.L34.h2M

end
