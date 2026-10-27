module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Sporadic.RowsWCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.Kernel.MaxD2.GenHeis
meta import Certificates.Data.HSFiveU35Data
import Certificates.Data.Kernel.MaxD2.GenHeis

namespace CertificateChecks.KernelMaxD2.HSU

open CFSG.KS.MaxD2 Certificates.MaxD2Perm Certificates.MaxD2Heis Certificates.HSU35

meta def preM : Gen.Pre := Gen.pre dataU 7

meta def preR : Gen.Pre := { preM with rT := Gen.hrTabs dataU }

meta def psM : Array (Nat × Nat) :=
  Gen.pairsBy (Gen.mkeys dataU 7 preM) (Gen.counts dataU 7 preM)

meta def gpM : Array (Array Nat) := dataU.gT
meta def gpiM : Array (Array Nat) := giT dataU
meta def ngiM : Array (Array Nat) := nGensI dataU
meta def repM : Array (Array Nat) := preM.rep
meta def repiM : Array (Array Nat) := preM.repi
meta def ptM : Array Nat := dataU.fpPts.toArray
meta def fsM : Array Nat := Gen.fpSort preM
meta def ksM : Array Nat := Gen.fpKeys preM
meta def rbM : Array Nat := Gen.repImgs dataU preM
meta def hM : Array Nat := Gen.hints dataU 7 preM
meta def cnM : Array Nat := Gen.counts dataU 7 preM
meta def ttM : Array (Array Nat) :=
  #[wT dataU dataU.tW, CFSG.PSL3Four.Native.invTab 100 (wT dataU dataU.tW)]
meta def chM : Array Nat := Gen.centHints dataU preR
meta def nhM : Array Nat := Gen.normHints dataU preR
meta def zpM : Array Nat := Gen.zPos dataU
meta def zxM : Array Nat := Gen.zIdx dataU
meta def czM : Array Nat := Gen.commHints dataU
meta def lM : Array Nat := Gen.labels dataU
meta def mkM : Array Nat := Gen.mkeys dataU 7 preM
meta def miscM : Array Nat :=
  #[Gen.numLabels dataU, psM.size, Gen.torusPos dataU preR,
    Gen.movesWit dataU preR / 2, Gen.movesWit dataU preR % 2]

end CertificateChecks.KernelMaxD2.HSU

public section

#kmisc_packarrs CertificateChecks.KernelMaxD2.HSU.GP CertificateChecks.KernelMaxD2.HSU.gpM 7
#kmisc_packarrs CertificateChecks.KernelMaxD2.HSU.GPI CertificateChecks.KernelMaxD2.HSU.gpiM 7
#kmisc_packarrs CertificateChecks.KernelMaxD2.HSU.NGI CertificateChecks.KernelMaxD2.HSU.ngiM 7
#kmisc_packarrs CertificateChecks.KernelMaxD2.HSU.REP CertificateChecks.KernelMaxD2.HSU.repM 7
#kmisc_packarrs CertificateChecks.KernelMaxD2.HSU.REPI CertificateChecks.KernelMaxD2.HSU.repiM 7
#kmisc_packarrs CertificateChecks.KernelMaxD2.HSU.TT CertificateChecks.KernelMaxD2.HSU.ttM 7
#krows CertificateChecks.KernelMaxD2.HSU.PT CertificateChecks.KernelMaxD2.HSU.ptM
#krows CertificateChecks.KernelMaxD2.HSU.FS CertificateChecks.KernelMaxD2.HSU.fsM
#krowsw CertificateChecks.KernelMaxD2.HSU.KS 700 CertificateChecks.KernelMaxD2.HSU.ksM
#krows CertificateChecks.KernelMaxD2.HSU.RB CertificateChecks.KernelMaxD2.HSU.rbM
#krows CertificateChecks.KernelMaxD2.HSU.H CertificateChecks.KernelMaxD2.HSU.hM
#krows CertificateChecks.KernelMaxD2.HSU.CN CertificateChecks.KernelMaxD2.HSU.cnM
#krows CertificateChecks.KernelMaxD2.HSU.CH CertificateChecks.KernelMaxD2.HSU.chM
#krows CertificateChecks.KernelMaxD2.HSU.NH CertificateChecks.KernelMaxD2.HSU.nhM
#krows CertificateChecks.KernelMaxD2.HSU.ZP CertificateChecks.KernelMaxD2.HSU.zpM
#krows CertificateChecks.KernelMaxD2.HSU.ZX CertificateChecks.KernelMaxD2.HSU.zxM
#krows CertificateChecks.KernelMaxD2.HSU.CZ CertificateChecks.KernelMaxD2.HSU.czM
#krows CertificateChecks.KernelMaxD2.HSU.L CertificateChecks.KernelMaxD2.HSU.lM
#krowsw CertificateChecks.KernelMaxD2.HSU.MK 64 CertificateChecks.KernelMaxD2.HSU.mkM
#krows CertificateChecks.KernelMaxD2.HSU.MISC CertificateChecks.KernelMaxD2.HSU.miscM

end
