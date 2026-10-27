module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Sporadic.RowsWCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.Kernel.MaxD2.GenHeis
meta import Certificates.Data.McLFiveLocalP
import Certificates.Data.Kernel.MaxD2.GenHeis

namespace CertificateChecks.KernelMaxD2.McLP

open CFSG.KS.MaxD2 Certificates.MaxD2Perm Certificates.MaxD2Heis

meta def preM : Gen.Pre := Gen.pre mclFiveDataP 9

meta def preR : Gen.Pre := { preM with rT := Gen.hrTabs mclFiveDataP }

meta def psM : Array (Nat × Nat) :=
  Gen.pairsBy (Gen.mkeys mclFiveDataP 9 preM) (Gen.counts mclFiveDataP 9 preM)

meta def gpM : Array (Array Nat) := mclFiveDataP.gT
meta def gpiM : Array (Array Nat) := giT mclFiveDataP
meta def ngiM : Array (Array Nat) := nGensI mclFiveDataP
meta def repM : Array (Array Nat) := preM.rep
meta def repiM : Array (Array Nat) := preM.repi
meta def ptM : Array Nat := mclFiveDataP.fpPts.toArray
meta def fsM : Array Nat := Gen.fpSort preM
meta def ksM : Array Nat := Gen.fpKeys preM
meta def rbM : Array Nat := Gen.repImgs mclFiveDataP preM
meta def hM : Array Nat := Gen.hints mclFiveDataP 9 preM
meta def cnM : Array Nat := Gen.counts mclFiveDataP 9 preM
meta def ttM : Array (Array Nat) :=
  #[wT mclFiveDataP mclFiveDataP.tW,
    CFSG.PSL3Four.Native.invTab 275 (wT mclFiveDataP mclFiveDataP.tW)]
meta def chM : Array Nat := Gen.centHints mclFiveDataP preR
meta def nhM : Array Nat := Gen.normHints mclFiveDataP preR
meta def zpM : Array Nat := Gen.zPos mclFiveDataP
meta def zxM : Array Nat := Gen.zIdx mclFiveDataP
meta def czM : Array Nat := Gen.commHints mclFiveDataP
meta def lM : Array Nat := Gen.labels mclFiveDataP
meta def mkM : Array Nat := Gen.mkeys mclFiveDataP 9 preM
meta def miscM : Array Nat :=
  #[Gen.numLabels mclFiveDataP, psM.size, Gen.torusPos mclFiveDataP preR,
    Gen.movesWit mclFiveDataP preR / 2, Gen.movesWit mclFiveDataP preR % 2]
meta def pqM : Array Nat := Gen.pairPos preM.rep.size psM
meta def piM : Array Nat := psM.map (·.1)
meta def pjM : Array Nat := psM.map (·.2)
meta def rb2M : Array Nat := Gen.pairImgsL mclFiveDataP preM psM
meta def h2M : Array Nat := Gen.pairHintsL mclFiveDataP 9 preM psM

end CertificateChecks.KernelMaxD2.McLP

public section

#kmisc_packarrs CertificateChecks.KernelMaxD2.McLP.GP CertificateChecks.KernelMaxD2.McLP.gpM 9
#kmisc_packarrs CertificateChecks.KernelMaxD2.McLP.GPI CertificateChecks.KernelMaxD2.McLP.gpiM 9
#kmisc_packarrs CertificateChecks.KernelMaxD2.McLP.NGI CertificateChecks.KernelMaxD2.McLP.ngiM 9
#kmisc_packarrs CertificateChecks.KernelMaxD2.McLP.REP CertificateChecks.KernelMaxD2.McLP.repM 9
#kmisc_packarrs CertificateChecks.KernelMaxD2.McLP.REPI CertificateChecks.KernelMaxD2.McLP.repiM 9
#kmisc_packarrs CertificateChecks.KernelMaxD2.McLP.TT CertificateChecks.KernelMaxD2.McLP.ttM 9
#krows CertificateChecks.KernelMaxD2.McLP.PT CertificateChecks.KernelMaxD2.McLP.ptM
#krows CertificateChecks.KernelMaxD2.McLP.FS CertificateChecks.KernelMaxD2.McLP.fsM
#krowsw CertificateChecks.KernelMaxD2.McLP.KS 18 CertificateChecks.KernelMaxD2.McLP.ksM
#krows CertificateChecks.KernelMaxD2.McLP.RB CertificateChecks.KernelMaxD2.McLP.rbM
#krows CertificateChecks.KernelMaxD2.McLP.H CertificateChecks.KernelMaxD2.McLP.hM
#krows CertificateChecks.KernelMaxD2.McLP.CN CertificateChecks.KernelMaxD2.McLP.cnM
#krows CertificateChecks.KernelMaxD2.McLP.CH CertificateChecks.KernelMaxD2.McLP.chM
#krows CertificateChecks.KernelMaxD2.McLP.NH CertificateChecks.KernelMaxD2.McLP.nhM
#krows CertificateChecks.KernelMaxD2.McLP.ZP CertificateChecks.KernelMaxD2.McLP.zpM
#krows CertificateChecks.KernelMaxD2.McLP.ZX CertificateChecks.KernelMaxD2.McLP.zxM
#krows CertificateChecks.KernelMaxD2.McLP.CZ CertificateChecks.KernelMaxD2.McLP.czM
#krows CertificateChecks.KernelMaxD2.McLP.L CertificateChecks.KernelMaxD2.McLP.lM
#krowsw CertificateChecks.KernelMaxD2.McLP.MK 64 CertificateChecks.KernelMaxD2.McLP.mkM
#krows CertificateChecks.KernelMaxD2.McLP.MISC CertificateChecks.KernelMaxD2.McLP.miscM
#krows CertificateChecks.KernelMaxD2.McLP.PQ CertificateChecks.KernelMaxD2.McLP.pqM
#krows CertificateChecks.KernelMaxD2.McLP.PI CertificateChecks.KernelMaxD2.McLP.piM
#krows CertificateChecks.KernelMaxD2.McLP.PJ CertificateChecks.KernelMaxD2.McLP.pjM
#krows CertificateChecks.KernelMaxD2.McLP.RB2 CertificateChecks.KernelMaxD2.McLP.rb2M
#krows CertificateChecks.KernelMaxD2.McLP.H2 CertificateChecks.KernelMaxD2.McLP.h2M

end
