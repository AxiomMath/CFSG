module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Sporadic.RowsWCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.Kernel.MaxD2.Gen
meta import Certificates.Data.M11ThreeLocal
import Certificates.Data.Kernel.MaxD2.Gen

namespace CertificateChecks.KernelMaxD2.M11

open CFSG.KS.MaxD2 Certificates.MaxD2Perm

meta def preM : Gen.Pre := Gen.pre m11ThreeData 4

meta def gpM : Array (Array Nat) := m11ThreeData.gT
meta def gpiM : Array (Array Nat) := giT m11ThreeData
meta def ngiM : Array (Array Nat) := nGensI m11ThreeData
meta def repM : Array (Array Nat) := preM.rep
meta def repiM : Array (Array Nat) := preM.repi
meta def ttM : Array (Array Nat) :=
  #[wT m11ThreeData m11ThreeData.tW, CFSG.PSL3Four.Native.invTab 11 (wT m11ThreeData m11ThreeData.tW)]
meta def ptM : Array Nat := m11ThreeData.fpPts.toArray
meta def fsM : Array Nat := Gen.fpSort preM
meta def ksM : Array Nat := Gen.fpKeys preM
meta def rbM : Array Nat := Gen.repImgs m11ThreeData preM
meta def hM : Array Nat := Gen.hints m11ThreeData 4 preM
meta def cnM : Array Nat := Gen.counts m11ThreeData 4 preM
meta def chM : Array Nat := Gen.centHints m11ThreeData preM
meta def nhM : Array Nat := Gen.normHints m11ThreeData preM
meta def lM : Array Nat := Gen.labels m11ThreeData
meta def mkM : Array Nat := Gen.mkeys m11ThreeData 4 preM
meta def miscM : Array Nat :=
  #[Gen.torusPos m11ThreeData preM, Gen.numLabels m11ThreeData]

end CertificateChecks.KernelMaxD2.M11

public section

#kmisc_packarrs CertificateChecks.KernelMaxD2.M11.GP CertificateChecks.KernelMaxD2.M11.gpM 4
#kmisc_packarrs CertificateChecks.KernelMaxD2.M11.GPI CertificateChecks.KernelMaxD2.M11.gpiM 4
#kmisc_packarrs CertificateChecks.KernelMaxD2.M11.NGI CertificateChecks.KernelMaxD2.M11.ngiM 4
#kmisc_packarrs CertificateChecks.KernelMaxD2.M11.REP CertificateChecks.KernelMaxD2.M11.repM 4
#kmisc_packarrs CertificateChecks.KernelMaxD2.M11.REPI CertificateChecks.KernelMaxD2.M11.repiM 4
#kmisc_packarrs CertificateChecks.KernelMaxD2.M11.TT CertificateChecks.KernelMaxD2.M11.ttM 4
#krows CertificateChecks.KernelMaxD2.M11.PT CertificateChecks.KernelMaxD2.M11.ptM
#krows CertificateChecks.KernelMaxD2.M11.FS CertificateChecks.KernelMaxD2.M11.fsM
#krowsw CertificateChecks.KernelMaxD2.M11.KS 16 CertificateChecks.KernelMaxD2.M11.ksM
#krows CertificateChecks.KernelMaxD2.M11.RB CertificateChecks.KernelMaxD2.M11.rbM
#krows CertificateChecks.KernelMaxD2.M11.H CertificateChecks.KernelMaxD2.M11.hM
#krows CertificateChecks.KernelMaxD2.M11.CN CertificateChecks.KernelMaxD2.M11.cnM
#krows CertificateChecks.KernelMaxD2.M11.CH CertificateChecks.KernelMaxD2.M11.chM
#krows CertificateChecks.KernelMaxD2.M11.NH CertificateChecks.KernelMaxD2.M11.nhM
#krows CertificateChecks.KernelMaxD2.M11.L CertificateChecks.KernelMaxD2.M11.lM
#krowsw CertificateChecks.KernelMaxD2.M11.MK 64 CertificateChecks.KernelMaxD2.M11.mkM
#krows CertificateChecks.KernelMaxD2.M11.MISC CertificateChecks.KernelMaxD2.M11.miscM

end
