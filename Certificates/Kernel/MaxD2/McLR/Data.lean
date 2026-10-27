module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Sporadic.RowsWCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.Kernel.MaxD2.Gen
meta import Certificates.Data.McLFiveLocalR
import Certificates.Data.Kernel.MaxD2.Gen

namespace CertificateChecks.KernelMaxD2.McLR

open CFSG.KS.MaxD2 Certificates.MaxD2Perm Certificates.MaxD2Heis

meta def preM : Gen.Pre := Gen.pre mclFiveDataR 9

meta def gpM : Array (Array Nat) := mclFiveDataR.gT
meta def gpiM : Array (Array Nat) := giT mclFiveDataR
meta def ngiM : Array (Array Nat) := nGensI mclFiveDataR
meta def repM : Array (Array Nat) := preM.rep
meta def repiM : Array (Array Nat) := preM.repi
meta def ptM : Array Nat := mclFiveDataR.fpPts.toArray
meta def fsM : Array Nat := Gen.fpSort preM
meta def ksM : Array Nat := Gen.fpKeys preM
meta def rbM : Array Nat := Gen.repImgs mclFiveDataR preM
meta def hM : Array Nat := Gen.hints mclFiveDataR 9 preM
meta def cnM : Array Nat := Gen.counts mclFiveDataR 9 preM

end CertificateChecks.KernelMaxD2.McLR

public section

#kmisc_packarrs CertificateChecks.KernelMaxD2.McLR.GP CertificateChecks.KernelMaxD2.McLR.gpM 9
#kmisc_packarrs CertificateChecks.KernelMaxD2.McLR.GPI CertificateChecks.KernelMaxD2.McLR.gpiM 9
#kmisc_packarrs CertificateChecks.KernelMaxD2.McLR.NGI CertificateChecks.KernelMaxD2.McLR.ngiM 9
#kmisc_packarrs CertificateChecks.KernelMaxD2.McLR.REP CertificateChecks.KernelMaxD2.McLR.repM 9
#kmisc_packarrs CertificateChecks.KernelMaxD2.McLR.REPI CertificateChecks.KernelMaxD2.McLR.repiM 9
#krows CertificateChecks.KernelMaxD2.McLR.PT CertificateChecks.KernelMaxD2.McLR.ptM
#krows CertificateChecks.KernelMaxD2.McLR.FS CertificateChecks.KernelMaxD2.McLR.fsM
#krowsw CertificateChecks.KernelMaxD2.McLR.KS 18 CertificateChecks.KernelMaxD2.McLR.ksM
#krows CertificateChecks.KernelMaxD2.McLR.RB CertificateChecks.KernelMaxD2.McLR.rbM
#krows CertificateChecks.KernelMaxD2.McLR.H CertificateChecks.KernelMaxD2.McLR.hM
#krows CertificateChecks.KernelMaxD2.McLR.CN CertificateChecks.KernelMaxD2.McLR.cnM

end
