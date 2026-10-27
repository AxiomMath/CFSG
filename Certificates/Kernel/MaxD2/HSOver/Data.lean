module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Sporadic.RowsWCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.Kernel.MaxD2.GenPair
meta import Certificates.Data.HSOverData
import Certificates.Data.Kernel.MaxD2.GenPair

namespace CertificateChecks.KernelMaxD2.HSOver

open CFSG.KS.MaxD2 Certificates.MaxD2Perm Certificates.HSOver

meta def preM : Gen.Pre := Gen.pre hsOverDataR 7

meta def gpM : Array (Array Nat) := hsOverDataR.gT
meta def gpiM : Array (Array Nat) := giT hsOverDataR
meta def ngiM : Array (Array Nat) := nGensI hsOverDataR
meta def repM : Array (Array Nat) := preM.rep
meta def repiM : Array (Array Nat) := preM.repi
meta def ptM : Array Nat := hsOverDataR.fpPts.toArray
meta def fsM : Array Nat := Gen.fpSort preM
meta def ksM : Array Nat := Gen.fpKeys preM
meta def rbM : Array Nat := Gen.repImgs hsOverDataR preM
meta def hM : Array Nat := Gen.hints hsOverDataR 7 preM
meta def cnM : Array Nat := Gen.counts hsOverDataR 7 preM
meta def rb2M : Array Nat := Gen.pairImgs hsOverDataR preM
meta def h2M : Array Nat := Gen.pairHints hsOverDataR 7 preM

end CertificateChecks.KernelMaxD2.HSOver

public section

#kmisc_packarrs CertificateChecks.KernelMaxD2.HSOver.GP CertificateChecks.KernelMaxD2.HSOver.gpM 7
#kmisc_packarrs CertificateChecks.KernelMaxD2.HSOver.GPI CertificateChecks.KernelMaxD2.HSOver.gpiM 7
#kmisc_packarrs CertificateChecks.KernelMaxD2.HSOver.NGI CertificateChecks.KernelMaxD2.HSOver.ngiM 7
#kmisc_packarrs CertificateChecks.KernelMaxD2.HSOver.REP CertificateChecks.KernelMaxD2.HSOver.repM 7
#kmisc_packarrs CertificateChecks.KernelMaxD2.HSOver.REPI CertificateChecks.KernelMaxD2.HSOver.repiM 7
#krows CertificateChecks.KernelMaxD2.HSOver.PT CertificateChecks.KernelMaxD2.HSOver.ptM
#krows CertificateChecks.KernelMaxD2.HSOver.FS CertificateChecks.KernelMaxD2.HSOver.fsM
#krowsw CertificateChecks.KernelMaxD2.HSOver.KS 21 CertificateChecks.KernelMaxD2.HSOver.ksM
#krows CertificateChecks.KernelMaxD2.HSOver.RB CertificateChecks.KernelMaxD2.HSOver.rbM
#krows CertificateChecks.KernelMaxD2.HSOver.H CertificateChecks.KernelMaxD2.HSOver.hM
#krows CertificateChecks.KernelMaxD2.HSOver.CN CertificateChecks.KernelMaxD2.HSOver.cnM
#krows CertificateChecks.KernelMaxD2.HSOver.RB2 CertificateChecks.KernelMaxD2.HSOver.rb2M
#krows CertificateChecks.KernelMaxD2.HSOver.H2 CertificateChecks.KernelMaxD2.HSOver.h2M

end
