module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.RowsCmd
import Certificates.Kernel.Sporadic.RowsWCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.Kernel.MaxD2.GenPair
meta import Certificates.Data.Kernel.MaxD2.GenClosed
meta import Certificates.Data.HSOverData
import Certificates.Data.Kernel.MaxD2.GenClosed
import Certificates.Data.Kernel.MaxD2.GenPair

namespace CertificateChecks.KernelMaxD2.HSP

open CFSG.KS.MaxD2 Certificates.MaxD2Perm Certificates.HSOver

meta def preM : Gen.Pre := Gen.pre hsOverDataP 7

meta def gpM : Array (Array Nat) := hsOverDataP.gT
meta def gpiM : Array (Array Nat) := giT hsOverDataP
meta def ngiM : Array (Array Nat) := nGensI hsOverDataP
meta def repM : Array (Array Nat) := preM.rep
meta def repiM : Array (Array Nat) := preM.repi
meta def ptM : Array Nat := hsOverDataP.fpPts.toArray
meta def fsM : Array Nat := Gen.fpSort preM
meta def ksM : Array Nat := Gen.fpKeys preM
meta def rbM : Array Nat := Gen.repImgs hsOverDataP preM
meta def hM : Array Nat := Gen.hints hsOverDataP 7 preM
meta def cnM : Array Nat := Gen.counts hsOverDataP 7 preM
meta def rb2M : Array Nat := Gen.pairImgs hsOverDataP preM
meta def h2M : Array Nat := Gen.pairHints hsOverDataP 7 preM
meta def x1M : Array Nat := Gen.closHints hsOverDataP preM 1
meta def x2M : Array Nat := Gen.closHints hsOverDataP preM 2

end CertificateChecks.KernelMaxD2.HSP

public section

#kmisc_packarrs CertificateChecks.KernelMaxD2.HSP.GP CertificateChecks.KernelMaxD2.HSP.gpM 7
#kmisc_packarrs CertificateChecks.KernelMaxD2.HSP.GPI CertificateChecks.KernelMaxD2.HSP.gpiM 7
#kmisc_packarrs CertificateChecks.KernelMaxD2.HSP.NGI CertificateChecks.KernelMaxD2.HSP.ngiM 7
#kmisc_packarrs CertificateChecks.KernelMaxD2.HSP.REP CertificateChecks.KernelMaxD2.HSP.repM 7
#kmisc_packarrs CertificateChecks.KernelMaxD2.HSP.REPI CertificateChecks.KernelMaxD2.HSP.repiM 7
#krows CertificateChecks.KernelMaxD2.HSP.PT CertificateChecks.KernelMaxD2.HSP.ptM
#krows CertificateChecks.KernelMaxD2.HSP.FS CertificateChecks.KernelMaxD2.HSP.fsM
#krowsw CertificateChecks.KernelMaxD2.HSP.KS 21 CertificateChecks.KernelMaxD2.HSP.ksM
#krows CertificateChecks.KernelMaxD2.HSP.RB CertificateChecks.KernelMaxD2.HSP.rbM
#krows CertificateChecks.KernelMaxD2.HSP.H CertificateChecks.KernelMaxD2.HSP.hM
#krows CertificateChecks.KernelMaxD2.HSP.CN CertificateChecks.KernelMaxD2.HSP.cnM
#krows CertificateChecks.KernelMaxD2.HSP.RB2 CertificateChecks.KernelMaxD2.HSP.rb2M
#krows CertificateChecks.KernelMaxD2.HSP.H2 CertificateChecks.KernelMaxD2.HSP.h2M
#krows CertificateChecks.KernelMaxD2.HSP.X1 CertificateChecks.KernelMaxD2.HSP.x1M
#krows CertificateChecks.KernelMaxD2.HSP.X2 CertificateChecks.KernelMaxD2.HSP.x2M

end
