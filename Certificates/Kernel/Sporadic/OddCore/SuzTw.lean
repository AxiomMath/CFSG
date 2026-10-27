module

public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Sporadic.RowsWCmd
public import Certificates.Data.SuzB0TwistInputs
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import Certificates.Kernel.Sporadic.OddCore.CLogGen
meta import Certificates.Data.SuzB0TwistInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.OddCore.CLogGen

public section

namespace CertificateChecks.KernelSpor.SuzTw

open CFSG.Sporadic.SuzRecog.B0TwistData

meta def relsM : Array (Array Nat) := (twRels.map List.toArray).toArray

meta def logM : CLogGen.Log := CLogGen.run 14 relsM [0, 2, 4, 6, 8, 10] 12 8192

meta def fdM : Array Nat := logM.fd
meta def fwM : Array Nat := logM.fw
meta def fsM : Array Nat := logM.fs
meta def sdM : Array Nat := logM.sd
meta def dtM : Array Nat := logM.dt
meta def rnM : Array Nat := relsM.map (·.size)
meta def nM : Array Nat := #[logM.fd.size, logM.nc, logM.fin]

end CertificateChecks.KernelSpor.SuzTw

#krowsw CertificateChecks.KernelSpor.SuzTwFD 34 CertificateChecks.KernelSpor.SuzTw.fdM
#krows CertificateChecks.KernelSpor.SuzTwFW CertificateChecks.KernelSpor.SuzTw.fwM
#krows CertificateChecks.KernelSpor.SuzTwFS CertificateChecks.KernelSpor.SuzTw.fsM
#krows CertificateChecks.KernelSpor.SuzTwSD CertificateChecks.KernelSpor.SuzTw.sdM
#krows CertificateChecks.KernelSpor.SuzTwDT CertificateChecks.KernelSpor.SuzTw.dtM
#krows CertificateChecks.KernelSpor.SuzTwRN CertificateChecks.KernelSpor.SuzTw.rnM
#krows CertificateChecks.KernelSpor.SuzTwN CertificateChecks.KernelSpor.SuzTw.nM
#kmisc_packarrs CertificateChecks.KernelSpor.SuzTwRL CertificateChecks.KernelSpor.SuzTw.relsM 4

end
