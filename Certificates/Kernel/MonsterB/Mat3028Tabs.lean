module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.CFSGNative.MonsterB.Co2Matrix

namespace CertificateChecks.KernelMonB.Mat3028

open CFSG.Monster.B.Co2

meta def permInvM : Array (Array Nat) := Native.permInv ()

meta def qMatM : Array (Array Nat) := (Native.genRecords ()).map (·.quotientMatrix)

meta def vecM : Array Nat := Native.vectors ()

meta def zeroM : Array Nat := Array.replicate 2300 0

end CertificateChecks.KernelMonB.Mat3028

public section

#kmisc_packarrs CertificateChecks.KernelMonB.Co2PI CertificateChecks.KernelMonB.Mat3028.permInvM 12
#kmisc_packarrs CertificateChecks.KernelMonB.Co2QM CertificateChecks.KernelMonB.Mat3028.qMatM 22
#kmisc_sortpair CertificateChecks.KernelMonB.Co2S CertificateChecks.KernelMonB.Mat3028.vecM
  CertificateChecks.KernelMonB.Mat3028.zeroM 1 2300

end
