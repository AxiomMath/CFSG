module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.K36SporJ2

namespace CertificateChecks.KernelK36K.J2

open Certificates.CoreD2Perm Certificates.K36Spor

meta def gt3M : Array (Array Nat) := gT j2SData3.base
meta def gti3M : Array (Array Nat) := gTi j2SData3.base
meta def eg3M : Array (Array Nat) := eGens j2SData3.base
meta def gt5M : Array (Array Nat) := gT j2SData5.base
meta def gti5M : Array (Array Nat) := gTi j2SData5.base
meta def eg5M : Array (Array Nat) := eGens j2SData5.base
meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 315

end CertificateChecks.KernelK36K.J2

public section

#kmisc_packarrs CertificateChecks.KernelK36K.J2.GT3 CertificateChecks.KernelK36K.J2.gt3M 9
#kmisc_packarrs CertificateChecks.KernelK36K.J2.GTI3 CertificateChecks.KernelK36K.J2.gti3M 9
#kmisc_packarrs CertificateChecks.KernelK36K.J2.GT5 CertificateChecks.KernelK36K.J2.gt5M 9
#kmisc_packarrs CertificateChecks.KernelK36K.J2.GTI5 CertificateChecks.KernelK36K.J2.gti5M 9
#kmisc_packarrs CertificateChecks.KernelK36K.J2.EG5 CertificateChecks.KernelK36K.J2.eg5M 9

#kpenum CertificateChecks.KernelK36K.J2.RE3 315 9 false CertificateChecks.KernelK36K.J2.eg3M
  CertificateChecks.KernelK36K.J2.eg3M CertificateChecks.KernelK36K.J2.idT 27

end
