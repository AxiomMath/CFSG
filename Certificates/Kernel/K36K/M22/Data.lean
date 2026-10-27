module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.K36SporM22

namespace CertificateChecks.KernelK36K.M22

open Certificates.CoreD2Perm Certificates.K36Spor

meta def gpM : Array (Array Nat) := gsT m22SData.base
meta def gpiM : Array (Array Nat) := giT m22SData.base
meta def gtM : Array (Array Nat) := gT m22SData.base
meta def gtiM : Array (Array Nat) := gTi m22SData.base
meta def egM : Array (Array Nat) := eGens m22SData.base

end CertificateChecks.KernelK36K.M22

public section

#kmisc_packarrs CertificateChecks.KernelK36K.M22.GP CertificateChecks.KernelK36K.M22.gpM 5
#kmisc_packarrs CertificateChecks.KernelK36K.M22.GPI CertificateChecks.KernelK36K.M22.gpiM 5
#kmisc_packarrs CertificateChecks.KernelK36K.M22.GT CertificateChecks.KernelK36K.M22.gtM 5
#kmisc_packarrs CertificateChecks.KernelK36K.M22.GTI CertificateChecks.KernelK36K.M22.gtiM 5
#kmisc_packarrs CertificateChecks.KernelK36K.M22.EG CertificateChecks.KernelK36K.M22.egM 5

end
