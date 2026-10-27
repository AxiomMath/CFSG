module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
meta import Certificates.Data.HSOverData

namespace CertificateChecks.KernelMaxD2.HSOver

meta def nG : Array (Array Nat) :=
  Certificates.MaxD2Perm.nGens Certificates.HSOver.hsOverDataR

meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 100

end CertificateChecks.KernelMaxD2.HSOver

public section

#kpenum CertificateChecks.KernelMaxD2.HSOver.NE 100 7 false CertificateChecks.KernelMaxD2.HSOver.nG
  CertificateChecks.KernelMaxD2.HSOver.nG CertificateChecks.KernelMaxD2.HSOver.idT 4000

end
