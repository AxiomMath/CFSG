module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
meta import Certificates.Data.HSOverData

namespace CertificateChecks.KernelMaxD2.HSP

meta def nG : Array (Array Nat) :=
  Certificates.MaxD2Perm.nGens Certificates.HSOver.hsOverDataP

meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 100

end CertificateChecks.KernelMaxD2.HSP

public section

#kpenum CertificateChecks.KernelMaxD2.HSP.NE 100 7 false CertificateChecks.KernelMaxD2.HSP.nG
  CertificateChecks.KernelMaxD2.HSP.nG CertificateChecks.KernelMaxD2.HSP.idT 2000

end
