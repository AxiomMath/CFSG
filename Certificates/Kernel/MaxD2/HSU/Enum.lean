module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
meta import Certificates.Data.HSFiveU35Data

namespace CertificateChecks.KernelMaxD2.HSU

meta def nG : Array (Array Nat) :=
  Certificates.MaxD2Perm.nGens Certificates.HSU35.dataU

meta def rG : Array (Array Nat) :=
  Certificates.MaxD2Perm.rGens Certificates.HSU35.dataU

meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 100

end CertificateChecks.KernelMaxD2.HSU

public section

#kpenum CertificateChecks.KernelMaxD2.HSU.NE 100 7 false CertificateChecks.KernelMaxD2.HSU.nG
  CertificateChecks.KernelMaxD2.HSU.nG CertificateChecks.KernelMaxD2.HSU.idT 1000

#kpenum CertificateChecks.KernelMaxD2.HSU.RE 100 7 false CertificateChecks.KernelMaxD2.HSU.rG
  CertificateChecks.KernelMaxD2.HSU.rG CertificateChecks.KernelMaxD2.HSU.idT 125

end
