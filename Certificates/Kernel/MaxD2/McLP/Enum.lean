module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
meta import Certificates.Data.McLFiveLocalP

namespace CertificateChecks.KernelMaxD2.McLP

meta def nG : Array (Array Nat) :=
  Certificates.MaxD2Perm.nGens Certificates.MaxD2Heis.mclFiveDataP

meta def rG : Array (Array Nat) :=
  Certificates.MaxD2Perm.rGens Certificates.MaxD2Heis.mclFiveDataP

meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 275

end CertificateChecks.KernelMaxD2.McLP

public section

#kpenum CertificateChecks.KernelMaxD2.McLP.NE 275 9 false CertificateChecks.KernelMaxD2.McLP.nG
  CertificateChecks.KernelMaxD2.McLP.nG CertificateChecks.KernelMaxD2.McLP.idT 3000

#kpenum CertificateChecks.KernelMaxD2.McLP.RE 275 9 false CertificateChecks.KernelMaxD2.McLP.rG
  CertificateChecks.KernelMaxD2.McLP.rG CertificateChecks.KernelMaxD2.McLP.idT 125

end
