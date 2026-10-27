module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
meta import Certificates.Data.McLFiveLocalR

namespace CertificateChecks.KernelMaxD2.McLR

meta def rG : Array (Array Nat) :=
  Certificates.MaxD2Perm.rGens Certificates.MaxD2Heis.mclFiveDataR

meta def idR : Array Nat := CFSG.PSL3Four.Native.idTab 275

end CertificateChecks.KernelMaxD2.McLR

public section

#kpenum CertificateChecks.KernelMaxD2.McLR.RE 275 9 false CertificateChecks.KernelMaxD2.McLR.rG
  CertificateChecks.KernelMaxD2.McLR.rG CertificateChecks.KernelMaxD2.McLR.idR 125

end
