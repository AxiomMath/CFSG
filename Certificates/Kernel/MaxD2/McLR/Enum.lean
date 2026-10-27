module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
meta import Certificates.Data.McLFiveLocalR

namespace CertificateChecks.KernelMaxD2.McLR

meta def nG : Array (Array Nat) :=
  Certificates.MaxD2Perm.nGens Certificates.MaxD2Heis.mclFiveDataR

meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 275

end CertificateChecks.KernelMaxD2.McLR

public section

#kpenum CertificateChecks.KernelMaxD2.McLR.NE 275 9 false CertificateChecks.KernelMaxD2.McLR.nG
  CertificateChecks.KernelMaxD2.McLR.nG CertificateChecks.KernelMaxD2.McLR.idT 6000

end
