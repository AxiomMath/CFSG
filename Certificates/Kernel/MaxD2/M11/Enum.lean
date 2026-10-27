module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
meta import Certificates.Data.M11ThreeLocal

namespace CertificateChecks.KernelMaxD2.M11

meta def rG : Array (Array Nat) :=
  Certificates.MaxD2Perm.rGens Certificates.MaxD2Perm.m11ThreeData

meta def nG : Array (Array Nat) :=
  Certificates.MaxD2Perm.nGens Certificates.MaxD2Perm.m11ThreeData

meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 11

end CertificateChecks.KernelMaxD2.M11

public section

#kpenum CertificateChecks.KernelMaxD2.M11.RE 11 4 false CertificateChecks.KernelMaxD2.M11.rG
  CertificateChecks.KernelMaxD2.M11.rG CertificateChecks.KernelMaxD2.M11.idT 9

#kpenum CertificateChecks.KernelMaxD2.M11.NE 11 4 false CertificateChecks.KernelMaxD2.M11.nG
  CertificateChecks.KernelMaxD2.M11.nG CertificateChecks.KernelMaxD2.M11.idT 144

end
