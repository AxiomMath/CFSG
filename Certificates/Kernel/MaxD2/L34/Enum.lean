module

public import CFSG.Certificates.Kernel.Common.Loop
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
meta import Certificates.Data.L34InnerLocal

namespace CertificateChecks.KernelMaxD2.L34

meta def rG : Array (Array Nat) :=
  Certificates.MaxD2Perm.rGens Certificates.MaxD2Perm.l34InnerData

meta def nG : Array (Array Nat) :=
  Certificates.MaxD2Perm.nGens Certificates.MaxD2Perm.l34InnerData

meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 42

end CertificateChecks.KernelMaxD2.L34

public section

#kpenum CertificateChecks.KernelMaxD2.L34.RE 42 6 false CertificateChecks.KernelMaxD2.L34.rG
  CertificateChecks.KernelMaxD2.L34.rG CertificateChecks.KernelMaxD2.L34.idT 9

#kpenum CertificateChecks.KernelMaxD2.L34.NE 42 6 false CertificateChecks.KernelMaxD2.L34.nG
  CertificateChecks.KernelMaxD2.L34.nG CertificateChecks.KernelMaxD2.L34.idT 72

end
