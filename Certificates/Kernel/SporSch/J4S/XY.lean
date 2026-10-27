
module

public import Certificates.Kernel.SporSch.J4S.Gen
public import CFSG.Certificates.Kernel.SporSch.J4SColsSound
meta import CFSG.Sporadic.Schreier.J4SData
import CFSG.Certificates.Kernel.Common.Harness

public section

#kss_array CertificateChecks.KernelSporSch.J4X CFSG.Sporadic.J4Schreier.xColumns 11 11
#kss_array CertificateChecks.KernelSporSch.J4XI CFSG.Sporadic.J4Schreier.xInvColumns 11 11
#kss_array CertificateChecks.KernelSporSch.J4Y CFSG.Sporadic.J4Schreier.yColumns 11 11
#kss_array CertificateChecks.KernelSporSch.J4YI CFSG.Sporadic.J4Schreier.yInvColumns 11 11

namespace CertificateChecks.KernelSporSch.J4XY

open CFSG.KS.SporSch.C11 CFSG.Sporadic.J4Schreier CertificateChecks.KernelSporSch

@[expose] noncomputable def W (w : List Int) : Nat := wordColsK J4X J4XI J4Y J4YI w

theorem wordCols_eq' (w : List Int) : wordCols w = unpack11 (W w) :=
  wordCols_eq J4X.bind J4XI.bind J4Y.bind J4YI.bind w

end CertificateChecks.KernelSporSch.J4XY

end
