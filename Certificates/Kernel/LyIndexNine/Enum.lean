module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.LyIndexNine.Gens
meta import Certificates.Kernel.LyIndexNine.Gens
public import Mathlib.Init
meta import Mathlib.Init

public section

namespace CertificateChecks.KernelLy9

meta def lyM : Array (Array Nat) := lyGensA

meta def lyIdM : Array Nat := lyIdA

end CertificateChecks.KernelLy9

#kpenum CertificateChecks.KernelLy9.LYE 11 4 false CertificateChecks.KernelLy9.lyM
  CertificateChecks.KernelLy9.lyM CertificateChecks.KernelLy9.lyIdM 128

end
