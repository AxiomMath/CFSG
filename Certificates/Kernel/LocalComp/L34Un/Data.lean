module

public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Data.L34Unitary
meta import Certificates.Data.L34Unitary

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34UnG

open CFSG.PSL3Four.Native Certificates.L34Unitary

meta def rM : Array Nat := (enumBFS 42 gTabs 241920).tabs[86182]!

meta def f0 : Array (Array Nat) := pairGens rM 0
meta def f1 : Array (Array Nat) := pairGens rM 1
meta def f2 : Array (Array Nat) := pairGens rM 2
meta def f3 : Array (Array Nat) := pairGens rM 3
meta def f4 : Array (Array Nat) := pairGens rM 4
meta def f5 : Array (Array Nat) := pairGens rM 5

meta def e0M : Array (Array Nat) := e0Gens

meta def idM : Array Nat := idTab 42

end CertificateChecks.KernelLC.L34UnG

#kpenum CertificateChecks.KernelLC.UP0 42 6 false CertificateChecks.KernelLC.L34UnG.f0
  CertificateChecks.KernelLC.L34UnG.f0 CertificateChecks.KernelLC.L34UnG.idM 20160
#kpenum CertificateChecks.KernelLC.UP1 42 6 false CertificateChecks.KernelLC.L34UnG.f1
  CertificateChecks.KernelLC.L34UnG.f1 CertificateChecks.KernelLC.L34UnG.idM 20160
#kpenum CertificateChecks.KernelLC.UP2 42 6 false CertificateChecks.KernelLC.L34UnG.f2
  CertificateChecks.KernelLC.L34UnG.f2 CertificateChecks.KernelLC.L34UnG.idM 20160
#kpenum CertificateChecks.KernelLC.UP3 42 6 false CertificateChecks.KernelLC.L34UnG.f3
  CertificateChecks.KernelLC.L34UnG.f3 CertificateChecks.KernelLC.L34UnG.idM 20160
#kpenum CertificateChecks.KernelLC.UP4 42 6 false CertificateChecks.KernelLC.L34UnG.f4
  CertificateChecks.KernelLC.L34UnG.f4 CertificateChecks.KernelLC.L34UnG.idM 20160
#kpenum CertificateChecks.KernelLC.UP5 42 6 false CertificateChecks.KernelLC.L34UnG.f5
  CertificateChecks.KernelLC.L34UnG.f5 CertificateChecks.KernelLC.L34UnG.idM 20160
#kpenum CertificateChecks.KernelLC.UE0 42 6 false CertificateChecks.KernelLC.L34UnG.e0M
  CertificateChecks.KernelLC.L34UnG.e0M CertificateChecks.KernelLC.L34UnG.idM 9

end
