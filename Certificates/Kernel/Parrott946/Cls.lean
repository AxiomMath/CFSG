
module

public import Certificates.Kernel.Misc.Perm.LeftOrbCmd
public import Certificates.Kernel.Parrott946.Data
meta import Certificates.Kernel.Parrott946.Data

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#conj_orb CertificateChecks.Parrott946.K1 CertificateChecks.KernelA45.gA 45 6
  CertificateChecks.KernelA45.ps 80 roots CertificateChecks.Parrott946.rS1 gens 3

#conj_orb CertificateChecks.Parrott946.K12 CertificateChecks.KernelA45.gA 45 6
  CertificateChecks.KernelA45.ps 80 roots CertificateChecks.Parrott946.rS12 gens 3

#conj_orb CertificateChecks.Parrott946.K12i CertificateChecks.KernelA45.gA 45 6
  CertificateChecks.KernelA45.ps 96 roots CertificateChecks.Parrott946.rS12i gens 3

#left_orb CertificateChecks.Parrott946.CZ CertificateChecks.Parrott946.zGen 45 6
  CertificateChecks.KernelA45.ps 108
