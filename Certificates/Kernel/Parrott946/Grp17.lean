module

public import Certificates.Kernel.Misc.Perm.LeftOrbCmd
public import Certificates.Kernel.Parrott946.Data17
meta import Certificates.Kernel.Parrott946.Data17

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#left_orb CertificateChecks.Parrott946.T0Z CertificateChecks.Parrott946.t0Gen17 45 6
  CertificateChecks.KernelA45.ps 64

#left_orb CertificateChecks.Parrott946.P3Z CertificateChecks.Parrott946.p3Gen 45 6
  CertificateChecks.KernelA45.ps 81

#conj_orb CertificateChecks.Parrott946.KUV CertificateChecks.KernelA45.gA 45 6
  CertificateChecks.KernelA45.ps 36 roots CertificateChecks.Parrott946.rUV gens 3
