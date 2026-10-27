module

public import Certificates.Kernel.LocalComp.Child3Gen
public import Certificates.Kernel.J2Cover.Gens
meta import Certificates.Kernel.J2Cover.Gens

public section

set_option maxRecDepth 400000

#lc_reps CertificateChecks.KernelJ2Cover.RA 9 CertificateChecks.KernelJ2Cover.crAGens
  CFSG.ComponentClassification.J2Cover.Kernel.crAReps

#lc_reps CertificateChecks.KernelJ2Cover.RPT 9 CertificateChecks.KernelJ2Cover.cpTGens
  CFSG.ComponentClassification.J2Cover.Kernel.cpTReps

#lc_reps CertificateChecks.KernelJ2Cover.RT 9 CertificateChecks.KernelJ2Cover.crTGens
  CFSG.ComponentClassification.J2Cover.Kernel.crTReps

#lc_reps CertificateChecks.KernelJ2Cover.RU 9 CertificateChecks.KernelJ2Cover.crUGens
  CFSG.ComponentClassification.J2Cover.Kernel.crUReps

end
