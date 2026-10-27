module

public import Certificates.Data.Kernel.SchurId
public import Certificates.Kernel.M23Mult.Words

public section

namespace CertificateChecks.KernelSchur.CoverIds

open CFSG.KC.Schur.Id CFSG.KC.Schur.Words CertificateChecks.KernelM23Mult

theorem rels : (rels6.all fun r => idOK (substK us r)) = true := by decide +kernel

theorem cover : (coverW.all fun w => idOK (substK us w)) = true := by decide +kernel

theorem cubes : (odds.all fun w => idOK (List.replicate 3 w).flatten) = true := by decide +kernel

theorem odd : ((List.range 5).all fun k =>
    idOK (odds.getD k [] ++ winvK (substK us (vs.getD k [])))) = true := by decide +kernel

theorem neg_a : idOK [(0, true)] = false := by decide +kernel

theorem neg_odd : idOK (odd0 ++ winvK (substK us v1)) = false := by decide +kernel

end CertificateChecks.KernelSchur.CoverIds

end
