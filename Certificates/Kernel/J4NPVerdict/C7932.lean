module

public import Certificates.Kernel.J4NPVerdict.Defs
public import CFSG.Milestones.ASVolI.C31.J4NP.VerdictJData
import CFSG.Certificates.Kernel.Common.EachTrue

public section

set_option maxRecDepth 400000

open CFSG.KC.J4NPV

#kc_each CertificateChecks.KernelJ4NPV vj7932c
  (fun i => chunkB (fB CertificateChecks.KernelJ4NPV.vjT) 1 CFSG.ASVolI.burnsideJ4NP_vjF i) 0 1

end
