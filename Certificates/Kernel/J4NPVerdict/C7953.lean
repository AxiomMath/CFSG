module

public import Certificates.Kernel.J4NPVerdict.Defs
import CFSG.Certificates.Kernel.Common.EachTrue

public section

set_option maxRecDepth 400000

open CFSG.KC.J4NPV CFSG.J4Tree.M4

#kc_each CertificateChecks.KernelJ4NPV vj7953c
  (fun i => chunkB (conjB CertificateChecks.KernelJ4NPV.vjT (CFSG.J4Tree.Native.treeWv 539)) 4
    [c486, c542, c136, c266] i) 0 1

end
