module

import CFSG.Certificates.Kernel.Common.ForallTree
public import Certificates.Kernel.Sporadic.Fi24Seven.Glue7
import Certificates.Kernel.Sporadic.Fi24Seven.C00
import Certificates.Kernel.Sporadic.Fi24Seven.C01
import Certificates.Kernel.Sporadic.Fi24Seven.C02
import Certificates.Kernel.Sporadic.Fi24Seven.C03
import Certificates.Kernel.Sporadic.Fi24Seven.C04
import Certificates.Kernel.Sporadic.Fi24Seven.C05
import Certificates.Kernel.Sporadic.Fi24Seven.C06
import Certificates.Kernel.Sporadic.Fi24Seven.Neg

public section

namespace CertificateChecks.KernelF24S

#kc_forall_tree chunks7_ok (fun k => CFSG.KD.F24S.CK k = true) 107 CFSG.KD.F24S.ck

theorem fi7OK_true : CFSG.HardMathSupport.Dickson.I271.Fi7.fi7OK () = true := fi7OK_of chunks7_ok

end CertificateChecks.KernelF24S

end
