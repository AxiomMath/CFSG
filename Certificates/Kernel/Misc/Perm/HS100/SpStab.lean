module

public import Certificates.Kernel.Misc.Perm.HS100.SpChecks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.Sp

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KC.Misc.ArrEnum (memK)
open CertificateChecks.KernelMisc.HS100

theorem nStab : allN 11520 (fun t => !(fixOmK (N.NN.T t)) || memK S0.E0.N S0.E0.T (N.NN.T t)) =
    true := by quickRfl

end CertificateChecks.KernelMisc.HS100.Sp

end
