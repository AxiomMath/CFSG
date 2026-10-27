module

public import Certificates.Kernel.Sporadic.Fi24R2W.Data
public import Certificates.Kernel.Sporadic.Fi24Net.Data
public import Certificates.Kernel.Sporadic.Fi24K.K2077
public import Certificates.Data.Kernel.Spor.Fi24R2W
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option Elab.async false

namespace CertificateChecks.KernelSpor.Fi24R2W

open CFSG.KC.Fi24R2W CFSG.KD.Fi24Net

theorem stA_t : stageOK NW (bray BA 10) SA = true := by quickRfl

theorem stB_t : stageOK NW (bray BB 13) SB = true := by quickRfl

theorem plA_t : plOK NW SA FP.F (krow (Fi24KC.S 0)) = true := by quickRfl

theorem plB_t : plOK NW SB FP.F (krow (Fi24KC.S 1)) = true := by quickRfl

end CertificateChecks.KernelSpor.Fi24R2W

end
