module

public import Certificates.Kernel.Sporadic.ONOrd.Defs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.ON5.Defs
public import Certificates.Kernel.Sporadic.ON8.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONOrd

open CertificateChecks.KernelSpor.ON8

theorem o8_ok : onP (powK o8K 8) (fun x => x) = true := by quickRfl
theorem o4_ne : (!onP (powK o8K 4) fun x => x) = true := by quickRfl

end CertificateChecks.KernelSpor.ONOrd

end
