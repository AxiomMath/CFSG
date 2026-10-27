module

public import Certificates.Kernel.KGC31M24.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M24

open CFSG.Quasithin.KGC31.M24

theorem kFr0 : (List.range 128).all (frOne 12 fr0W) = true := by quickRfl

theorem kFr1 : (List.range 128).all (frOne 17 fr1W) = true := by quickRfl

theorem kFr2 : (List.range 128).all (frOne 18 fr2W) = true := by quickRfl

end CertificateChecks.KernelKGC31M24

end
