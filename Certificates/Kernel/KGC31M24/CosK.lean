module

public import Certificates.Kernel.KGC31M24.CosDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.KGC31M24.Data7217

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M24

theorem kCosN : cosNK = true := by quickRfl

theorem kCos0 : cos0K = true := by quickRfl

end CertificateChecks.KernelKGC31M24

end
