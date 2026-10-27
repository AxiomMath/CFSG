module

public import Certificates.Kernel.Stroth77.MnsData
public import Certificates.Kernel.Stroth77.MnsUniqData
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelMnsU778702

open CFSG.KC.Stroth77MN CertificateChecks.KernelMns778702

theorem ch778702u_red : uRedOK tabs utabs = true := by quickRfl
theorem ch778702u_cen : uCenOK tabs utabs = true := by quickRfl
theorem ch778702u_pair : uPairOK tabs utabs = true := by quickRfl

end CertificateChecks.KernelMnsU778702
