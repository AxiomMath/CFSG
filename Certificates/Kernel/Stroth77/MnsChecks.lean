module

public import Certificates.Kernel.Stroth77.MnsData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelMns778702

open CFSG.KC.Stroth77MN

theorem ch778702_rel : relOK = true := by quickRfl
theorem ch778702_tab : tabOK tabs = true := by quickRfl
theorem ch778702_cl : clOK tabs = true := by quickRfl
theorem ch778702_a : aOK tabs = true := by quickRfl
theorem ch778702_na : naOK tabs = true := by quickRfl

end CertificateChecks.KernelMns778702
