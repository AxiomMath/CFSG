module

public import Certificates.Data.Kernel.GGToral.PkTag
public import Certificates.Kernel.GGToral.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelGGToral

open CFSG.KC.GGToral CFSG.KD.GGToral CFSG.Blueprint.Chevalley

set_option maxRecDepth 100000

theorem ch946001_tag_F43 : pkTag .F4 3 0 F43 = true := by quickRfl
theorem ch946001_tag_E63 : pkTag .E6 3 0 E63 = true := by quickRfl
theorem ch946001_tag_E65 : pkTag .E6 5 0 E65 = true := by quickRfl
theorem ch946001_tag_E73 : pkTag .E7 3 0 E73 = true := by quickRfl
theorem ch946001_tag_E75 : pkTag .E7 5 0 E75 = true := by quickRfl
theorem ch946001_tag_E77 : pkTag .E7 7 0 E77 = true := by quickRfl
theorem ch946001_tag_E83 : pkTag .E8 3 0 E83 = true := by quickRfl
theorem ch946001_tag_E85 : pkTag .E8 5 0 E85 = true := by quickRfl
theorem ch946002_tag_TW3 : pkTag .E6 3 1 TW3 = true := by quickRfl
theorem ch946002_tag_TW5 : pkTag .E6 5 1 TW5 = true := by quickRfl
theorem ch946004_tag_E87 : pkTag .E8 7 0 E87 = true := by quickRfl

end CertificateChecks.KernelGGToral
