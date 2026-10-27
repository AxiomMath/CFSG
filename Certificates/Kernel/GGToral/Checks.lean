module

public import Certificates.Data.Kernel.GGToral.Pk
public import Certificates.Kernel.GGToral.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelGGToral

open CFSG.KC.GGToral CFSG.KD.GGToral

set_option maxRecDepth 100000

theorem ch946001_F43 : pkCheck [2, 3, 4, 2] F43 = true := by quickRfl
theorem ch946001_E63 : pkCheck [1, 2, 2, 3, 2, 1] E63 = true := by quickRfl
theorem ch946001_E65 : pkCheck [1, 2, 2, 3, 2, 1] E65 = true := by quickRfl
theorem ch946001_E73 : pkCheck [2, 2, 3, 4, 3, 2, 1] E73 = true := by quickRfl
theorem ch946001_E75 : pkCheck [2, 2, 3, 4, 3, 2, 1] E75 = true := by quickRfl
theorem ch946001_E77 : pkCheck [2, 2, 3, 4, 3, 2, 1] E77 = true := by quickRfl
theorem ch946001_E83 : pkCheck [2, 3, 4, 6, 5, 4, 3, 2] E83 = true := by quickRfl
theorem ch946001_E85 : pkCheck [2, 3, 4, 6, 5, 4, 3, 2] E85 = true := by quickRfl
theorem ch946002_TW3 : pkCheck [] TW3 = true := by quickRfl
theorem ch946002_TW5 : pkCheck [] TW5 = true := by quickRfl
theorem ch946004_E87 : pkCheck [2, 3, 4, 6, 5, 4, 3, 2] E87 = true := by quickRfl

end CertificateChecks.KernelGGToral
