module

public import Certificates.Data.Kernel.GGToral.Pk
public import Certificates.Kernel.GGToral.Data
public import CFSG.Blueprint.ChevalleyRootsInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelGGToral

open CFSG.KC.GGToral CFSG.KD.GGToral CFSG.Blueprint.Chevalley

set_option maxRecDepth 100000

theorem ch946001_hd_F43 : pkHead (Tag.rootCertificate .F4).roots F43 = true := by quickRfl
theorem ch946001_hd_E63 : pkHead (Tag.rootCertificate .E6).roots E63 = true := by quickRfl
theorem ch946001_hd_E65 : pkHead (Tag.rootCertificate .E6).roots E65 = true := by quickRfl
theorem ch946001_hd_E73 : pkHead (Tag.rootCertificate .E7).roots E73 = true := by quickRfl
theorem ch946001_hd_E75 : pkHead (Tag.rootCertificate .E7).roots E75 = true := by quickRfl
theorem ch946001_hd_E77 : pkHead (Tag.rootCertificate .E7).roots E77 = true := by quickRfl
theorem ch946001_hd_E83 : pkHead (Tag.rootCertificate .E8).roots E83 = true := by quickRfl
theorem ch946001_hd_E85 : pkHead (Tag.rootCertificate .E8).roots E85 = true := by quickRfl
theorem ch946002_hd_TW3 : pkHead (Tag.rootCertificate .E6).roots TW3 = true := by quickRfl
theorem ch946002_hd_TW5 : pkHead (Tag.rootCertificate .E6).roots TW5 = true := by quickRfl
theorem ch946004_hd_E87 : pkHead (Tag.rootCertificate .E8).roots E87 = true := by quickRfl

end CertificateChecks.KernelGGToral
