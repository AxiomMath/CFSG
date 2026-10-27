module

public import Certificates.Data.Kernel.T84S4.Check
public import Certificates.Kernel.T84S4.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelT84S4

open CFSG.KD.T84S4

theorem ch442352_e0 : enumB ACT TM WP L3 L4 I2 S0 = true := by quickRfl
theorem ch442352_e1 : enumB ACT TM WP L3 L4 I2 S1 = true := by quickRfl
theorem ch442352_e2 : enumB ACT TM WP L3 L4 I2 S2 = true := by quickRfl
theorem ch442352_e3 : enumB ACT TM WP L3 L4 I2 S3 = true := by quickRfl
theorem ch442352_e4 : enumB ACT TM WP L3 L4 I2 S4 = true := by quickRfl
theorem ch442352_e5 : enumB ACT TM WP L3 L4 I2 S5 = true := by quickRfl
theorem ch442352_e6 : enumB ACT TM WP L3 L4 I2 S6 = true := by quickRfl
theorem ch442352_e7 : enumB ACT TM WP L3 L4 I2 S7 = true := by quickRfl

end CertificateChecks.KernelT84S4

end
