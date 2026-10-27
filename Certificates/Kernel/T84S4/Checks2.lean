module

public import Certificates.Data.Kernel.T84S4.Check
public import Certificates.Kernel.T84S4.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelT84S4

open CFSG.KD.T84S4

theorem ch442352_rels : relsB ACT TM = true := by quickRfl
theorem ch442352_bound : boundB ACT TM = true := by quickRfl
theorem ch442352_inj : injB TC = true := by quickRfl
theorem ch442352_jeq : jEqB TC = true := by quickRfl
theorem ch442352_tc : tcB TC = true := by quickRfl
theorem ch442352_jk : jkB TC = true := by quickRfl

end CertificateChecks.KernelT84S4

end
