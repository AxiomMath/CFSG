module

public import Certificates.Data.Kernel.Fi22.LHK
public import Certificates.Kernel.Fi22LH.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22LH

open CFSG.KS.Fi22LH CFSG.KD.Fi22LH

theorem bfsA : orbBfsK QA = true := by quickRfl
theorem bfsB : orbBfsK QB = true := by quickRfl
theorem walkA : walkOK QA lb0 (fd mt 14 16383) = true := by quickRfl
theorem walkB : walkOK QB lb1 (fd mt 28 16383) = true := by quickRfl
theorem notIn : notInK QA lb1 = true := by quickRfl
theorem flat : flatK QA qa qb qbi = true := by quickRfl
theorem phi_0 : phiK op ol qa qb qbi ph 0 = true := by quickRfl
theorem phi_1 : phiK op ol qa qb qbi ph 1 = true := by quickRfl
theorem phi_2 : phiK op ol qa qb qbi ph 2 = true := by quickRfl
theorem phi_3 : phiK op ol qa qb qbi ph 3 = true := by quickRfl
theorem phi_4 : phiK op ol qa qb qbi ph 4 = true := by quickRfl
theorem phi_5 : phiK op ol qa qb qbi ph 5 = true := by quickRfl
theorem phi_6 : phiK op ol qa qb qbi ph 6 = true := by quickRfl

end CertificateChecks.KernelFi22LH
