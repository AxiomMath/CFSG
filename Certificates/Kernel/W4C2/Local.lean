module

public import Certificates.Kernel.W4C2.Data
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelW4C2

open CFSG.KC.W4C2K

theorem ch330390un : (PN.filter (isCommK PN) == UN) = true := by quickRfl

theorem ch330390cl : (PM.filter (isCommK PM) == CL) = true := by quickRfl

theorem ch330390chkN : chkNK PN UN = true := by quickRfl

theorem ch330390chkM : chkMK PM CL = true := by quickRfl

theorem ch330390orb : orbWK WIT = true := by quickRfl

end CertificateChecks.KernelW4C2
