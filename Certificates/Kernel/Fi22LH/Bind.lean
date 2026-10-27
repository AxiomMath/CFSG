module

public import Certificates.Kernel.Fi22LH.Sel
public import Certificates.Data.Kernel.Fi22.Letters
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelFi22LH

open CFSG.KD.Fi22LH CFSG.KS.Fi22L

theorem al_eq : Nat.beq al (orbT 0) = true := by quickRfl
theorem be_eq : Nat.beq be (orbT 1) = true := by quickRfl
theorem op_eq : Nat.beq op (orbT 2) = true := by quickRfl
theorem ol_eq : Nat.beq ol (orbT 3) = true := by quickRfl

end CertificateChecks.KernelFi22LH
