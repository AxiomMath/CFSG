module

public import Certificates.Kernel.Sporadic.M12Count
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelSpor.M12Count

open CFSG.Sporadic.Mathieu CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.PCnt

set_option maxRecDepth 100000
set_option Elab.async false

example : Nat.beq (ordTwo 12 4 (mask 4) I (pk m12gB)) 0 = true := by quickRfl

example : Nat.beq (partner 12 4 (mask 4) I (pk m12gA) (pk m12gA)) 0 = true := by quickRfl

example : (!conjTreeP 12 4 (mask 4) (pk m12gA) (pk m12gA⁻¹) (pk m12gB) (pk m12gB⁻¹) (pk m12gB)
    cl₁.1 cl₁.2.1 cl₁.2.2) = true := by quickRfl

example : (!conjTreeP 12 4 (mask 4) (pk m12gA) (pk m12gA⁻¹) (pk m12gB) (pk m12gB⁻¹) (pk m12gA)
    cl₁.1 cl₁.2.1 (cl₁.2.2.map fun _ => 0)) = true := by quickRfl

example : (!distB (cl₁.1 ++ cl₁.1)) = true := by quickRfl

example : (!Nat.beq cl₂.1.length 395) = true := by quickRfl

end CertificateChecks.KernelSpor.M12Count
