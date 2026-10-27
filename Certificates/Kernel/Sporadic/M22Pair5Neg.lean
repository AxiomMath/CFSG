module

public import Certificates.Kernel.Sporadic.M22Pair5
import CFSG.Certificates.Kernel.Common.Harness

namespace CertificateChecks.KernelSpor.M22Pair5

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.KC.Enum CFSG.KS CFSG.KS.PK CFSG.KS.PCnt

set_option maxRecDepth 100000
set_option Elab.async false

example : Nat.beq (ordTwo 22 5 (mask 5) I (pkw 5 m22gB)) 0 = true := by quickRfl

example : Nat.beq (ordPr 22 5 (mask 5) I (pkw 5 (m22gA * m22gB)) 4) 0 = true := by quickRfl

example : Nat.beq (partnerW 22 5 (mask 5) I (pkw 5 m22gA) (pkw 5 m22gA)) 0 = true := by quickRfl

example : (!baseOK lv [1, 0, 2, 3, 4]) = true := by quickRfl

example : (!Nat.beq (conjDFS 22 5 (mask 5) (pkw 5 m22gA) (pkw 5 m22gA⁻¹) (pkw 5 m22gB)
    (pkw 5 m22gB⁻¹) (pkw 5 m22gA) 0).length 1155) = true := by quickRfl

example : (!Nat.beq cl.length 1154) = true := by quickRfl

example : (!Nat.beq (cntS 1) 1155) = true := by quickRfl

end CertificateChecks.KernelSpor.M22Pair5
