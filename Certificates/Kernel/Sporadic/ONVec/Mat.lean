module

public import Certificates.Kernel.Sporadic.ONVec.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONVec

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CertificateChecks.KernelSpor

theorem sigLK : allN 154 (fun j => Nat.beq (List.getD ONS.LA j 0) (ONS.CA j)) = true := by quickRfl
theorem lensK : bAnd(Nat.beq (List.length CM) 154, bAnd(Nat.beq (List.length XI) 154,
    bAnd(Nat.beq (List.length RA) 154, bAnd(Nat.beq (List.length RB) 154,
    bAnd(Nat.beq (List.length CU) 154, bAnd(Nat.beq (List.length GR) 154,
    Nat.beq (List.length ONS.LA) 154)))))) = true := by quickRfl
theorem rootNZ : Bool.not (Nat.beq (key ONV.K 0) (nat_lit 0)) = true := by quickRfl

end CertificateChecks.KernelSpor.ONVec

end
