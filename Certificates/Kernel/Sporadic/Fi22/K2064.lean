module

public import Certificates.Kernel.Sporadic.Fi22.T2064
public import Certificates.Data.Kernel.ClosBfs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22CtiB

open CFSG.KC.Enum CFSG.KS CFSG.KC.ClosBfs CertificateChecks.KernelSpor.Fi22CtiX

theorem bfs : closBfsOK 10 NX PA LA 1024 = true := by quickRfl

@[expose] noncomputable def ziRow (i : Nat) : Bool :=
  bAnd(Nat.beq (ZI (ZI i)) i, Bool.not (Nat.beq (ZI i) i))

theorem ziRows : allN 1024 ziRow = true := by quickRfl

theorem repRows : allN 512 (fun c => Nat.blt (RP c) (ZI (RP c))) = true := by quickRfl

theorem incRows : allN 511 (fun c => Nat.blt (RP c) (RP (Nat.succ c))) = true := by quickRfl

theorem cidRows : allN 1024 (fun i => bOr (Nat.beq (RP (CD i)) i) (Nat.beq (RP (CD i)) (ZI i))) =
    true := by quickRfl

end CertificateChecks.KernelSpor.Fi22CtiB

end
