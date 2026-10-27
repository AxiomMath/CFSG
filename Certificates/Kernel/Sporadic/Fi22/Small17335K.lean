module

public import Certificates.Kernel.Sporadic.Fi22.Small17335D
public import Certificates.Kernel.Sporadic.Fi22.Five8124K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Small17335

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Fv8124 (ev idP pwK isP)

@[expose] noncomputable def cntP (p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x acc => Nat.add acc (nIf(Nat.beq (ev p x) x, nat_lit 1, nat_lit 0))) (nat_lit 3510)

@[expose] noncomputable def chkU (u q f : Nat) : Bool :=
  isP u && Fi22X.siftP u && Nat.beq (pwK u q) idP && !(Nat.beq u idP) && Nat.beq (cntP u) f

theorem ok7 : strictB (Fi22SmallT.U 0) (fun u => chkU u 7 3) = true := by quickRfl

theorem ok11 : strictB (Fi22SmallT.U 1) (fun u => chkU u 11 1) = true := by quickRfl

theorem ok13 : strictB (Fi22SmallT.U 2) (fun u => chkU u 13 0) = true := by quickRfl

end CertificateChecks.KernelSpor.Small17335

end
