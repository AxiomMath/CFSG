module

public import Certificates.Kernel.Sporadic.SuzK.TabDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.KC.Enum CFSG.KS.PEnum

@[expose] noncomputable def trAt (k : Nat) : Bool :=
  bIf(Nat.beq k (nat_lit 0), true, strictB (r32 PA k) fun p => bAnd(Nat.blt p k,
    bIf(Nat.beq (r32 LB k) (nat_lit 1), Nat.beq (r32 AL p) k,
      bAnd(Nat.beq (r32 LB k) (nat_lit 2), Nat.beq (r32 BE p) k))))

@[expose] noncomputable def trK : Bool := allN (nat_lit 22880) trAt

set_option Elab.async false

theorem tree_ok : trK = true := by quickRfl

end CertificateChecks.KernelSpor.SuzK

end
