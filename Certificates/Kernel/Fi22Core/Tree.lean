module

public import Certificates.Kernel.Fi22Core.Keys
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22C

open CFSG.F3.Native CFSG.KS CFSG.KS.F3L CFSG.KS.Fi22L CFSG.KC.Enum

@[expose] noncomputable def treeAt (k : Nat) : Bool :=
  bIf(Nat.beq k (nat_lit 0), true, strictB (lk (orbT (nat_lit 2)) k) fun p =>
    strictB (lk (orbT (nat_lit 3)) k) fun l => bAnd(Nat.blt p k,
      bIf(Nat.beq l (nat_lit 1), Nat.beq (lk (orbT (nat_lit 0)) p) k,
        bAnd(Nat.beq l (nat_lit 2), Nat.beq (lk (orbT (nat_lit 1)) p) k))))

@[expose] noncomputable def invoAt (x : Nat) : Bool :=
  bAnd(Nat.blt (lk (orbT (nat_lit 0)) x) (nat_lit 3510), bAnd(Nat.blt (lk (orbT (nat_lit 1)) x) (nat_lit 3510),
    Nat.beq (lk (orbT (nat_lit 0)) (lk (orbT (nat_lit 0)) x)) x))

@[expose] noncomputable def treeK : Bool := allN (nat_lit 3510) fun k => bAnd(treeAt k, invoAt k)

@[expose] noncomputable def P1L : V := mulF LA (KL (nat_lit 1))
@[expose] noncomputable def P2L : V := mulF LA (KL (nat_lit 8))

@[expose] noncomputable def prodK : Bool :=
  bAnd(canonF P1L, bAnd(canonF P2L, bAnd(eqF (powF P1L (nat_lit 3)) LI, bAnd(Bool.not (eqF P1L LI),
    bAnd(eqF (powF P2L (nat_lit 2)) LI, Bool.not (eqF P2L LI))))))

set_option Elab.async false

theorem tree_ok : treeK = true := by quickRfl

theorem prod_ok : prodK = true := by quickRfl

end CertificateChecks.KernelFi22C

end
