module

public import Certificates.Kernel.Sporadic.ON.TrData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.TW CFSG.KS.Words CFSG.KS.FLGen

@[expose] noncomputable def trAtP (x : Nat) : Bool :=
  bAnd(allBlk (nat_lit 0) (fun h => strictB (TT h x) fun y => bAnd(Nat.blt y (nat_lit 245520),
      bAnd(Nat.blt (UU h x) (nat_lit 245520), Nat.beq (UU h y) x))) (nat_lit 7),
    allBlk (nat_lit 0) (fun h => bAnd(Nat.beq (TB h x) (TT h x), Nat.beq (UB h x) (UU h x)))
        (nat_lit 7))

@[expose] noncomputable def trP (s : Nat) : Bool :=
  allBlk (Nat.mul s (nat_lit 240)) trAtP (nat_lit 240)

end CertificateChecks.KernelSpor.ON

end
