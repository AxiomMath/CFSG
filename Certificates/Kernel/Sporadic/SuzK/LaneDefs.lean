module

public import Certificates.Kernel.Sporadic.SuzK.KeyDefs
public import Certificates.Data.Kernel.Spor.F3LaneSep

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.F3.Native CFSG.KS CFSG.KS.F3L CFSG.KC.Enum CFSG.Sporadic.Suz.Native

@[expose] noncomputable def SP : Nat := spreadE (nat_lit 64) (nat_lit 64)

@[expose] noncomputable def mulF (X Y : V) : V := mulLane (nat_lit 64) SP X Y

@[expose] noncomputable def powF (X : V) (e : Nat) : V := powLane (nat_lit 64) SP (ln (nat_lit 3)) X e

@[expose] noncomputable def canonF (X : V) : Bool :=
  bAnd(Nat.beq (Nat.land X.p X.m) (nat_lit 0), bAnd(Nat.blt X.p (Nat.shiftLeft (nat_lit 1) (nat_lit 4096)),
    Nat.blt X.m (Nat.shiftLeft (nat_lit 1) (nat_lit 4096))))

@[expose] noncomputable def eqF (X Y : V) : Bool := bAnd(Nat.beq X.p Y.p, Nat.beq X.m Y.m)

@[expose] noncomputable def laneK (k : Nat) : V :=
  strictT (kx k) fun x => ⟨Nat.land x (mask (nat_lit 4096)), Nat.shiftRight x (nat_lit 4096)⟩

@[expose] noncomputable def LsS : List V :=
  [laneK 0, laneK 1, laneK 2, laneK 3, laneK 4, laneK 5]

@[expose] noncomputable def WL : V := combL 64 SP (ln (nat_lit 3)) LsS sepTerms

end CertificateChecks.KernelSpor.SuzK

end
