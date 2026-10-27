module

public import Certificates.Data.CFSGNative.Fi22.Certificate
public import Certificates.Data.Kernel.Spor.F3Lane
public import Certificates.Data.Kernel.Spor.Row
public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Kernel.Sporadic.RowsWCmd
public import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Data.CFSGNative.Fi22.Certificate

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelFi22C.SeedA CFSG.Sporadic.Fi22.Native.seedA
#ks_chars CertificateChecks.KernelFi22C.SeedB CFSG.Sporadic.Fi22.Native.seedB

namespace CertificateChecks.KernelFi22C

open CFSG.F3.Native CFSG.Sporadic.Fi22.Native

meta def laneOf (X : Array V) : Array Nat :=
  #[(List.range 77).foldl (fun a i => a + X[i]!.p * 2 ^ (77 * i)) 0,
    (List.range 77).foldl (fun a i => a + X[i]!.m * 2 ^ (77 * i)) 0]

meta def lanesM : Array Nat :=
  laneOf (matA ()) ++ laneOf (matB ()) ++ laneOf (matBi ()) ++ laneOf (idM 77)

end CertificateChecks.KernelFi22C

#krowsw CertificateChecks.KernelFi22C.LT 5929 CertificateChecks.KernelFi22C.lanesM

namespace CertificateChecks.KernelFi22C

open CFSG.F3.Native CFSG.KS CFSG.KS.Row CFSG.KS.F3L

@[expose] noncomputable def lt (i : Nat) : Nat := rg (nat_lit 5929) (mask (nat_lit 5929)) LT (nat_lit 0) i

@[expose] noncomputable def ln (i : Nat) : V := ⟨lt (Nat.mul (nat_lit 2) i), lt (Nat.succ (Nat.mul (nat_lit 2) i))⟩

@[expose] noncomputable def LA : V := ln (nat_lit 0)
@[expose] noncomputable def LB : V := ln (nat_lit 1)
@[expose] noncomputable def LBi : V := ln (nat_lit 2)
@[expose] noncomputable def LI : V := ln (nat_lit 3)

@[expose] noncomputable def SP : Nat := spreadE (nat_lit 77) (nat_lit 77)

@[expose] noncomputable def mulF (X Y : V) : V := mulLane (nat_lit 77) SP X Y

@[expose] noncomputable def powF (X : V) (e : Nat) : V := powLane (nat_lit 77) SP LI X e

@[expose] noncomputable def canonF (X : V) : Bool :=
  bAnd(Nat.beq (Nat.land X.p X.m) (nat_lit 0), bAnd(Nat.blt X.p (Nat.shiftLeft (nat_lit 1) (nat_lit 5929)),
    Nat.blt X.m (Nat.shiftLeft (nat_lit 1) (nat_lit 5929))))

@[expose] noncomputable def eqF (X Y : V) : Bool := bAnd(Nat.beq X.p Y.p, Nat.beq X.m Y.m)

end CertificateChecks.KernelFi22C

end
