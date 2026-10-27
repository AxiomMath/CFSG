module

public import Certificates.Data.CFSGNative.Fi23.Data
public import Certificates.Data.Kernel.Spor.F3Lane
public import Certificates.Data.Kernel.Spor.Row
public import Certificates.Kernel.Sporadic.RowsWCmd
public import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Data.CFSGNative.Fi23.Data
public meta import Certificates.Data.CFSGNative.F3.Basic

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelDet.Fi23.SeedA CFSG.Sporadic.Fi23.Native.seedA
#ks_chars CertificateChecks.KernelDet.Fi23.SeedB CFSG.Sporadic.Fi23.Native.seedB

namespace CertificateChecks.KernelDet.Fi23

open CFSG.F3.Native CFSG.Sporadic.Fi23.Native

meta def laneOf (X : Array V) : Array Nat :=
  #[(List.range 253).foldl (fun a i => a + X[i]!.p * 2 ^ (253 * i)) 0,
    (List.range 253).foldl (fun a i => a + X[i]!.m * 2 ^ (253 * i)) 0]

meta def lanesM : Array Nat :=
  laneOf (rowsOf 253 seedA) ++ laneOf (rowsOf 253 seedB) ++ laneOf (idM 253)

end CertificateChecks.KernelDet.Fi23

#krowsw CertificateChecks.KernelDet.Fi23.LT 64009 CertificateChecks.KernelDet.Fi23.lanesM

namespace CertificateChecks.KernelDet.Fi23

open CFSG.F3.Native CFSG.KS CFSG.KS.Row CFSG.KS.F3L

@[expose] noncomputable def lt (i : Nat) : Nat :=
  rg (nat_lit 64009) (mask (nat_lit 64009)) LT (nat_lit 0) i

@[expose] noncomputable def ln (i : Nat) : V :=
  ⟨lt (Nat.mul (nat_lit 2) i), lt (Nat.succ (Nat.mul (nat_lit 2) i))⟩

@[expose] noncomputable def LA : V := ln (nat_lit 0)
@[expose] noncomputable def LB : V := ln (nat_lit 1)
@[expose] noncomputable def LI : V := ln (nat_lit 2)

@[expose] noncomputable def SP : Nat := spreadE (nat_lit 253) (nat_lit 253)

@[expose] noncomputable def mulF (X Y : V) : V := mulLane (nat_lit 253) SP X Y

@[expose] noncomputable def powF (X : V) (e : Nat) : V := powLane (nat_lit 253) SP LI X e

end CertificateChecks.KernelDet.Fi23

end
