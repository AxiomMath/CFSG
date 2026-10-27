module

public import Certificates.Data.CFSGNative.Fi24.Data
public import Certificates.Data.CFSGNative.F3.Basic
public import Certificates.Data.Kernel.Spor.F3Lane
public import Certificates.Data.Kernel.Spor.Row
public import Certificates.Kernel.Sporadic.RowsWCmd
public import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Data.CFSGNative.Fi24.Data
public meta import Certificates.Data.CFSGNative.F3.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelDet.Fi24

open CFSG.F3.Native CFSG.Sporadic.Fi24.Native

meta def laneOf (X : Array V) : Array Nat :=
  #[(List.range 781).foldl (fun a i => a + X[i]!.p * 2 ^ (781 * i)) 0,
    (List.range 781).foldl (fun a i => a + X[i]!.m * 2 ^ (781 * i)) 0]

meta def lanesM : Array Nat :=
  laneOf (rowsOf 781 seedA) ++ laneOf (rowsOf 781 seedB) ++ laneOf (idM 781)

end CertificateChecks.KernelDet.Fi24

#krowsw CertificateChecks.KernelDet.Fi24.LT 609961 CertificateChecks.KernelDet.Fi24.lanesM

namespace CertificateChecks.KernelDet.Fi24

open CFSG.F3.Native CFSG.KS CFSG.KS.Row CFSG.KS.F3L

@[expose] noncomputable def lt (i : Nat) : Nat :=
  rg (nat_lit 609961) (mask (nat_lit 609961)) LT (nat_lit 0) i

@[expose] noncomputable def ln (i : Nat) : V :=
  ⟨lt (Nat.mul (nat_lit 2) i), lt (Nat.succ (Nat.mul (nat_lit 2) i))⟩

@[expose] noncomputable def LA : V := ln (nat_lit 0)
@[expose] noncomputable def LB : V := ln (nat_lit 1)
@[expose] noncomputable def LI : V := ln (nat_lit 2)

@[expose] noncomputable def SP : Nat := spreadE (nat_lit 781) (nat_lit 781)

@[expose] noncomputable def mulF (X Y : V) : V := mulLane (nat_lit 781) SP X Y

@[expose] noncomputable def powF (X : V) (e : Nat) : V := powLane (nat_lit 781) SP LI X e

end CertificateChecks.KernelDet.Fi24

end
