module

public import Certificates.Data.CFSGNative.ON.Data
public import Certificates.Data.Kernel.Spor.F3Lane
public import Certificates.Data.Kernel.Spor.Row
public import Certificates.Kernel.Sporadic.RowsWCmd
public import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Data.CFSGNative.ON.Data
public meta import Certificates.Data.CFSGNative.F3.Basic

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelDet.ON.SeedA CFSG.Sporadic.ON.Native.seedA
#ks_chars CertificateChecks.KernelDet.ON.SeedB CFSG.Sporadic.ON.Native.seedB

namespace CertificateChecks.KernelDet.ON

open CFSG.F3.Native CFSG.Sporadic.ON.Native

meta def laneOf (X : Array V) : Array Nat :=
  #[(List.range 154).foldl (fun a i => a + X[i]!.p * 2 ^ (154 * i)) 0,
    (List.range 154).foldl (fun a i => a + X[i]!.m * 2 ^ (154 * i)) 0]

meta def lanesM : Array Nat :=
  laneOf (rowsOf 154 seedA) ++ laneOf (rowsOf 154 seedB) ++ laneOf (idM 154)

end CertificateChecks.KernelDet.ON

#krowsw CertificateChecks.KernelDet.ON.LT 23716 CertificateChecks.KernelDet.ON.lanesM

namespace CertificateChecks.KernelDet.ON

open CFSG.F3.Native CFSG.KS CFSG.KS.Row CFSG.KS.F3L

@[expose] noncomputable def lt (i : Nat) : Nat :=
  rg (nat_lit 23716) (mask (nat_lit 23716)) LT (nat_lit 0) i

@[expose] noncomputable def ln (i : Nat) : V :=
  ⟨lt (Nat.mul (nat_lit 2) i), lt (Nat.succ (Nat.mul (nat_lit 2) i))⟩

@[expose] noncomputable def LA : V := ln (nat_lit 0)
@[expose] noncomputable def LB : V := ln (nat_lit 1)
@[expose] noncomputable def LI : V := ln (nat_lit 2)

@[expose] noncomputable def SP : Nat := spreadE (nat_lit 154) (nat_lit 154)

@[expose] noncomputable def mulF (X Y : V) : V := mulLane (nat_lit 154) SP X Y

@[expose] noncomputable def powF (X : V) (e : Nat) : V := powLane (nat_lit 154) SP LI X e

end CertificateChecks.KernelDet.ON

end
