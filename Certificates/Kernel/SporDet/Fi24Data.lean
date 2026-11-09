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

meta def spreadM : Nat := (List.range 781).foldl (fun a b => a ||| 1 <<< (781 * b)) 0

meta def addWM (a b : V) : V :=
  let t := (a.p ||| b.m) ^^^ (a.m ||| b.p)
  ⟨(a.m ||| b.m) ^^^ t, (a.p ||| b.p) ^^^ t⟩

meta def mulM (X Y : V) : V :=
  (List.range 781).foldl (fun acc j =>
    let sp := (X.p >>> j) &&& spreadM
    let sm := (X.m >>> j) &&& spreadM
    let yp := (Y.p >>> (781 * j)) &&& (2 ^ 781 - 1)
    let ym := (Y.m >>> (781 * j)) &&& (2 ^ 781 - 1)
    addWM acc ⟨(sp * yp) ||| (sm * ym), (sp * ym) ||| (sm * yp)⟩) V.zero

meta def laneV (X : Array V) : V :=
  ⟨(List.range 781).foldl (fun a i => a + X[i]!.p * 2 ^ (781 * i)) 0,
    (List.range 781).foldl (fun a i => a + X[i]!.m * 2 ^ (781 * i)) 0⟩

meta def powsM : Array V :=
  let A := laneV (rowsOf 781 seedA)
  let C := mulM A (laneV (rowsOf 781 seedB))
  (List.range 27).foldl (fun acc _ => acc.push (mulM acc.back! C)) #[C]

meta def lanesM : Array Nat :=
  let B := laneV (rowsOf 781 seedB)
  let B2 := mulM B B
  laneOf (rowsOf 781 seedA) ++ laneOf (rowsOf 781 seedB) ++ laneOf (idM 781) ++
    powsM.foldl (fun a X => a ++ #[X.p, X.m]) #[] ++ #[B2.p, B2.m]

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

@[expose] noncomputable def LC (k : Nat) : V := ln (Nat.add (nat_lit 2) k)

@[expose] noncomputable def LB2 : V := ln (nat_lit 31)

@[expose] noncomputable def SP : Nat := spreadE (nat_lit 781) (nat_lit 781)

@[expose] noncomputable def mulF (X Y : V) : V := mulLane (nat_lit 781) SP X Y

@[expose] noncomputable def powF (X : V) (e : Nat) : V := powLane (nat_lit 781) SP LI X e

end CertificateChecks.KernelDet.Fi24

end
