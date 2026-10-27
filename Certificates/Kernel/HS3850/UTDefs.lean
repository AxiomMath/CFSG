module

public import Certificates.Kernel.HS3850.UTData
public import Certificates.Kernel.LocalQT.SV.C4126D
public import Certificates.Data.Kernel.LocalQT.HSAutN
public import Certificates.Data.Kernel.InvTabK
public import CFSG.Certificates.Kernel.Lie.CT.Core

public section

namespace CertificateChecks.KernelHS3850.UT

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.HSAutN CFSG.KD.LQT.C4126 CFSG.KC.InvTabK
open CFSG.KLie.CT (fget)
open CFSG.Quasithin.B45Exc.HS

@[expose] noncomputable def X (i : Nat) : Nat := SY.E (INV i)

@[expose] noncomputable def xE (k : Nat) : Nat := cond (Nat.blt k 191) (X k) idn

@[expose] noncomputable def kk (p : Nat) : Nat := Nat.add (Nat.mul (img p 0) 4096) (img p 5)

@[expose] noncomputable def cK (i j : Nat) : Bool :=
  if i < 191 ∧ j < 191 then Nat.testBit (CM i) j else true

@[expose] noncomputable def pK (i j : Nat) : Nat :=
  if i < 191 then (if j < 191 then fget (PR i) j 8 else i) else j

@[expose] noncomputable def pred4K (l : List Nat) : Bool :=
  let S := subprodsF 191 pK l
  (S.any fun s => decide (s < 191) && (FX s == 30 || FX s == 46)) ||
    hsGenWits.any fun w => w.basis.all S.contains

@[expose] noncomputable def pred5K (l : List Nat) : Bool :=
  let S := subprodsF 191 pK l
  (hsGenWits.any fun w => w.basis.all S.contains) &&
    hsDimWits.any fun w => [w.d, w.c, w.e, w.e'].all S.contains

@[expose] noncomputable def ckP (s : Nat) : Bool :=
  allN 8 fun d => strictB (Nat.add (Nat.mul s 8) d) fun i => bIf(Nat.blt i 191,
    allN 191 (fun j => bIf(Nat.ble i j, bIf(Nat.testBit (CM i) j,
      strictB (xE (fget (PR i) j 8)) fun E =>
        bAnd(Nat.beq (pc (X i) (X j)) E, Nat.beq (pc (X j) (X i)) E), true), true)), true)

end CertificateChecks.KernelHS3850.UT

end
