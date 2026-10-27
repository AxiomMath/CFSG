module

public import Certificates.Data.Kernel.Misc.GL4Elt
public import Certificates.Kernel.Misc.GL4.EAData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_ktree CertificateChecks.KernelMisc.GL4S3 SW
  "Certificates/Kernel/Misc/GL4/S3/data/s3w.bin" 4 4 80640 5421077241066401832
#kc_repo #kc_ktree CertificateChecks.KernelMisc.GL4S3 SV
  "Certificates/Kernel/Misc/GL4/S3/data/s3v.bin" 4 4 161280 9050937720045032983
#kc_repo #kc_ktree CertificateChecks.KernelMisc.GL4S3 ST
  "Certificates/Kernel/Misc/GL4/S3/data/s3t.bin" 4 4 368 4535957685937027708

namespace CertificateChecks.KernelMisc.GL4S3

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.Misc.GL4
open CertificateChecks.KernelMisc.GL4EA (EA)

@[expose] noncomputable def sA0 (t : Nat) : Nat := lAt [51233, 51250] t

@[expose] noncomputable def sB0 (t : Nat) : Nat := lAt [33842, 19506] t

@[expose] noncomputable def cL (t i : Nat) : Nat := ST (Nat.add (Nat.mul (nat_lit 3) t) i)

@[expose] noncomputable def cT (t i l : Nat) : Nat :=
  ST (Nat.add (Nat.add (Nat.add (nat_lit 6) (Nat.mul (nat_lit 18) t)) (Nat.mul (nat_lit 6) i)) l)

@[expose] noncomputable def bO (t : Nat) : Nat := lAt [42, 48] t

@[expose] noncomputable def bN (t : Nat) : Nat := lAt [6, 42] t

@[expose] noncomputable def bd (t i : Nat) : Nat := ST (Nat.add (bO t) i)

@[expose] noncomputable def commB (x y : Nat) : Bool := Nat.beq (mul4F x y) (mul4F y x)

@[expose] noncomputable def wW (x w : Nat) : Bool :=
  letB (fld w (nat_lit 0) (nat_lit 15)) fun j => letB (Nat.shiftRight w (nat_lit 15)) fun t =>
    andB (Nat.blt j (nat_lit 20160)) (andB (Nat.blt t (nat_lit 2))
      (Nat.beq (mul4F (EA j) x) (mul4F (sA0 t) (EA j))))

@[expose] noncomputable def vW (t x h : Nat) : Bool :=
  andB (Nat.blt h (nat_lit 20160)) (andB (commB (EA h) (sA0 t))
    (Nat.beq (mul4F (EA h) x) (mul4F (sB0 t) (EA h))))

@[expose] noncomputable def tAt (k x x2 : Nat) (o3 : Bool) (t : Nat) : Bool :=
  letB (sA0 t) fun a =>
    andB (impB (andB o3 (commB x a)) (orB (vW t x (SV (Nat.add (Nat.mul (nat_lit 2) k) t)))
        (inL (bd t) (bN t) x)))
      (andB (impB (andB (Nat.beq x2 id4) (Nat.beq (mul4F x a) (mul4F (mul4F a a) x)))
          (andB (allN (bN t) fun i => notB (commB x (bd t i)))
            (impB (commB x (sB0 t)) (inL (cL t) (nat_lit 3) x))))
        (impB (commB x a) (allN (nat_lit 3) fun i =>
          impB (commB x (cL t i)) (inL (cT t i) (nat_lit 6) x))))

@[expose] noncomputable def o3B (x x2 : Nat) : Bool :=
  andB (Nat.beq (mul4F x2 x) id4) (notB (Nat.beq x id4))

@[expose] noncomputable def s3At (k : Nat) : Bool :=
  letB (EA k) fun x => letB (mul4F x x) fun x2 =>
    andB (impB (o3B x x2) (wW x (SW k))) (allN (nat_lit 2) fun t => tAt k x x2 (o3B x x2) t)

@[expose] noncomputable def s3S (s : Nat) : Bool := allR (Nat.mul (nat_lit 5040) s) (nat_lit 5040) s3At

@[expose] noncomputable def centS (t : Nat) : Bool :=
  allN (nat_lit 3) fun i => allN (nat_lit 6) fun l => letB (cT t i l) fun g =>
    impB (Nat.beq (mul4F (mul4F g g) g) id4) (orB (Nat.beq g id4) (orB (Nat.beq g (sB0 t))
      (Nat.beq g (mul4F (sB0 t) (sB0 t)))))

end CertificateChecks.KernelMisc.GL4S3

end
