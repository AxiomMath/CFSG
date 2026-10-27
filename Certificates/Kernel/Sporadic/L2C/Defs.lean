module

public import Certificates.Kernel.Sporadic.L2.Defs
public import Certificates.Kernel.Sporadic.L2C.Text
public import Certificates.Kernel.Sporadic.L2C.Pins

public section

namespace CertificateChecks.KernelSpor.L2CK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.L2K

local notation "pgv" => pg 12 (mask 12)
local notation "pg2" => pg 2 (mask 2)
local notation "pc" => pcomp 1782 11 (mask 11)
local notation "Idn" => pidn 1782 11

@[expose] noncomputable def voltK (x k : Nat) : Nat := pg2 (L2CV.F x) k
@[expose] noncomputable def shK (s v : Nat) : Nat := pg2 (L2CS.F s) v
@[expose] noncomputable def tParC (z : Nat) : Nat := pg 14 (mask 14) (L2CT 0) z
@[expose] noncomputable def tDepC (z : Nat) : Nat := pg 14 (mask 14) (L2CT 1) z
@[expose] noncomputable def recK (u k : Nat) : Nat := pg 16 (mask 16) (L2CR u) k
@[expose] noncomputable def rkK (u k : Nat) : Nat := Nat.land (recK u k) 15
@[expose] noncomputable def apK (u k : Nat) : Nat := fld(recK u k, 4, 63)
@[expose] noncomputable def bpK (u k : Nat) : Nat := fld(recK u k, 10, 63)

@[expose] noncomputable def nbCR (B V i k : Nat) : Nat :=
  Nat.add (pgv B k) (Nat.mul 2997 (Nat.mod (Nat.add i (pg2 V k)) 3))

@[expose] noncomputable def nbC (u k : Nat) : Nat :=
  nbCR (L2NB.F (Nat.mod u 2997)) (L2CV.F (Nat.mod u 2997)) (Nat.div u 2997) k

@[expose] noncomputable def anyN (n : Nat) (f : Nat → Bool) : Bool :=
  Bool.not (allN n fun j => Bool.not (f j))

@[expose] noncomputable def baseG (NB VF : Nat → Nat) (x : Nat) : Bool :=
  strictB (NB x) fun B => strictB (VF x) fun V =>
  allN 36 fun k => strictB (pgv B k) fun y =>
    bAnd(Nat.blt y 2997, bAnd(Bool.not (Nat.beq y x),
    bAnd(allN k (fun j => Bool.not (Nat.beq (pgv B j) y)),
      bIf(Nat.ble 2835 y, true, strictB (NB y) fun By => strictB (VF y) fun Vy =>
        anyN 36 fun j => bAnd(Nat.beq (pgv By j) x,
          Nat.beq (Nat.mod (Nat.add (pg2 V k) (pg2 Vy j)) 3) 0)))))

@[expose] noncomputable def baseK (x : Nat) : Bool := baseG L2NB.F L2CV.F x

@[expose] noncomputable def baseSl (s : Nat) : Bool := allBlk (Nat.mul 315 s) baseK 315

@[expose] noncomputable def liftG (VT SH : Nat → Nat → Nat) (s x : Nat) : Bool :=
  bIf(Nat.blt x 2835,
    strictB (VT s x) fun x' => strictB (L2NB.F x) fun B => strictB (L2CV.F x) fun V =>
    strictB (L2NB.F x') fun B' => strictB (L2CV.F x') fun V' => strictB (SH s x) fun h =>
    allN 36 fun k => strictB (pgv B k) fun y => strictB (VT s y) fun y' =>
      strictB (Nat.mod (Nat.add (pg2 V k) (SH s y)) 3) fun t =>
      anyN 36 fun j => bAnd(Nat.beq (pgv B' j) y', Nat.beq (Nat.mod (Nat.add h (pg2 V' j)) 3) t),
    true)

@[expose] noncomputable def liftK (x : Nat) : Bool := bAnd(liftG VK shK 0 x, liftG VK shK 1 x)

@[expose] noncomputable def liftSl (s : Nat) : Bool := allBlk (Nat.mul 315 s) liftK 315

@[expose] noncomputable def letK (VT SH : Nat → Nat → Nat) (s t : Nat) : Nat :=
  strictN t fun t => strictN (Nat.land t 4095) fun v =>
    Nat.add (VT s v) (Nat.shiftLeft (Nat.add (Nat.shiftRight t 12) (SH s v)) 12)

@[expose] noncomputable def word3 (VT SH : Nat → Nat → Nat) (t : Nat) : Nat :=
  letK VT SH 0 (letK VT SH 0 (letK VT SH 1 t))

@[expose] noncomputable def walkG (VT SH : Nat → Nat → Nat) (x : Nat) : Bool :=
  strictB (Nat.rec (motive := fun _ => Nat) x (fun _ ih => word3 VT SH ih) 8) fun t =>
    bAnd(Nat.beq (Nat.land t 4095) x, Nat.beq (Nat.mod (Nat.shiftRight t 12) 3) 1)

@[expose] noncomputable def walkK (x : Nat) : Bool := walkG VK shK x

@[expose] noncomputable def walkSl (s : Nat) : Bool :=
  allBlk (Nat.mul 300 s) (fun x => bIf(Nat.blt x 2997, walkK x, true)) 300

@[expose] noncomputable def pw (G : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) Idn (fun _ ih => pc G ih) k

@[expose] noncomputable def wordK : Bool :=
  strictB (pc (XG 0) (pc (XG 0) (XG 1))) fun W => Nat.beq (pw W 8) Idn

@[expose] noncomputable def occC (u w : Nat) : Bool :=
  bIf(Nat.blt (Nat.mod u 2997) 2835, anyN 36 (fun k => Nat.beq (nbC u k) w), false)

@[expose] noncomputable def adjC (u w : Nat) : Bool :=
  bAnd(Bool.not (Nat.beq u w), bIf(occC u w, true, occC w u))

@[expose] noncomputable def treeC (z : Nat) : Bool :=
  bIf(Nat.beq z 0, true, strictB (tParC z) fun p =>
    bAnd(Nat.blt p 8991, bAnd(Nat.blt (tDepC p) (tDepC z), adjC p z)))

@[expose] noncomputable def listR (u i B V R k : Nat) : Bool :=
  strictB (pg 16 (mask 16) R k) fun c => strictB (Nat.land c 15) fun r =>
  strictB (nbCR B V i k) fun y =>
  bIf(Nat.beq r 0,
    bIf(bAnd(Nat.blt 0 y, Nat.beq (tParC y) u), true, bAnd(Nat.blt 0 u, Nat.beq (tParC u) y)),
    strictB (fld(c, 4, 63)) fun a => strictB (fld(c, 10, 63)) fun b =>
    strictB (nbCR B V i a) fun z =>
    bAnd(Nat.blt a 36, bAnd(Nat.blt b 36, bAnd(Nat.blt (Nat.land (pg 16 (mask 16) R a) 15) r,
    bAnd(Bool.not (Nat.beq u z), bAnd(Bool.not (Nat.beq u y),
      bIf(Nat.blt (Nat.mod z 2997) 2835,
        bAnd(Nat.ble 2835 (Nat.mod y 2997), bAnd(Nat.beq (nbC z b) y, Nat.blt (rkK z b) r)),
        bAnd(Nat.blt (Nat.mod y 2997) 2835,
          bAnd(Nat.beq (nbC y b) z, Nat.blt (rkK y b) r)))))))))

@[expose] noncomputable def rowG (RR : Nat → Nat) (u : Nat) : Bool :=
  bAnd(treeC u,
    strictB (Nat.mod u 2997) fun x => bIf(Nat.blt x 2835,
      strictB (Nat.div u 2997) fun i => strictB (L2NB.F x) fun B => strictB (L2CV.F x) fun V =>
        strictB (RR u) fun R => allN 36 (listR u i B V R),
      true))

@[expose] noncomputable def rowK (u : Nat) : Bool := rowG L2CR u

@[expose] noncomputable def rowSl (s : Nat) : Bool :=
  allBlk (Nat.mul 100 s) (fun u => bIf(Nat.blt u 8991, rowK u, true)) 100

@[expose] noncomputable def posOK (y k : Nat) : Bool :=
  bAnd(Nat.beq (nbK 0 k) y, allN k (fun j => Bool.not (Nat.beq (nbK 0 j) y)))

@[expose] noncomputable def locK : Bool :=
  bAnd(posOK 342 0, bAnd(posOK 2835 18, bAnd(posOK 2852 19, bAnd(posOK 2890 23,
  bAnd(posOK 2922 27, bAnd(posOK 2932 28, bAnd(posOK 2968 33, bAnd(posOK 2970 34,
  bAnd(Nat.beq (nbC 0 0) 342,
  bAnd(Nat.beq (nbC 342 33) (nbC 0 19), bAnd(Nat.beq (nbC 342 30) (nbC 0 27),
  bAnd(allN 36 (fun j => Bool.not (Nat.beq (nbC 342 j) (nbC 0 23))),
  bAnd(allN 36 (fun j => Bool.not (Nat.beq (nbC 342 j) (nbC 0 34))),
  bAnd(Nat.beq (nbC 342 29) (nbC 0 33), Nat.beq (nbC 342 31) (nbC 0 28)))))))))))))))

end CertificateChecks.KernelSpor.L2CK

end
