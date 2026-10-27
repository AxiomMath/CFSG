module

public import Certificates.Kernel.Sporadic.Q3A.Text
public import Certificates.Kernel.Sporadic.Q3A.Pins
public import Certificates.Kernel.Sporadic.Suz.Text2306
public import Certificates.Kernel.Sporadic.OddCore.SuzTwC
public import Certificates.Kernel.Sporadic.OddCore.SuzMG
public import Certificates.Kernel.Sporadic.OddCore.Suz2302

public section

namespace CertificateChecks.KernelSpor.Q3AK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim

local notation "pgk" => pg 11 (mask 11)
local notation "pc" => pcomp 1782 11 (mask 11)
local notation "Idn" => pidn 1782 11
local notation "T64" => nat_lit 18446744073709551616

@[expose] noncomputable def hx (F : Nat → Nat) (i : Nat) : Nat :=
  pg 16 (mask 16) (F (Nat.div i 160)) (Nat.mod i 160)

@[expose] noncomputable def tparK (i : Nat) : Nat := hx Q3ATP.F i
@[expose] noncomputable def tlabK (i : Nat) : Nat := hx Q3ATL.F i
@[expose] noncomputable def frootK (i : Nat) : Nat := hx Q3AFR.F i
@[expose] noncomputable def fparK (i : Nat) : Nat := hx Q3AFP.F i
@[expose] noncomputable def flabK (i : Nat) : Nat := hx Q3AFL.F i
@[expose] noncomputable def fdepK (i : Nat) : Nat := hx Q3AFD.F i

@[expose] noncomputable def spanK (k : Nat) : Nat :=
  pg 16 (mask 16) (Q3ASP.F (Nat.div k 127)) (Nat.mod k 127)

@[expose] noncomputable def BK (s : Nat) : Nat := nIf(Nat.beq s 0, Suz2306.B0, Suz2306.B1)
@[expose] noncomputable def BIK (s : Nat) : Nat := nIf(Nat.beq s 0, Q3AI 0, Q3AI 1)
@[expose] noncomputable def RHO : Nat := SuzTwG 2
@[expose] noncomputable def XK (s : Nat) : Nat := nIf(Nat.beq s 0, Q3AX.F 0, Q3AX.F 1)
@[expose] noncomputable def XIK (s : Nat) : Nat := nIf(Nat.beq s 0, Q3AI 3, Q3AI 4)

@[expose] noncomputable def wtK (x : Nat) : Nat := pg 64 (mask 64) (Q3AW 0) x

@[expose] noncomputable def mixK (x : Nat) : Nat :=
  strictN (Nat.mod (Nat.mul (Nat.succ x) (nat_lit 11400714819323198485)) T64) fun z =>
  strictN (Nat.mod (Nat.mul (Nat.xor z (Nat.shiftRight z (nat_lit 30)))
    (nat_lit 13787848793156543929)) T64) fun z =>
  strictN (Nat.mod (Nat.mul (Nat.xor z (Nat.shiftRight z (nat_lit 27)))
    (nat_lit 10723151780598845931)) T64) fun z =>
  Nat.xor z (Nat.shiftRight z (nat_lit 31))

@[expose] noncomputable def keyF (X : Nat) : Nat :=
  Nat.mod (foldN (nat_lit 162) (fun t a => Nat.add a (wtK (pgk X t))) (nat_lit 0)) T64

@[expose] noncomputable def imgK (G X : Nat) : Nat := pcomp (nat_lit 162) 11 (mask 11) G X

@[expose] noncomputable def skey (m : Nat) : Nat := Nat.mod (Q3AK m) T64
@[expose] noncomputable def sidx (m : Nat) : Nat := Nat.div (Q3AK m) T64

@[expose] noncomputable def bsK (k : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => lo)
    (fun _ ih lo hi => nIf(Nat.blt lo hi,
      strictN (Nat.shiftRight (Nat.add lo hi) (nat_lit 1)) (fun mid =>
        nIf(Nat.blt (skey mid) k, ih (Nat.succ mid) hi, ih lo mid)), lo))

@[expose] noncomputable def searchK (k : Nat) : Nat :=
  strictN (bsK k (nat_lit 16) (nat_lit 0) (nat_lit 22880)) fun m =>
    nIf(bAnd(Nat.blt m (nat_lit 22880), Nat.beq (skey m) k), sidx m, nat_lit 22880)

@[expose] noncomputable def actK (G i : Nat) : Nat := searchK (keyF (imgK G (Q3AF i)))

@[expose] noncomputable def cK : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => Idn)
    (fun _ ih i => nIf(bAnd(Nat.blt (nat_lit 0) i, Nat.blt (tparK i) i),
      strictN (ih (tparK i)) (fun C => pc (BK (tlabK i)) C), Idn))

@[expose] noncomputable def cIK : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => Idn)
    (fun _ ih i => nIf(bAnd(Nat.blt (nat_lit 0) i, Nat.blt (tparK i) i),
      strictN (ih (tparK i)) (fun C => pc C (BIK (tlabK i))), Idn))

@[expose] noncomputable def cA (i : Nat) : Nat := cK (Nat.succ i) i
@[expose] noncomputable def cIA (i : Nat) : Nat := cIK (Nat.succ i) i

@[expose] noncomputable def memF (X x : Nat) : Bool :=
  Bool.not (allN (nat_lit 162) fun t => Bool.not (Nat.beq (pgk X t) x))

@[expose] noncomputable def f0OK : Bool :=
  bAnd(allN (nat_lit 161) (fun t => Nat.blt (pgk (Q3AF 0) t) (pgk (Q3AF 0) (Nat.succ t))),
  bAnd(allN (nat_lit 162) (fun t => strictB (pgk (Q3AF 0) t) fun x =>
    bAnd(Nat.blt x (nat_lit 1782), Nat.beq (pgk RHO x) x)),
  allN (nat_lit 1782) (fun x => bIf(Nat.beq (pgk RHO x) x, memF (Q3AF 0) x, true))))

@[expose] noncomputable def vtOK (i : Nat) : Bool :=
  bAnd(bIf(Nat.beq i 0, true, strictB (tparK i) fun p => strictB (tlabK i) fun l =>
    bAnd(Nat.blt p i, bAnd(Nat.blt l (nat_lit 2), Nat.beq (Q3AF i) (imgK (BK l) (Q3AF p))))),
  bAnd(Nat.beq (searchK (keyF (Q3AF i))) i,
    strictB (sidx i) fun v => bAnd(Nat.blt v (nat_lit 22880), Nat.beq (skey i) (keyF (Q3AF v)))))

@[expose] noncomputable def vtSl (s : Nat) : Bool := allBlk (Nat.mul (nat_lit 160) s) vtOK (nat_lit 160)

@[expose] noncomputable def frOK (i : Nat) : Bool :=
  strictB (frootK i) fun r => bAnd(Nat.blt r (nat_lit 22880), bAnd(Nat.beq (frootK r) r,
    bIf(Nat.beq r i, Nat.beq (fdepK i) (nat_lit 0), strictB (fparK i) fun p =>
      strictB (flabK i) fun l => bAnd(Nat.blt p (nat_lit 22880), bAnd(Nat.blt l (nat_lit 2),
        bAnd(Nat.blt (fdepK p) (fdepK i), bAnd(Nat.beq (frootK p) r,
          Nat.beq (actK (XK l) p) i)))))))

@[expose] noncomputable def frSl (s : Nat) : Bool := allBlk (Nat.mul (nat_lit 160) s) frOK (nat_lit 160)

@[expose] noncomputable def countK (n : Nat) (p : Nat → Bool) : Nat :=
  foldN n (fun i c => nIf(p i, Nat.succ c, c)) (nat_lit 0)

@[expose] noncomputable def isRoot (i : Nat) : Bool :=
  bIf(Nat.beq i 0, true, bIf(Nat.beq i 1, true, bIf(Nat.beq i 2, true,
    bIf(Nat.beq i 10, true, Nat.beq i 202))))

@[expose] noncomputable def rootsOK : Bool :=
  bAnd(Nat.beq (countK (nat_lit 22880) fun i => Nat.beq (frootK i) i) (nat_lit 5),
    bAnd(Nat.beq (frootK 0) 0, bAnd(Nat.beq (frootK 1) 1, bAnd(Nat.beq (frootK 2) 2,
      bAnd(Nat.beq (frootK 10) 10, Nat.beq (frootK 202) 202)))))

@[expose] noncomputable def n0K (t : Nat) : Nat := pg 15 (mask 15) (Q3AN 0) t

@[expose] noncomputable def n0OK : Bool :=
  bAnd(Nat.beq (countK (nat_lit 22880) fun i => Nat.beq (frootK i) (nat_lit 10)) (nat_lit 486),
  bAnd(allN (nat_lit 485) (fun t => Nat.blt (n0K t) (n0K (Nat.succ t))),
    allN (nat_lit 486) (fun t => strictB (n0K t) fun y =>
      bAnd(Nat.blt y (nat_lit 22880), Nat.beq (frootK y) (nat_lit 10)))))

@[expose] noncomputable def invoK (G : Nat) : Bool :=
  bAnd(Nat.beq (pc G G) Idn, Bool.not (Nat.beq G Idn))

@[expose] noncomputable def adj0K (r : Nat) : Bool :=
  bAnd(Bool.not (Nat.beq r 0), strictB (pc (cA r) (pc RHO (cIA r))) fun Q =>
    strictB (pc Q Q) fun Q2 => strictB (pc RHO RHO) fun R2 =>
      bIf(bIf(invoK (pc RHO Q), true, invoK (pc RHO Q2)), true,
        bIf(invoK (pc R2 Q), true, invoK (pc R2 Q2))))

@[expose] noncomputable def rtK (k : Nat) : Nat := nIf(Nat.beq k 0, 1, nIf(Nat.beq k 1, 2, 202))
@[expose] noncomputable def rdK (k : Nat) : Nat := nIf(Nat.beq k 2, 3, 2)
@[expose] noncomputable def dlK (k : Nat) : Nat := nIf(Nat.beq k 0, 18, nIf(Nat.beq k 1, 4, 486))
@[expose] noncomputable def soK (k : Nat) : Nat := nIf(Nat.beq k 0, 0, nIf(Nat.beq k 1, 36, 44))

@[expose] noncomputable def dK (r : Nat) : Nat :=
  nIf(Nat.beq r 0, 0, nIf(Nat.beq r 10, 1, nIf(Nat.beq r 202, 3, 2)))
@[expose] noncomputable def vdK (y : Nat) : Nat := nIf(Nat.blt y 22880, dK (frootK y), 4)

@[expose] noncomputable def posK (k a : Nat) : Nat := pg 10 (mask 10) (Q3AP k) a
@[expose] noncomputable def dsK (k a : Nat) : Nat := pg 15 (mask 15) (Q3AD k) a

@[expose] noncomputable def dsChk (k : Nat) : Bool :=
  strictB (cA (rtK k)) fun C => strictB (rdK k) fun d => strictB (dlK k) fun n =>
    bAnd(Nat.beq (countK (nat_lit 486) fun t =>
        Nat.beq (Nat.succ (vdK (actK C (n0K t)))) d) n,
    bAnd(allN (Nat.sub n 1) (fun a => Nat.blt (posK k a) (posK k (Nat.succ a))),
      allN n (fun a => strictB (posK k a) fun t => bAnd(Nat.blt t (nat_lit 486),
        strictB (actK C (n0K t)) fun y => bAnd(Nat.beq (dsK k a) y,
          Nat.beq (Nat.succ (vdK y)) d)))))

@[expose] noncomputable def ciK (k a : Nat) : Nat := Q3ACI (Nat.add (Nat.mul (nat_lit 512) k) a)

@[expose] noncomputable def parK (k b : Nat) : Nat := spanK (Nat.add (soK k) b)
@[expose] noncomputable def depK (k b : Nat) : Nat := spanK (Nat.add (Nat.add (soK k) (dlK k)) b)

@[expose] noncomputable def hasChild (k a : Nat) : Bool :=
  Bool.not (allN (dlK k) fun b => Bool.not (bAnd(Bool.not (Nat.beq b 0), Nat.beq (parK k b) a)))

@[expose] noncomputable def adjK (C v : Nat) : Bool :=
  strictB (actK C v) fun y => bAnd(Nat.blt y (nat_lit 22880), Nat.beq (frootK y) (nat_lit 10))

@[expose] noncomputable def ciSl (k a : Nat) : Bool :=
  bIf(bIf(Nat.blt k 2, true, hasChild k a), Nat.beq (ciK k a) (cIA (dsK k a)), true)

@[expose] noncomputable def spShape (k : Nat) : Bool :=
  allN (dlK k) fun b => bIf(Nat.beq b 0, true, strictB (parK k b) fun a =>
    bAnd(Nat.blt a (dlK k), Nat.blt (depK k a) (depK k b)))

@[expose] noncomputable def spSl (k a : Nat) : Bool :=
  bIf(hasChild k a, strictB (ciK k a) fun C => allN (dlK k) fun b =>
    bIf(bAnd(Bool.not (Nat.beq b 0), Nat.beq (parK k b) a), adjK C (dsK k b), true), true)

@[expose] noncomputable def q2Sl (k t : Nat) : Bool :=
  strictB (actK (cA (rtK k)) (n0K t)) fun g =>
  strictB (Q3AQ (Nat.add (Nat.mul (nat_lit 512) k) t)) fun w =>
  strictB (Nat.mod w 4) fun ty => strictB (Nat.mod (Nat.div w 4) 32) fun a =>
  bIf(Nat.beq w 0, Bool.not (Nat.beq (vdK g) 2),
    bAnd(Nat.blt a (dlK k), bIf(Nat.beq ty 1, adjK (ciK k a) g,
      bAnd(Nat.beq ty 2, strictB (Nat.div w 128) fun u => bAnd(Nat.blt u 486,
        strictB (actK (cA g) (n0K u)) fun c' =>
          bAnd(Nat.beq (vdK c') 1, adjK (ciK k a) c'))))))

@[expose] noncomputable def ci0 (a : Nat) : Bool := ciSl 0 a
@[expose] noncomputable def ci1 (a : Nat) : Bool := ciSl 1 a
@[expose] noncomputable def ci2 (a : Nat) : Bool := ciSl 2 a
@[expose] noncomputable def sp0 (a : Nat) : Bool := spSl 0 a
@[expose] noncomputable def sp1 (a : Nat) : Bool := spSl 1 a
@[expose] noncomputable def sp2 (a : Nat) : Bool := spSl 2 a
@[expose] noncomputable def qa (t : Nat) : Bool := q2Sl 0 t
@[expose] noncomputable def qb (t : Nat) : Bool := q2Sl 1 t

end CertificateChecks.KernelSpor.Q3AK

end
