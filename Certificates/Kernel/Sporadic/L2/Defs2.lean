module

public import Certificates.Kernel.Sporadic.L2.Defs

public section

namespace CertificateChecks.KernelSpor.L2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs

local notation "pgk" => pg 11 (mask 11)
local notation "pgv" => pg 12 (mask 12)
local notation "pc" => pcomp 1782 11 (mask 11)
local notation "Idn" => pidn 1782 11
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "inv" => invEqK 1782 11 (mask 11) (1782 * 11)

@[expose] noncomputable def npK (r k : Nat) : Nat := pgv (L2NP.F r) k
@[expose] noncomputable def nqK (r m : Nat) : Nat := pgv (L2NQ.F r) m
@[expose] noncomputable def trK (r t : Nat) : Nat := pgv (L2TR.F r) t
@[expose] noncomputable def tiK (e : Nat) : Nat := pgv (L2TI.F 0) e

@[expose] noncomputable def crK (k : Nat) : Nat :=
  nIf(Nat.beq k 0, 2852, nIf(Nat.beq k 1, 2890, nIf(Nat.beq k 2, 2922, 2970)))
@[expose] noncomputable def v1K (k : Nat) : Nat :=
  nIf(Nat.beq k 0, 2968, nIf(Nat.beq k 1, 2970, nIf(Nat.beq k 2, 2932, 2890)))

@[expose] noncomputable def eltOK (k : Nat) : Bool :=
  bAnd(cn (L2EL.F k), bAnd(cn (L2EI k), elemK k))

@[expose] noncomputable def occQ (y : Nat) : Bool :=
  Bool.not (allN 315 fun m => Bool.not (Nat.beq (nqK 0 m) y))

@[expose] noncomputable def nbPStep (k : Nat) : Bool :=
  bAnd(Nat.beq (nIf(Nat.blt k 18, 1, 0)) (nIf(Nat.blt (nbK 0 k) 2835, 1, 0)),
    bIf(Nat.beq k 0, true, bIf(Nat.beq k 18, true,
      strictB (npK 0 k) fun a => strictB (npK 1 k) fun l =>
        bAnd(Nat.blt a 36, bAnd(Nat.blt (npK 2 a) (npK 2 k), bAnd(Nat.blt l 6,
          sendsE l (nbK 0 a) (nbK 0 k)))))))

@[expose] noncomputable def nbPSl (s : Nat) : Bool := allBlk (Nat.mul 18 s) nbPStep 18

@[expose] noncomputable def nbPK : Bool :=
  bAnd(allN 6 (fun l => sendsE l 0 0), bAnd(Nat.beq (nbK 0 0) 342, bAnd(Nat.beq (nbK 0 18) 2835,
    allN 2997 (fun y => bIf(adjK 0 y, occK 0 y, true)))))

@[expose] noncomputable def nbQStep (m : Nat) : Bool :=
  bIf(Nat.beq m 0, true, bIf(Nat.blt m 315,
    strictB (nqK 1 m) fun a => strictB (nqK 2 m) fun l =>
      bAnd(Nat.blt a 315, bAnd(Nat.blt (nqK 3 a) (nqK 3 m), bAnd(Nat.blt l 6,
        sendsE (Nat.add 6 l) (nqK 0 a) (nqK 0 m)))), true))

@[expose] noncomputable def nbQSl (s : Nat) : Bool := allBlk (Nat.mul 20 s) nbQStep 20

@[expose] noncomputable def nbQK : Bool :=
  bAnd(allN 6 (fun l => sendsE (Nat.add 6 l) 2835 2835), bAnd(Nat.beq (nqK 0 0) 0,
    allN 2997 (fun y => bIf(adjK 2835 y, occQ y, true))))

@[expose] noncomputable def locK : Bool :=
  bAnd(adjK 0 342, bAnd(adjK 0 2835, bAnd(sendsE 12 0 342, sendsE 12 342 0)))

@[expose] noncomputable def cellK (k : Nat) : Bool :=
  bAnd(sendsE (Nat.add 13 k) 0 0, bAnd(sendsE (Nat.add 13 k) 2835 (crK k),
    bAnd(sendsE (Nat.add 17 k) 0 0, bAnd(sendsE (Nat.add 17 k) 2835 (v1K k),
      sendsE 12 (v1K k) (crK k)))))

@[expose] noncomputable def eltSl (s : Nat) : Bool := allBlk (Nat.mul 7 s) eltOK 7

@[expose] noncomputable def triRK : Bool :=
  allN 4 (fun k => bAnd(Nat.beq (trK 0 k) 342, Nat.beq (trK 1 k) (crK k)))

@[expose] noncomputable def triStep (t : Nat) : Bool :=
  bIf(Nat.blt t 4, true, bIf(Nat.blt t 180,
    strictB (trK 2 t) fun a => strictB (trK 3 t) fun l =>
      bAnd(Nat.blt a t, bAnd(Nat.blt l 6, bAnd(sendsE l (trK 0 a) (trK 0 t),
        sendsE l (trK 1 a) (trK 1 t)))), true))

@[expose] noncomputable def triSl (s : Nat) : Bool := allBlk (Nat.mul 10 s) triStep 10

@[expose] noncomputable def triLK : Bool :=
  allN 18 fun a => allN 18 fun b => bIf(adjK (nbK 0 a) (nbK 0 (Nat.add 18 b)),
    strictB (tiK (Nat.add (Nat.mul 18 a) b)) fun t => bAnd(Nat.blt t 180,
      bAnd(Nat.beq (trK 0 t) (nbK 0 a), Nat.beq (trK 1 t) (nbK 0 (Nat.add 18 b)))), true)

@[expose] noncomputable def commK2 (G H : Nat) : Bool := Nat.beq (pc G H) (pc H G)

@[expose] noncomputable def basicK : Bool :=
  bAnd(Bool.not (Nat.beq RHO Idn), bAnd(memXK RHO, bAnd(memXK T1,
  bAnd(inv T1 T1, bAnd(inv W0 W0, bAnd(commK2 W0 T1,
  bAnd(commK2 W0 (pc RHO (pc W0 RHOI)), Bool.not (Nat.beq W0 (pc RHO (pc W0 RHOI))))))))))

@[expose] noncomputable def classK : Bool :=
  Nat.beq (pc RHO RHO) (pc Q3AK.S1 (pc RHO (Q3AI 11)))

@[expose] noncomputable def qEK (j x : Nat) : Nat :=
  SuzWK.qPtK KernelLC.SuzB0Q.F (Nat.div j 2) 6 (nIf(Nat.beq (Nat.mod j 2) 1, pgk T1 x, x))

@[expose] noncomputable def eqQ (i j : Nat) : Bool :=
  allN 1782 fun x => Nat.beq (pgk (L2A i) x) (qEK j x)

@[expose] noncomputable def fQ (j : Nat) : Nat := fpOf (qEK j)

@[expose] noncomputable def bsA (f : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => lo)
    (fun _ ih lo hi => nIf(Nat.blt lo hi,
      strictN (Nat.shiftRight (Nat.add lo hi) (nat_lit 1)) (fun mid =>
        nIf(Nat.blt (fA (ordA mid)) f, ih (Nat.succ mid) hi, ih lo mid)), lo))

@[expose] noncomputable def qChk (j : Nat) : Bool :=
  strictB (fQ j) fun f => strictB (bsA f 13 0 2835) fun m =>
    bIf(bAnd(Nat.blt m 2835, Nat.beq (fA (ordA m)) f),
      strictB (ordA m) fun i => bAnd(Nat.blt i 2835,
        bIf(bAnd(Bool.not (Nat.beq i 0), eqQ i j), adjK 0 i, true)),
      bAnd(Nat.ble m 2835, bAnd(bIf(Nat.beq m 0, true, Nat.blt (fA (ordA (Nat.pred m))) f),
        bIf(Nat.beq m 2835, true, Nat.blt f (fA (ordA m))))))

@[expose] noncomputable def qSl (s : Nat) : Bool := allBlk (Nat.mul 16 s) qChk 16

@[expose] noncomputable def nb0Q (k : Nat) : Bool :=
  strictB (nbK 0 k) fun y => bIf(Nat.blt y 2835,
    bAnd(Bool.not (Nat.beq y 0), Bool.not (allN 128 fun j => Bool.not (eqQ y j))),
    commK2 T1 (TK (Nat.sub y 2835) 0))

@[expose] noncomputable def wCen (j : Nat) : Bool :=
  bIf(commK2 T1 (TK j 0), adjK 0 (Nat.add 2835 j), true)

@[expose] noncomputable def wcSl (s : Nat) : Bool :=
  allBlk (Nat.mul 16 s) (fun j => bIf(Nat.blt j 162, wCen j, true)) 16

@[expose] noncomputable def groupK : Bool :=
  bAnd(Nat.beq (pc (TK 0 0) (TK 0 1)) (TK 0 2), bAnd(commK2 (L2A 342) T1,
    strictB (pc T1 (L2A 342)) fun B => bAnd(Nat.beq (fA 680) (fpK 11 (mask 11) B),
      bAnd(Nat.beq (L2A 680) B, adjK 680 2852))))

end CertificateChecks.KernelSpor.L2K

end
