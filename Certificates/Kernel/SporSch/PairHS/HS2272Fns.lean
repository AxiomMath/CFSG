module

public import Certificates.Kernel.SporSch.PairHS.HS2272Data
public import Certificates.Kernel.SporSch.PairHS.ClData
public import Certificates.Kernel.LocalQT.SV.C4126T
public import Certificates.Data.Kernel.SporSch.HS2272K

public section

namespace CertificateChecks.KernelSporSch.HS72

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.HS2272 CertificateChecks.KernelSporSch
open CFSG.KD.LQT.C4126

@[expose] def bsR : List Nat := [nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 5]

@[expose] def bs4 : List Nat := [nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3]

@[expose] noncomputable def nfp (F x : Nat) : Nat := nfPtT 12 PHST.NR PHST.NR PHST.LT PHST.PT 4 F x

@[expose] noncomputable def tv (k x : Nat) : Nat := pg 12 (mask 12) (HC.F k) x

@[expose] noncomputable def ti (k x : Nat) : Nat := pg 12 (mask 12) (HCI k) x

@[expose] noncomputable def uP (x : Nat) : Nat := tv (nat_lit 0) x

@[expose] noncomputable def lp (j : Nat) : Nat :=
  nIf(Nat.beq j (nat_lit 0), PHSC.S (nat_lit 0), nIf(Nat.beq j (nat_lit 1),
    PHSC.SI (nat_lit 0), nIf(Nat.beq j (nat_lit 2), PHSC.S (nat_lit 1), PHSC.SI (nat_lit 1))))

@[expose] noncomputable def LP (k x : Nat) : Nat := pg 12 (mask 12) (lp (Nat.mod k (nat_lit 4))) x

@[expose] noncomputable def cb (r : Nat) : Nat :=
  nIf(Nat.beq r (nat_lit 0), nat_lit 6, nIf(Nat.beq r (nat_lit 1), nat_lit 13,
    nIf(Nat.beq r (nat_lit 2), nat_lit 22, nat_lit 35)))

@[expose] noncomputable def ncg (r : Nat) : Nat := nIf(Nat.beq r (nat_lit 0), nat_lit 2, nat_lit 4)

@[expose] noncomputable def rt (r : Nat) : Nat := Nat.sub (cb r) (nat_lit 1)

@[expose] noncomputable def ct (r k : Nat) : Nat :=
  Nat.add (cb r) (Nat.mod (Nat.div k (nat_lit 2)) (ncg r))

@[expose] noncomputable def LC (r k x : Nat) : Nat :=
  nIf(Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 0), tv (ct r k) x, ti (ct r k) x)

@[expose] noncomputable def st (k : Nat) : Nat :=
  Nat.succ (Nat.mod (Nat.div k (nat_lit 2)) (nat_lit 4))

@[expose] noncomputable def LS (k x : Nat) : Nat :=
  nIf(Nat.beq (Nat.mod k (nat_lit 2)) (nat_lit 0), tv (st k) x, ti (st k) x)

@[expose] noncomputable def bndAt (j : Nat) : Nat × Nat × Bool := HSD.bnd.getD j (0, 0, false)

@[expose] noncomputable def bndP (j x : Nat) : Nat :=
  nIf((bndAt j).2.2, nfp (bndAt j).2.1 (uP x), nfp (bndAt j).2.1 x)

@[expose] noncomputable def bindB (j r : Nat) : Bool :=
  eqBlk (Nat.mul r (nat_lit 770)) (nat_lit 770) (tv (bndAt j).1) (bndP j)

@[expose] noncomputable def uaF (i : Nat) : Nat := HSD.ua.getD i 0

@[expose] noncomputable def uaB (i r : Nat) : Bool :=
  eqBlk (Nat.mul r (nat_lit 770)) (nat_lit 770) (fun x => uP (LP (Nat.mul i (nat_lit 2)) (uP x)))
    (nfp (uaF i))

@[expose] noncomputable def validB : Bool :=
  bAnd(allN (nat_lit 22) (fun j => nfValidK (nat_lit 4) PHSC.LR (bndAt j).2.1),
    bAnd(allN (nat_lit 2) (fun i => nfValidK (nat_lit 4) PHSC.LR (uaF i)),
      nfValidK (nat_lit 4) PHSC.LR HSD.z0))

@[expose] noncomputable def uB : Bool :=
  bAnd(eqBlk (nat_lit 0) (nat_lit 3850) (fun x => uP (uP x)) (fun x => x),
    bAnd(bIf(Nat.beq (uP (nat_lit 0)) (nat_lit 0), false, true),
      bAnd(eqOnL bs4 (fun x => nfp HSD.z0 (uP x)) (fun x => x),
        bIf(Nat.beq (nfp HSD.z0 (uP (nat_lit 5))) (nat_lit 5), false, true))))

@[expose] noncomputable def stabF (x : Nat) : Bool :=
  allBlk (nat_lit 0) (fun j => Nat.beq (pg 12 (mask 12) (PHSC.S (Nat.add j (nat_lit 2))) x) x)
    (nat_lit 6)

@[expose] noncomputable def stabX : Bool :=
  allN (nat_lit 3850) (fun x => bIf(Nat.beq x (nat_lit 0), true, bIf(stabF x, false, true)))

@[expose] noncomputable def stabB : Bool := bAnd(stabF (nat_lit 0), stabX)

@[expose] noncomputable def repA : Bool := Nat.beq (HC.F (nat_lit 5)) (PHSC.S (nat_lit 0))

@[expose] noncomputable def tR (r x : Nat) : Nat := tv (rt r) x

@[expose] noncomputable def recB (r : Nat) : Bool :=
  bAnd(eqOnL bsR (fun x => tR r (tR r x)) (fun x => x),
  bAnd(neL bsR (tR r) (fun x => x),
  bAnd(allN (ncg r) (fun j => eqOnL bsR (fun x => tv (Nat.add (cb r) j) (tR r x))
      (fun x => tR r (tv (Nat.add (cb r) j) x))),
  bAnd(Nat.beq (cntFix (nat_lit 3850) (tR r)) (HSD.fx.getD r 0),
  bAnd(chainL (nat_lit 3850) (LC r) (HSD.ch.getD r []) [],
    oddL bsR (LC r) (HSD.od.getD r []))))))

@[expose] def clsz (r : Nat) : Nat := [nat_lit 5775, nat_lit 15400, nat_lit 1100, nat_lit 23100].getD r 0

@[expose] def cnto (r : Nat) : Nat := [nat_lit 7680, nat_lit 2880, nat_lit 40320, nat_lit 1920].getD r 0

@[expose] noncomputable def chainOrd (r : Nat) : Nat :=
  ((HSD.ch.getD r []).map fun v => Nat.succ v.2.2.length).prod

@[expose] noncomputable def dataB (r : Nat) : Bool :=
  bAnd(Nat.beq (chainOrd r) (cnto r),
  bAnd(Nat.beq (Nat.mul (clsz r) (HSD.fx.getD r 0)) (Nat.mul (nat_lit 3850) (HSD.cf.getD r []).length),
  bAnd(Nat.blt (HSD.uc.getD r (0, [])).1 (nat_lit 4),
    eqOnL bsR (cjv LP (HSD.uc.getD r (0, [])).2 (fun x => uP (tR r (uP x))))
      (tR (HSD.uc.getD r (0, [])).1))))

@[expose] noncomputable def cfB (r : Nat) : Bool :=
  cfL (nat_lit 3850) LP (tR r) (HSD.cf.getD r []) (nat_lit 0)

@[expose] noncomputable def wdB : Bool :=
  bAnd(ordPL bsR (wv (LC (nat_lit 3)) (HSD.wd.getD 0 [])) (nat_lit 5),
    ord6L bsR (conjProd (LC (nat_lit 3)) (HSD.wd.getD 0 []) (HSD.wd.getD 1 [])))

@[expose] noncomputable def sK (i : Nat) : Nat := pg (nat_lit 64) (mask (nat_lit 64)) HSD.sK i

@[expose] noncomputable def sM (q : Nat) : Nat := pg (nat_lit 10) (mask (nat_lit 10)) HSD.sM q

@[expose] noncomputable def sS (j : Nat) : Nat := pg (nat_lit 10) (mask (nat_lit 10)) HSD.sS j

@[expose] noncomputable def sSI (i : Nat) : Nat := pg (nat_lit 10) (mask (nat_lit 10)) HSD.sSI i

@[expose] noncomputable def sAt (i : Nat) (w : List Nat) (c : Nat × List Nat) : Bool :=
  bAnd(Nat.beq (sK i) (keyL (nat_lit 3850) (wv LS w) bsR),
  bAnd(allN (nat_lit 4) (fun l => strictB (sM (Nat.add (Nat.mul i (nat_lit 4)) l)) (fun m =>
      bAnd(Nat.blt m (nat_lit 1024),
        Nat.beq (sK m) (keyL (nat_lit 3850) (fun x => wv LS w (LS (Nat.mul l (nat_lit 2)) x))
          bsR)))),
    bIf(bAnd(eqOnL bsR (fun x => wv LS w (wv LS w x)) (fun x => x), neL bsR (wv LS w) (fun x => x)),
      bAnd(Nat.blt c.1 (nat_lit 4), eqOnL bsR (cjv LP c.2 (wv LS w)) (tR c.1)), true)))

@[expose] noncomputable def sRun (i₀ : Nat) (ws : List (List Nat)) (cs : List (Nat × List Nat)) :
    Bool :=
  List.rec (motive := fun _ => Nat → List (Nat × List Nat) → Bool) (fun _ _ => true)
    (fun w _ ih i cs => bAnd(sAt i w (cs.headD (0, [])), ih (Nat.succ i) cs.tail)) ws i₀ cs

@[expose] noncomputable def sB (g r : Nat) : Bool :=
  strictB (Nat.mul (Nat.add (Nat.mul g (nat_lit 8)) r) (nat_lit 8)) (fun i₀ =>
    sRun i₀ ((HSD.sw.drop i₀).take (nat_lit 8)) ((HSD.sc.drop i₀).take (nat_lit 8)))

@[expose] noncomputable def sortB : Bool :=
  bAnd(Nat.beq (sK (nat_lit 0)) (keyL (nat_lit 3850) (fun x => x) bsR),
  bAnd(Nat.beq HSD.sw.length (nat_lit 1024), bAnd(Nat.beq HSD.sc.length (nat_lit 1024),
    sortK (nat_lit 1024) sK sS sSI)))

end CertificateChecks.KernelSporSch.HS72

end
