module

public import Certificates.Kernel.SporSch.PairHS.HS7208Data
public import Certificates.Kernel.SporSch.PairHS.HS2272Fns
public import Certificates.Data.Kernel.SporSch.HS7208K

public section

namespace CertificateChecks.KernelSporSch.HS78

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.KS.HS2272 CFSG.KS.HS7208
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.HS72 CFSG.KD.LQT.C4126

@[expose] def b2 : List Nat := [nat_lit 0, nat_lit 1]

@[expose] noncomputable def k2 (f : Nat → Nat) : Nat := keyL (nat_lit 3850) f b2

@[expose] noncomputable def cw (w : List Nat) (x : Nat) : Nat := wv (LC (nat_lit 1)) w x

@[expose] noncomputable def t0 (x : Nat) : Nat := tR (nat_lit 1) x

@[expose] noncomputable def w0 (x : Nat) : Nat :=
  wv LP (HSD.uc.getD (nat_lit 1) (nat_lit 0, [])).2 (uP x)

@[expose] noncomputable def GT (l x : Nat) : Nat := cw (H78D.gw.getD l []) x

@[expose] noncomputable def eK (i : Nat) : Nat := pg (nat_lit 24) (mask (nat_lit 24)) H78D.K i

@[expose] noncomputable def eCl (i : Nat) : Nat := pg (nat_lit 3) (mask (nat_lit 3)) H78D.cl i

@[expose] noncomputable def eTx (i : Nat) : Nat := pg (nat_lit 12) (mask (nat_lit 12)) H78D.tx i

@[expose] noncomputable def eXp (i : Nat) : Nat := pg (nat_lit 7) (mask (nat_lit 7)) H78D.xp i

@[expose] noncomputable def eWi (i : Nat) : Nat := pg (nat_lit 14) (mask (nat_lit 14)) H78D.wi i

@[expose] noncomputable def eWo (i : Nat) : Nat := pg (nat_lit 14) (mask (nat_lit 14)) H78D.wo i

@[expose] noncomputable def xS (a : Nat) : Nat := pg (nat_lit 12) (mask (nat_lit 12)) H78D.xs a

@[expose] noncomputable def tK (j : Nat) : Nat := pg (nat_lit 24) (mask (nat_lit 24)) H78D.TK j

@[expose] noncomputable def tM (q : Nat) : Nat := pg (nat_lit 6) (mask (nat_lit 6)) H78D.tm q

@[expose] noncomputable def clsB (x : Nat → Nat) (c : List Nat) (r : Nat) : Bool :=
  bIf(bAnd(eqOnL bs4 (fun p => x (x p)) (fun p => p), neL bs4 x (fun p => p)),
    bAnd(Nat.blt r (nat_lit 2), eqOnL bs4 (cjv LP c x) (tR r)), Nat.beq r (nat_lit 4))

@[expose] noncomputable def witB (f : Nat → Nat) (v : Nat) : Bool :=
  ncW (nat_lit 3850) f (GT (Nat.mod v (nat_lit 4))) (Nat.div v (nat_lit 4))

@[expose] noncomputable def eAt (i : Nat) (w c : List Nat) : Bool :=
  bAnd(Nat.beq (eK i) (k2 (cw w)),
  bAnd(ordK (nat_lit 2880) eK i,
  bAnd(clsB (cw w) c (eCl i),
  bAnd(strictB (eTx i) (fun j => bAnd(Nat.blt j (nat_lit 2880),
      Nat.beq (k2 (fun p => t0 (cw w p))) (eK j))),
  bAnd(bIf(bAnd(Nat.beq (eCl i) (nat_lit 1), Nat.beq (eCl (eTx i)) (nat_lit 1)),
      strictB (eXp i) (fun a => bAnd(Nat.blt a (nat_lit 72), Nat.beq (xS a) i)), true),
  bAnd(bIf(memN i H78D.sk, true, witB (cw w) (eWi i)),
    witB (fun p => w0 (cw w p)) (eWo i)))))))

@[expose] noncomputable def eRun (i₀ : Nat) (ws cs : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Nat → List (List Nat) → Bool) (fun _ _ => true)
    (fun w _ ih i cs => bAnd(eAt i w (cs.headD []), ih (Nat.succ i) cs.tail)) ws i₀ cs

@[expose] noncomputable def eB (g r : Nat) : Bool :=
  strictB (Nat.mul (Nat.add (Nat.mul g (nat_lit 8)) r) (nat_lit 45)) (fun i₀ =>
    eRun i₀ ((H78D.w.drop i₀).take (nat_lit 45)) ((H78D.cj.drop i₀).take (nat_lit 45)))

@[expose] noncomputable def pE (b : Nat → Nat) (ib a a' : Nat) (c : Nat → Nat) (v : Nat) : Bool :=
  bIf(Nat.beq v (nat_lit 0), bIf(Nat.beq a' a, true, Nat.beq (xS a') (eTx ib)),
    bIf(Nat.beq (Nat.mod v (nat_lit 2)) (nat_lit 1), ncW (nat_lit 3850) b c (Nat.div v (nat_lit 2)),
      strictB (Nat.sub (Nat.div v (nat_lit 2)) (nat_lit 1)) (fun m => bAnd(Nat.blt m (nat_lit 2880),
        bAnd(Nat.beq (k2 (fun p => b (c p))) (eK m),
          bIf(bAnd(Nat.beq (eCl m) (nat_lit 1), Nat.beq (eCl (eTx m)) (nat_lit 1)), false, true))))))

@[expose] noncomputable def pRow (b : Nat → Nat) (ib a P : Nat) (cs : List (List Nat)) (a' : Nat) :
    Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ ih a' => bAnd(pE b ib a a' (cw c) (pg (nat_lit 14) (mask (nat_lit 14)) P a'),
      ih (Nat.succ a'))) cs a'

@[expose] noncomputable def pAt (a : Nat) : Bool :=
  strictB (xS a) (fun ib => strictB (H78D.pv.getD a (nat_lit 0)) (fun P =>
    bAnd(Nat.blt ib (nat_lit 2880),
    bAnd(Nat.beq (k2 (cw (H78D.xw.getD a []))) (eK ib),
      pRow (cw (H78D.xw.getD a [])) ib a P H78D.xw (nat_lit 0)))))

@[expose] noncomputable def pB (g r : Nat) : Bool := pAt (Nat.add (Nat.mul g (nat_lit 9)) r)

@[expose] noncomputable def tAt (j : Nat) (t : List Nat) : Bool :=
  bAnd(Nat.beq (tK j) (k2 (wv GT t)),
  bAnd(ordK (nat_lit 64) tK j,
    allN (nat_lit 4) (fun l => strictB (tM (Nat.add (Nat.mul j (nat_lit 4)) l)) (fun m =>
      bAnd(Nat.blt m (nat_lit 64), Nat.beq (k2 (fun p => wv GT t (GT l p))) (tK m))))))

@[expose] noncomputable def tRun (ts : List (List Nat)) (j : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun t _ ih j => bAnd(tAt j t, ih (Nat.succ j))) ts j

@[expose] noncomputable def tB : Bool :=
  bAnd(tRun H78D.tw (nat_lit 0),
  bAnd(Nat.beq H78D.tw.length (nat_lit 64), bAnd(Nat.beq H78D.gw.length (nat_lit 4),
    bAnd(Nat.blt H78D.j0 (nat_lit 64), Nat.beq (tK H78D.j0) (k2 t0)))))

@[expose] noncomputable def smallB : Bool :=
  bAnd(Nat.beq H78D.w.length (nat_lit 2880), bAnd(Nat.beq H78D.cj.length (nat_lit 2880),
  bAnd(Nat.beq H78D.xw.length (nat_lit 72), bAnd(Nat.beq H78D.pv.length (nat_lit 72),
  bAnd(Nat.beq H78D.sk.length (nat_lit 4),
    Nat.beq (HSD.uc.getD (nat_lit 1) (nat_lit 0, [])).1 (nat_lit 1))))))

end CertificateChecks.KernelSporSch.HS78

end
