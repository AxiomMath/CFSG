module

public import Certificates.Kernel.Fi22Reps.Data
public import Certificates.Kernel.Fi22Cls.Each
public import Certificates.Data.Kernel.Fi22Reps.Check

public section

namespace CertificateChecks.KernelFi22Reps

open CFSG.KC.Enum CFSG.KC.Fi22S0 CFSG.KC.Fi22Cls CFSG.KC.Fi22Reps CFSG.KS.Row
  CertificateChecks.KernelFi22S0 CertificateChecks.KernelFi22Cls

@[expose] noncomputable def td (o i : Nat) : Nat := rg (nat_lit 16) (nat_lit 65535) DF o i

@[expose] noncomputable def tw (o i : Nat) : Nat :=
  rg (nat_lit 64) (nat_lit 18446744073709551615) WF o i

@[expose] noncomputable def pa (k t : Nat) : Nat := td (nat_lit 0) (Nat.add (Nat.mul (nat_lit 8) k) t)

@[expose] noncomputable def pb (k t : Nat) : Nat := td (nat_lit 1) (Nat.add (Nat.mul (nat_lit 8) k) t)

@[expose] noncomputable def nLev (k : Nat) : Nat := pa k (nat_lit 0)

@[expose] noncomputable def lv0 (k : Nat) : Nat := pa k (nat_lit 1)

@[expose] noncomputable def nP (k : Nat) : Nat := pa k (nat_lit 2)

@[expose] noncomputable def P (k m : Nat) : Nat := tw (pa k (nat_lit 3)) m

@[expose] noncomputable def dep (k : Nat) : Nat := pa k (nat_lit 4)

@[expose] noncomputable def xs (k : Nat) : Nat := pa k (nat_lit 5)

@[expose] noncomputable def nd (k t : Nat) : Nat := td (pa k (nat_lit 6)) t

@[expose] noncomputable def fp (k w : Nat) : Nat := td (pa k (nat_lit 7)) w

@[expose] noncomputable def bp (k t : Nat) : Nat := pb k t

@[expose] noncomputable def sw (k i : Nat) : Nat := td (pb k (nat_lit 5)) i

@[expose] noncomputable def nF (k : Nat) : Nat := pb k (nat_lit 6)

@[expose] noncomputable def xT (k : Nat) : Nat := XF (Nat.sub (Nat.add (xs k) (dep k)) (nat_lit 1))

@[expose] noncomputable def lf (lv t : Nat) : Nat := td (Nat.add (nat_lit 2) lv) t

@[expose] noncomputable def ln (lv : Nat) : Nat := lf lv (nat_lit 0)

@[expose] noncomputable def ls (lv : Nat) : Nat := lf lv (nat_lit 1)

@[expose] noncomputable def f1 (lv : Nat) : Nat := lf lv (nat_lit 2)

@[expose] noncomputable def f2 (lv : Nat) : Nat := lf lv (nat_lit 3)

@[expose] noncomputable def cd (lv w : Nat) : Nat := td (lf lv (nat_lit 4)) w

@[expose] noncomputable def cl (lv v : Nat) : Nat := td (lf lv (nat_lit 5)) v

@[expose] noncomputable def cb (lv m : Nat) : Nat := td (lf lv (nat_lit 6)) m

@[expose] noncomputable def lk (lv : Nat) : Nat := lf lv (nat_lit 7)

@[expose] noncomputable def li (lv : Nat) : Nat := lf lv (nat_lit 8)

@[expose] noncomputable def wd (v : Nat) : Nat := tw (nat_lit 0) v

@[expose] noncomputable def LT (c : Nat) : Nat := RF (nIf(Nat.blt c (nat_lit 2), c, nat_lit 2))

@[expose] noncomputable def w4 (t : Nat) : Nat := td (pb (nat_lit 3) (nat_lit 7)) t

@[expose] noncomputable def bsP (t : Nat) : Nat :=
  List.getD [nat_lit 0, nat_lit 1, nat_lit 6, nat_lit 11, nat_lit 3] t (nat_lit 0)

@[expose] noncomputable def ch13621word (q : Nat) : Bool := blkC (nat_lit 135) (wordC LT wd) q

@[expose] noncomputable def ch13621xt (k : Nat) : Bool :=
  allN (dep k) fun t => xtC XF gR pp pj (nd k) (xs k) (Nat.succ t)

@[expose] noncomputable def ch13621phi (k : Nat) : Bool :=
  allN (nP k) (phiC LT wd (xT k) (P k) (fun u => ln (Nat.add (lv0 k) u)) (nLev k))

@[expose] noncomputable def ch13621fix (k : Nat) : Bool :=
  allN (nat_lit 3510) (fixC (xT k) (P k) (fp k) (nF k))

@[expose] noncomputable def ch13621par (k : Nat) : Bool :=
  bAnd(Nat.beq (nd k (nat_lit 0)) (nat_lit 0), bAnd(Nat.beq (nd k (dep k)) (glob k),
  bAnd(Nat.blt (nat_lit 0) (dep k), bAnd(Nat.blt (nat_lit 0) (nLev k),
  bAnd(allN (nF k) (fun m => Nat.beq fld(P k m, nat_lit 12, nat_lit 3) (nat_lit 0)),
  bAnd(allN (nat_lit 5) (fun t => strictB (bp k t) fun m =>
    bAnd(Nat.blt m (nP k), Nat.beq (ptE (P k m)) (bsP t))),
  bAnd(Nat.beq (ln (lv0 k)) (nF k),
    allN (nLev k) fun i => strictB (Nat.add (lv0 k) i) fun lv =>
      bAnd(Nat.beq (lk lv) k, bAnd(Nat.beq (li lv) i,
        bIf(Nat.blt (Nat.succ i) (nLev k), Nat.blt (ln lv) (ln (Nat.succ lv)),
          Nat.blt (ln lv) (nP k)))))))))))

@[expose] noncomputable def ch13621lev (q : Nat) : Bool :=
  strictB (Nat.div q (nat_lit 5)) fun lv => strictB (lk lv) fun k =>
    blkC (nat_lit 702) (levC LT wd (xT k) (P k) (cd lv) (cl lv) (cb lv) (ln lv) (ls lv) (f1 lv)
      (f2 lv)) (Nat.mod q (nat_lit 5))

@[expose] noncomputable def ch13621levb (lv : Nat) : Bool :=
  strictB (lk lv) fun k =>
    allN (Nat.succ (ln lv)) (levB LT wd (xT k) (P k) (cb lv) (ln lv) (f1 lv))

@[expose] noncomputable def ch13621scan (lv : Nat) : Bool :=
  strictB (lk lv) fun k => allN (nat_lit 3510) (scanC LT wd (xT k) (P k) (ln lv) (f2 lv))

@[expose] noncomputable def ch13621sep (q : Nat) : Bool :=
  strictB (nIf(Nat.blt q (nat_lit 3), nat_lit 1, nIf(Nat.blt q (nat_lit 7), nat_lit 2, nat_lit 3)))
    fun k => strictB (nIf(Nat.blt q (nat_lit 3), q,
      nIf(Nat.blt q (nat_lit 7), Nat.sub q (nat_lit 3), Nat.sub q (nat_lit 7)))) fun r =>
      blkC (nat_lit 9) (fun m => bIf(Nat.blt m (nF k), sepC LT wd (P k) (sw k) (nF k) m, false)) r

@[expose] noncomputable def ch13621ord : Bool := ordC LJT w4 (nat_lit 17) (xT (nat_lit 0)) k0

end CertificateChecks.KernelFi22Reps

end
