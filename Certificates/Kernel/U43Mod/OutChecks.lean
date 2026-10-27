module

public import Certificates.Data.Kernel.U43Mod.OutDefs
public import Certificates.Data.Kernel.U43Mod.Aut3962
public import Certificates.Kernel.U43Mod.OutData
public import Certificates.Kernel.U43Mod.InvChecks
public import Certificates.Kernel.U43Mod.Checks3962
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43OutData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Out

open CFSG.KC.Enum CFSG.KC.U43Inv CFSG.KC.U43Out CertificateChecks.KernelU43Inv
open CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv
open CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Out

@[expose] noncomputable def LP8 (l q : Nat) : Nat :=
  nIf(Nat.blt l (nat_lit 4), LP l q,
    nIf(Nat.beq l (nat_lit 4), pg (nat_lit 10) (nat_lit 1023) (KernelU43Aut3962.DT (nat_lit 0)) q,
    nIf(Nat.beq l (nat_lit 5), pg (nat_lit 10) (nat_lit 1023) (KernelU43Aut3962.DT (nat_lit 1)) q,
    nIf(Nat.beq l (nat_lit 6), pg (nat_lit 10) (nat_lit 1023) (KernelU43Aut3962.DTI (nat_lit 0)) q,
      pg (nat_lit 10) (nat_lit 1023) (KernelU43Aut3962.DTI (nat_lit 1)) q))))

@[expose] noncomputable def GkT (l q : Nat) : Nat := pg (nat_lit 10) (nat_lit 1023) (TT l) q

@[expose] noncomputable def GrT (l q : Nat) : Nat :=
  pg (nat_lit 10) (nat_lit 1023) (TT (Nat.xor l (nat_lit 1))) q

@[expose] noncomputable def ET (k q : Nat) : Nat := eW TR GrT (nat_lit 32) k q

@[expose] noncomputable def ETi (k q : Nat) : Nat := eWi TR GkT (nat_lit 32) k q

@[expose] noncomputable def EPi (j q : Nat) : Nat := eWi PR GkP (nat_lit 32) j q

@[expose] noncomputable def dIPow (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (pidn 820 10)
    (fun _ ih => KernelU43Aut3962.pc (KernelU43Aut3962.DTI (nat_lit 0)) ih) m

@[expose] noncomputable def cosI (c : Nat) : Nat :=
  KernelU43Aut3962.pc (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
      pidn 820 10, KernelU43Aut3962.DTI (nat_lit 1)))
    (dIPow (Nat.shiftRight c (nat_lit 1)))

@[expose] noncomputable def rpt (A B i j q : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    (nIf(Nat.beq j (nat_lit 0), q, pg (nat_lit 10) (nat_lit 1023) B q))
    (fun _ ih => pg (nat_lit 10) (nat_lit 1023) A ih) i

@[expose] def bs4 : List Nat := [0, 1, 9, 84]

@[expose] noncomputable def xRec (X : Nat → Nat) (e : Nat) : Bool :=
  strictB (Nat.add (nat_lit 7) (Nat.shiftLeft e (nat_lit 1))) fun h =>
    bAnd(permOK 820 10 (CFSG.KS.mask 10) (820 * 10) (TT h) (TT (Nat.sub h (nat_lit 1))),
    bAnd(KernelU43Aut3962.inN (KernelU43Aut3962.pc (TT h) (cosI (X e))),
      CFSG.KC.U43Mod.baseEq bs4 (pg (nat_lit 10) (nat_lit 1023) (TT h))
        (mwv LP8 (CFSG.KC.U43Aut3962.lSel [] tExtraWords e))))

@[expose] noncomputable def sRec (W L : Nat → Nat) (c : Nat) : Bool :=
  strictB (Nat.shiftRight c (nat_lit 1)) fun i => strictB (Nat.land c (nat_lit 1)) fun j =>
    bAnd(base3 (pwv LP (W c) (L c)) (rpt (KernelU43Aut3962.DT (nat_lit 0)) (KernelU43Aut3962.DT (nat_lit 1)) i j),
      bIf(Nat.beq c (nat_lit 0), true, bNot (Nat.beq (pwv LP (W c) (L c) (nat_lit 84))
        (rpt (KernelU43Aut3962.DT (nat_lit 0)) (KernelU43Aut3962.DT (nat_lit 1)) i j (nat_lit 84)))))

@[expose] noncomputable def innerOK (k j : Nat) : Bool :=
  bAnd(Nat.blt j (nat_lit 128), strictB (TR k) fun r => strictB (PR j) fun rp =>
    bAnd(Nat.beq (kf r (nat_lit 0)) (kf rp (nat_lit 0)), bAnd(Nat.beq (kf r (nat_lit 1)) (kf rp (nat_lit 1)),
      bAnd(Nat.beq (kf r (nat_lit 2)) (kf rp (nat_lit 2)), Nat.beq (f4 r) (EPi j (nat_lit 84))))))

@[expose] noncomputable def uPt (k : Nat) (w : List Nat) (p : Nat) : Nat :=
  ET k (mwv LP w (ET k (mwvI LP w p)))

@[expose] noncomputable def witOK (k i q : Nat) : Bool :=
  bAnd(Nat.blt i (nat_lit 3), bAnd(Nat.blt q (nat_lit 820),
    orbOK (uPt k (CFSG.KC.U43Aut3962.lSel [] witWords i)) q (nat_lit 5) q))

@[expose] noncomputable def fRec (F S : Nat → Nat) (k : Nat) : Bool :=
  strictB (F k) fun d => strictB (Nat.land d (nat_lit 3)) fun t =>
    strictB (Nat.shiftRight d (nat_lit 2)) fun x =>
      bIf(Nat.beq t (nat_lit 0), innerOK k x,
      bIf(Nat.beq t (nat_lit 1), bAnd(Nat.blt x (nat_lit 820), bNot (Nat.beq (ET k (ET k x)) x)),
      bIf(Nat.beq t (nat_lit 2), witOK k (Nat.land x (nat_lit 3)) (Nat.shiftRight x (nat_lit 2)),
        bAnd(Nat.blt x (nat_lit 24), Nat.beq (S x) k))))

@[expose] noncomputable def prodKey (k₁ k₂ r : Nat) : Bool :=
  bAnd(Nat.beq (kf r (nat_lit 0)) (ETi k₂ (ETi k₁ (nat_lit 0))),
  bAnd(Nat.beq (kf r (nat_lit 1)) (ETi k₂ (ETi k₁ (nat_lit 1))),
  bAnd(Nat.beq (kf r (nat_lit 2)) (ETi k₂ (ETi k₁ (nat_lit 9))),
    Nat.beq (f4 r) (ETi k₂ (ETi k₁ (nat_lit 84))))))

@[expose] noncomputable def pRec (F : Nat → Nat) (k₁ k₂ d : Nat) : Bool :=
  strictB (Nat.land d (nat_lit 3)) fun t => strictB (Nat.shiftRight d (nat_lit 2)) fun x =>
    bIf(Nat.beq t (nat_lit 0),
      bAnd(Nat.blt x (nat_lit 820), bNot (Nat.beq (ET k₁ (ET k₂ x)) (ET k₂ (ET k₁ x)))),
      bAnd(Nat.beq t (nat_lit 1), bAnd(Nat.blt x (nat_lit 1024),
        strictB (Nat.land (F x) (nat_lit 3)) fun tm =>
          bAnd(bIf(Nat.beq tm (nat_lit 0), true, Nat.beq tm (nat_lit 2)), prodKey k₁ k₂ (TR x)))))

theorem kTP : allN 3 (fun j => allN 820 (fun q =>
    bAnd(Nat.beq (pg 10 1023 (TT (Nat.succ (Nat.shiftLeft j 1))) q) (EH (pIdx j) q),
      Nat.beq (pg 10 1023 (TT (Nat.shiftLeft j 1)) q) (EHi (pIdx j) q)))) = true := by
  quickRfl

theorem kTX : allN 2 (xRec XC) = true := by quickRfl

theorem kSep : allN 8 (sRec MW ML) = true := by quickRfl

theorem kTpar : fldsAre TR kpar (nat_lit 1024) tPar.toList = true := by quickRfl

theorem kTlab : fldsAre TR klab (nat_lit 1024) tLab.toList = true := by quickRfl

theorem kTtree : kTree TR (nat_lit 1024) (nat_lit 10) GkT = true := by quickRfl

theorem kT4 : k4Tree TR (nat_lit 1024) GkT = true := by quickRfl

theorem kTclos : tClos TR (nat_lit 1024) (nat_lit 10) GkT tTbl.toList = true := by quickRfl

theorem kTord : kOrd TR (nat_lit 1024) TO = true := by quickRfl

theorem kF : allN 1024 (fRec FR SK) = true := by quickRfl

theorem kPW : allN 576 (fun i => pRec FR (SK (Nat.div i 24)) (SK (Nat.mod i 24)) (PW i)) = true := by
  quickRfl

end CertificateChecks.KernelU43Out

end
