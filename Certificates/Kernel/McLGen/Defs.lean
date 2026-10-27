module

public import Certificates.Kernel.McLGen.Data
public import Certificates.Kernel.Census.McLChain
public import CFSG.Certificates.Kernel.Spor.SlpCard

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLGen

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.SC

@[expose] noncomputable def LJ (l x : Nat) : Nat := r32 LT (Nat.add (Nat.mul l (nat_lit 275)) x)

@[expose] noncomputable def GJ (z : Int) (x : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => nIf(Nat.beq k (nat_lit 1), r32 AT x, nIf(Nat.beq k (nat_lit 2), r32 BT x, r32 BI x)))
    (fun k => nIf(Nat.beq k (nat_lit 0), r32 AI x, r32 BI x)) z

@[expose] noncomputable def STJ (i : Nat) : Nat := List.getD [8, 10, 12, 14, 17, 18] i (nat_lit 0)

@[expose] noncomputable def BSJ (i : Nat) : Nat := List.getD [0, 3, 4, 5, 1] i (nat_lit 0)

@[expose] noncomputable def LVJ (i t : Nat) : Nat := Nat.add (Nat.mul (nat_lit 2) (STJ i)) t

@[expose] noncomputable def RJ (i : Nat) : Nat := Nat.mul (nat_lit 2) (Nat.sub (STJ (Nat.succ i)) (STJ i))

@[expose] noncomputable def lvSel (fs : List (Nat → Nat)) (i : Nat) : Nat → Nat :=
  List.getD fs i fun _ => nat_lit 0
@[expose] noncomputable def PTSJ : Nat → Nat → Nat := lvSel [CT0.PTS, CT1.PTS, CT2.PTS, CT3.PTS, CT4.PTS]
@[expose] noncomputable def POSJ : Nat → Nat → Nat := lvSel [CT0.POS, CT1.POS, CT2.POS, CT3.POS, CT4.POS]
@[expose] noncomputable def PARJ : Nat → Nat → Nat := lvSel [CT0.PAR, CT1.PAR, CT2.PAR, CT3.PAR, CT4.PAR]
@[expose] noncomputable def LABJ : Nat → Nat → Nat := lvSel [CT0.LAB, CT1.LAB, CT2.LAB, CT3.LAB, CT4.LAB]
@[expose] noncomputable def TIJ : Nat → Nat → Nat := lvSel [CT0.TI, CT1.TI, CT2.TI, CT3.TI, CT4.TI]
@[expose] noncomputable def CNTJ (i : Nat) : Nat :=
  List.getD [CT0.cnt, CT1.cnt, CT2.cnt, CT3.cnt, CT4.cnt] i (nat_lit 0)

@[expose] noncomputable def genOK : Bool :=
  allN (nat_lit 275) fun x => bAnd(Nat.blt (r32 AT x) (nat_lit 275),
    bAnd(Nat.beq (r32 AI (r32 AT x)) x, bAnd(Nat.blt (r32 AI x) (nat_lit 275),
    bAnd(Nat.blt (r32 BT x) (nat_lit 275), bAnd(Nat.beq (r32 BI (r32 BT x)) x,
    bAnd(Nat.blt (r32 BI x) (nat_lit 275),
    bAnd(Nat.beq (r32 AT x) (pg (nat_lit 9) (mask (nat_lit 9)) (CertificateChecks.KernelCensus.McLS.F 0) x),
      Nat.beq (r32 BT x) (pg (nat_lit 9) (mask (nat_lit 9)) (CertificateChecks.KernelCensus.McLS.F 1) x))))))))

@[expose] noncomputable def wordsOK : Bool :=
  allN (nat_lit 18) fun j => allN (nat_lit 275) fun x =>
    Nat.beq (LJ (Nat.mul (nat_lit 2) j) x)
      (List.foldr (slpG GJ LJ) x (CFSG.Sporadic.McL.Gen45.mclGenWords[j]!))

@[expose] noncomputable def invOK' : Bool := invK LJ (nat_lit 275) (nat_lit 36)

@[expose] noncomputable def notK (b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false b

@[expose] noncomputable def pairOK : Bool :=
  bAnd(allN (nat_lit 275) fun x =>
    bAnd(Nat.beq (LJ 0 (LJ 0 x)) x, bAnd(Nat.beq (LJ 6 (LJ 6 x)) x,
    bAnd(Nat.beq (LJ 0 (LJ 6 x)) (LJ 6 (LJ 0 x)), bAnd(Nat.beq (LJ 0 (LJ 16 x)) (LJ 16 (LJ 0 x)),
      Nat.beq (LJ 6 (LJ 18 x)) (LJ 18 (LJ 6 x)))))),
  bAnd(notK (Nat.beq (LJ 0 1) 1), bAnd(notK (Nat.beq (LJ 6 0) 0),
    notK (Nat.beq (LJ 0 0) (LJ 6 0)))))

@[expose] noncomputable def fixOK : Bool :=
  allN (nat_lit 4) fun i => allN (Nat.sub (STJ (Nat.succ (Nat.succ i))) (STJ (Nat.succ i))) fun d =>
    Nat.beq (LJ (Nat.mul (nat_lit 2) (Nat.add (STJ (Nat.succ i)) d)) (BSJ i)) (BSJ i)

@[expose] noncomputable def tree (i : Nat) : Bool :=
  bAnd(tbfsHdK (nat_lit 275) (BSJ i) (CNTJ i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i),
    allN (CNTJ i) (tbfsPtK (nat_lit 275) (CNTJ i) (RJ i) LJ (LVJ i) (PTSJ i) (POSJ i) (PARJ i)
      (LABJ i) (TIJ i)))

end CertificateChecks.KernelMcLGen

end
