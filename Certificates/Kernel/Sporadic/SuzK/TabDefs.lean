module

public import Certificates.Kernel.Sporadic.SuzK.Data
public import Certificates.Data.Kernel.Spor.PChain
public import Certificates.Data.Kernel.F3Bfs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.Sporadic.Suz.Native

@[expose] noncomputable def LJ (l x : Nat) : Nat := r32 LT (Nat.add (Nat.mul l (nat_lit 22880)) x)

@[expose] noncomputable def BJ (i : Nat) : Nat := i

@[expose] noncomputable def bfsK : Bool :=
  CFSG.KC.F3Bfs.bfsOrderOK (r32 AL) (r32 BE) (r32 PA) (r32 LB) (nat_lit 22880)

@[expose] noncomputable def depK : Bool :=
  bAnd(Nat.beq (r32 DP (nat_lit 0)) (nat_lit 0),
    allN (nat_lit 22880) fun k => strictB (r32 DP k) fun e => bAnd(Nat.blt e (nat_lit 1000),
      bIf(Nat.beq k (nat_lit 0), true, Nat.beq e (Nat.succ (r32 DP (r32 PA k))))))

@[expose] noncomputable def symK (s x : Nat) : Nat :=
  nIf(Nat.beq s (nat_lit 0), r32 AL x, nIf(Nat.beq s (nat_lit 1), r32 BE x,
    nIf(Nat.beq s (nat_lit 2), r32 BE (r32 BE x),
      r32 RT (Nat.add (Nat.mul (Nat.sub s (nat_lit 3)) (nat_lit 22880)) x))))

@[expose] noncomputable def ruleK (r : Nat) : Bool :=
  strictB (List.getD RULES (Nat.mul (nat_lit 2) r) (nat_lit 0)) fun a =>
    strictB (List.getD RULES (Nat.succ (Nat.mul (nat_lit 2) r)) (nat_lit 0)) fun b =>
      allN (nat_lit 22880) fun x => strictB (symK b x) fun y => bAnd(Nat.blt y (nat_lit 22880),
        Nat.beq (symK (Nat.add (nat_lit 3) r) x) (symK a y))

@[expose] noncomputable def cwAt (l : List Nat) (j : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun l => l.tail.take (l.headD (nat_lit 0)))
    (fun _ ih l => ih (l.tail.drop (l.headD (nat_lit 0)))) j l

@[expose] noncomputable def wordsSl (s : Nat) : Bool :=
  strictB (Nat.div s (nat_lit 23)) fun j => strictB (Nat.mul (Nat.mod s (nat_lit 23)) (nat_lit 1000))
    fun lo => allN (nat_lit 1000) fun d => strictB (Nat.add lo d) fun x =>
      bIf(Nat.blt x (nat_lit 22880),
        Nat.beq (LJ (Nat.mul (nat_lit 2) j) x) (List.foldr symK x (cwAt CW j)), true)

@[expose] noncomputable def invSl (j : Nat) : Bool :=
  allN (nat_lit 22880) fun x => strictB (LJ (Nat.mul (nat_lit 2) j) x) fun y =>
    bAnd(Nat.blt y (nat_lit 22880), bAnd(Nat.blt (LJ (Nat.succ (Nat.mul (nat_lit 2) j)) x) (nat_lit 22880),
      Nat.beq (LJ (Nat.succ (Nat.mul (nat_lit 2) j)) y) x))

@[expose] noncomputable def sel (fs : List (Nat → Nat)) (i : Nat) : Nat → Nat :=
  List.getD fs i fun _ => nat_lit 0

@[expose] noncomputable def TPTS : Nat → Nat → Nat :=
  sel [CT0.PTS, CT1.PTS, CT2.PTS, CT3.PTS, ST0.PTS, ST1.PTS, ST2.PTS]
@[expose] noncomputable def TPOS : Nat → Nat → Nat :=
  sel [CT0.POS, CT1.POS, CT2.POS, CT3.POS, ST0.POS, ST1.POS, ST2.POS]
@[expose] noncomputable def TPAR : Nat → Nat → Nat :=
  sel [CT0.PAR, CT1.PAR, CT2.PAR, CT3.PAR, ST0.PAR, ST1.PAR, ST2.PAR]
@[expose] noncomputable def TLAB : Nat → Nat → Nat :=
  sel [CT0.LAB, CT1.LAB, CT2.LAB, CT3.LAB, ST0.LAB, ST1.LAB, ST2.LAB]
@[expose] noncomputable def TTI : Nat → Nat → Nat :=
  sel [CT0.TI, CT1.TI, CT2.TI, CT3.TI, ST0.TI, ST1.TI, ST2.TI]
@[expose] noncomputable def TCNT (i : Nat) : Nat :=
  List.getD [CT0.cnt, CT1.cnt, CT2.cnt, CT3.cnt, ST0.cnt, ST1.cnt, ST2.cnt] i (nat_lit 0)

@[expose] noncomputable def TROOT (i : Nat) : Nat := List.getD [0, 1, 2, 3, 2, 11, 20] i (nat_lit 0)

@[expose] noncomputable def TLV (i : Nat) : Nat := List.getD [0, 1, 2, 3, 1, 1, 1] i (nat_lit 0)

@[expose] noncomputable def hdAt (i : Nat) : Bool :=
  tbfsHdK (nat_lit 22880) (TROOT i) (TCNT i) (TPTS i) (TPOS i) (TPAR i) (TLAB i)

@[expose] noncomputable def treeSl (i s : Nat) : Bool :=
  tbfsSlK (nat_lit 22880) (TCNT i) (lvK LJ BJ (nat_lit 28) (TLV i)).length LJ
    (lvAt LJ BJ (nat_lit 28) (TLV i)) (TPTS i) (TPOS i) (TPAR i) (TLAB i) (TTI i)
    (Nat.mul s (nat_lit 1000)) (nat_lit 1000)

@[expose] noncomputable def trSl (s : Nat) : Bool :=
  bIf(Nat.blt s (nat_lit 23), treeSl (nat_lit 0) s,
  bIf(Nat.blt s (nat_lit 32), treeSl (nat_lit 1) (Nat.sub s (nat_lit 23)),
  bIf(Nat.beq s (nat_lit 32), treeSl (nat_lit 2) (nat_lit 0),
  bIf(Nat.beq s (nat_lit 33), treeSl (nat_lit 3) (nat_lit 0),
  bIf(Nat.blt s (nat_lit 48), treeSl (nat_lit 4) (Nat.sub s (nat_lit 34)),
  bIf(Nat.beq s (nat_lit 48), treeSl (nat_lit 5) (nat_lit 0), treeSl (nat_lit 6) (nat_lit 0)))))))

@[expose] noncomputable def inTK (i p : Nat) : Bool :=
  strictB (r32 (TPOS i) p) fun q => bAnd(Nat.blt q (TCNT i), Nat.beq (r32 (TPTS i) q) p)

@[expose] noncomputable def coverK : Bool :=
  allN (nat_lit 22880) fun p => bIf(Nat.beq p (nat_lit 0), true, bIf(inTK (nat_lit 1) p, true,
    bIf(inTK (nat_lit 4) p, true, bIf(inTK (nat_lit 5) p, true, inTK (nat_lit 6) p))))

end CertificateChecks.KernelSpor.SuzK

end
