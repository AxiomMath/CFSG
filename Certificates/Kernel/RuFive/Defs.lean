module

public import Certificates.Kernel.RuFive.Data
public import Certificates.Kernel.Misc.RuFive.Q8
public import Certificates.Data.Kernel.HeLoc.Tree

public section

namespace CertificateChecks.KernelRuFive

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.KC.HeLoc

@[expose] noncomputable def F (k : Nat) : Nat := CertificateChecks.KernelMisc.RuFive.RG.F k

@[expose] noncomputable def AI (k : Nat) : Nat := AIF k

@[expose] noncomputable def pa (k x : Nat) : Nat := pg 12 (mask 12) (F k) x

@[expose] noncomputable def pi (k x : Nat) : Nat := pg 12 (mask 12) (AI k) x

@[expose] def wdec (c : Nat) : Int :=
  if c % 2 = 0 then ((c / 2 + 1 : Nat) : Int) else -((c / 2 + 1 : Nat) : Int)

@[expose] def runAt : Nat → List Nat → List Nat
  | _, [] => []
  | 0, len :: rest => rest.take len
  | k + 1, len :: rest => runAt k (rest.drop len)

@[expose] noncomputable def wd (k : Nat) : List Int := (runAt k WF).map wdec

@[expose] def bs : List Nat := CFSG.RankThree.PartOne.ruFiveKeys

@[expose] def q0 (_ : Nat) : Nat := 0

@[expose] noncomputable def gQ (k x : Nat) : Nat := pa k x

@[expose] noncomputable def gC (k x : Nat) : Nat := pa (Nat.add 64 k) x

@[expose] noncomputable def gC1 (k x : Nat) : Nat := pa (Nat.add 67 k) x

@[expose] noncomputable def gA (k x : Nat) : Nat := pa (Nat.add 70 k) x

@[expose] noncomputable def gD (l x : Nat) : Nat :=
  nIf(Nat.beq l 0, pa 68 (pa 69 (pi 68 (pi 69 x))), pa 69 x)

@[expose] noncomputable def QE (i k : Nat) : Nat := fld(Q.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def CE (i k : Nat) : Nat := fld(C0.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def CE1 (i k : Nat) : Nat := fld(C1.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def AE (i k : Nat) : Nat := fld(A0.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def DE (i k : Nat) : Nat := fld(D0.ER i, Nat.mul 16 k, 65535)

@[expose] noncomputable def qv (i x : Nat) : Nat := trV gQ Q.P Q.L 125 i x

@[expose] noncomputable def cv (i x : Nat) : Nat := trV gC C0.P C0.L 1000 i x

@[expose] noncomputable def cv1 (i x : Nat) : Nat := trV gC1 C1.P C1.L 300 i x

@[expose] noncomputable def av (i x : Nat) : Nat := trV gA A0.P A0.L 125 i x

@[expose] noncomputable def dv (i x : Nat) : Nat := trV gD D0.P D0.L 60 i x

@[expose] noncomputable def qkey (i : Nat) : Nat := keyV 4060 CFSG.RankThree.PartOne.ruFiveKeys (qv i)

@[expose] noncomputable def ckey (i : Nat) : Nat := keyV 4060 CFSG.RankThree.PartOne.ruFiveKeys (cv i)

@[expose] noncomputable def ckey1 (i : Nat) : Nat :=
  keyV 4060 CFSG.RankThree.PartOne.ruFiveKeys (cv1 i)

@[expose] noncomputable def akey (i : Nat) : Nat := keyV 4060 CFSG.RankThree.PartOne.ruFiveKeys (av i)

@[expose] noncomputable def dkey (i : Nat) : Nat := keyV 4060 CFSG.RankThree.PartOne.ruFiveKeys (dv i)

@[expose] noncomputable def ln (j x : Nat) : Nat := pa (Nat.add 2 j) x

@[expose] noncomputable def coverAt (k : Nat) : Bool :=
  strictB (QW.getD k 0) fun w => bIf(Nat.beq w 0, eqOnL bs (qv k) (fun x => x),
    bAnd(Nat.blt (Nat.div w 8) 31, bAnd(Nat.blt 0 (Nat.mod w 8), bAnd(Nat.blt (Nat.mod w 8) 5,
      eqOnL bs (qv k) (powF (ln (Nat.div w 8)) (Nat.mod w 8))))))

@[expose] noncomputable def distAt (j j' : Nat) : Bool :=
  bIf(Nat.beq j j', true, allN 5 fun e => !eqOnL bs (ln j) (powF (ln j') e))

@[expose] noncomputable def lineAt (j : Nat) : Bool :=
  bAnd(eqOnL bs (powF (ln j) 5) (fun x => x), bAnd(!eqOnL bs (ln j) (fun x => x),
    bAnd(Nat.blt (LQ.getD j 0) 125, eqOnL bs (qv (LQ.getD j 0)) (ln j))))

@[expose] noncomputable def transAt (j : Nat) : Bool :=
  eqOnL bs (fun y => pa (Nat.add 33 j) (ln (CFSG.RankThree.PartOne.ruFiveRec.getD j 0)
    (pi (Nat.add 33 j) y))) (ln j)

@[expose] noncomputable def x0 (y : Nat) : Nat := pa 2 y

@[expose] noncomputable def x1 (y : Nat) : Nat := pa 3 y

@[expose] noncomputable def relAt0 (r : Nat × Nat × Nat) : Bool :=
  bAnd(Nat.blt r.2.2 5, bAnd(Nat.blt r.1 9, bAnd(Nat.blt r.2.1 9,
    Nat.beq (powF x0 r.2.2 (CFSG.RankThree.PartOne.ruCase0BaseArr[r.1]!))
      (CFSG.RankThree.PartOne.ruCase0BaseArr[r.2.1]!))))

@[expose] noncomputable def relAt1 (r : Nat × Nat × Nat) : Bool :=
  bAnd(Nat.blt r.2.2 5, bAnd(Nat.blt r.1 5, bAnd(Nat.blt r.2.1 5,
    Nat.beq (powF x1 r.2.2 (CFSG.RankThree.PartOne.ruCase1BaseArr[r.1]!))
      (CFSG.RankThree.PartOne.ruCase1BaseArr[r.2.1]!))))

@[expose] noncomputable def fr0 (i : Nat) : Nat := FR0.getD i 0

@[expose] noncomputable def fr1 (i : Nat) : Nat := FR1.getD i 0

@[expose] noncomputable def zAt0 (c : Nat) : Bool :=
  strictB (ZW0.getD c 0) fun w => bIf(Nat.blt w 100,
    bAnd(Nat.blt 0 w, bAnd(Nat.blt w 4,
      !eqOnL bs (fun y => cv c (gA (Nat.sub w 1) y)) (fun y => gA (Nat.sub w 1) (cv c y)))),
    bAnd(Nat.blt (Nat.sub w 100) 5, eqOnL bs (cv c) (powF x0 (Nat.sub w 100))))

@[expose] noncomputable def zAt1 (c : Nat) : Bool :=
  strictB (ZW1.getD c 0) fun w => bIf(Nat.blt w 100,
    bAnd(Nat.blt 0 w, bAnd(Nat.blt w 3,
      !eqOnL bs (fun y => cv1 c (gD (Nat.sub w 1) y)) (fun y => gD (Nat.sub w 1) (cv1 c y)))),
    bAnd(Nat.blt (Nat.sub w 100) 5, eqOnL bs (cv1 c) (powF x1 (Nat.sub w 100))))

@[expose] noncomputable def mt (a b : Nat) : Nat := fld(MT a, Nat.mul 8 b, 255)

@[expose] noncomputable def iv (a : Nat) : Nat := fld(IV 0, Nat.mul 8 a, 255)

@[expose] noncomputable def cj (j r : Nat) : Nat := mt (mt j r) (iv j)

@[expose] noncomputable def btP (t i : Nat) : Nat := fld(BT t, Nat.mul 20 i, 255)

@[expose] noncomputable def btL (t i : Nat) : Nat := fld(BT t, Nat.add (Nat.mul 20 i) 8, 255)

@[expose] noncomputable def btD (t i : Nat) : Nat := fld(BT t, Nat.add (Nat.mul 20 i) 16, 15)

@[expose] noncomputable def mtB (a : Nat) : Bool :=
  allN 60 fun b => bAnd(Nat.blt (mt a b) 60, eqOnL bs (dv (mt a b)) (fun y => dv a (dv b y)))

@[expose] noncomputable def btB (t : Nat) : Bool :=
  bIf(Nat.beq t 0, true, allN 60 fun i => bIf(Nat.beq i 0, true,
    bAnd(Nat.blt (btP t i) 60, bAnd(Nat.blt (btL t i) 60,
      bAnd(Nat.beq (btD t i) (Nat.succ (btD t (btP t i))),
        Nat.beq i (mt (cj (btL t i) t) (btP t i)))))))

end CertificateChecks.KernelRuFive

end
