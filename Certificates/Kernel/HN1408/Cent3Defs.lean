module

public import Certificates.Kernel.HN1408.Cent3Data
public import Certificates.Kernel.HN1408.Words
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.FixData

public section

namespace CFSG.KD.HN1408.Cent3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.EvenSporadicStandard.HNRecog

@[expose] noncomputable def fd (W i : Nat) : Nat := Nat.land (Nat.shiftRight W (Nat.mul 16 i)) 65535

@[expose] noncomputable def ev (k p : Nat) : Nat := pt (T0 (Nat.div k 36)) (pt (T1 (Nat.mod k 36)) p)

@[expose] noncomputable def elK (k : Nat) : Nat := pc (T0 (Nat.div k 36)) (T1 (Nat.mod k 36))

@[expose] noncomputable def base2 (f : Nat → Bool) : Bool := bAnd(f 0, f 1)

@[expose] noncomputable def mulEq (g h u : Nat) : Bool :=
  base2 fun p => Nat.beq (ev g (ev h p)) (ev u p)

@[expose] noncomputable def invK (k : Nat) : Bool :=
  bAnd(bIf(Nat.beq k 0, false, true), base2 fun p => Nat.beq (ev k (ev k p)) p)

@[expose] noncomputable def headK (G T0 T1 : Nat → Nat) : Bool :=
  bAnd(allN 4 (fun l => Nat.beq (G l) (WK (fix3.cent.getD l []))),
    bAnd(Nat.beq (T0 0) idK, Nat.beq (T1 0) idK))

@[expose] noncomputable def keysK (T0 : Nat → Nat) : Bool :=
  allN 39 fun i => Nat.blt (pt (T0 i) 0) (pt (T0 (Nat.succ i)) 0)

@[expose] noncomputable def treeK (G T0 P0 : Nat → Nat) (i : Nat) : Bool :=
  bIf(Nat.beq i 0, true,
    strictB (P0 i) fun w => strictB (fd w 0) fun p => strictB (fd w 1) fun l =>
      bAnd(Nat.blt p 40, bAnd(Nat.blt l 4, bAnd(Nat.beq (fd w 2) (Nat.succ (fd (P0 p) 2)),
        Nat.beq (T0 i) (pc (G l) (T0 p))))))

@[expose] noncomputable def schK (G T0 S SR : Nat → Nat) (r : Nat) : Bool :=
  strictB (S r) fun X => strictB (SR r) fun w =>
    strictB (fd w 0) fun p => strictB (fd w 1) fun q => strictB (fd w 2) fun l =>
      bAnd(canonK 1408 11 (mask 11) (1408 * 11) X, bAnd(Nat.blt p 40, bAnd(Nat.blt q 40,
        bAnd(Nat.blt l 4, Nat.beq (pc (T0 q) X) (pc (G l) (T0 p))))))

@[expose] noncomputable def t1K (S T1 P1 : Nat → Nat) (j : Nat) : Bool :=
  strictB (T1 j) fun X => strictB (pt X 1) fun y =>
    bAnd(Nat.beq (pt X 0) 0,
      bAnd(allN j (fun j' => bIf(Nat.beq y (pt (T1 j') 1), false, true)),
        bIf(Nat.beq j 0, true,
          strictB (P1 j) fun w => strictB (fd w 0) fun p => strictB (fd w 1) fun r =>
            bAnd(Nat.blt p j, bAnd(Nat.blt r 3, Nat.beq X (pc (S r) (T1 p)))))))

@[expose] noncomputable def rowK (R RK : Nat → Nat) (k : Nat) : Bool :=
  strictB (R k) fun v =>
    bIf(Nat.beq v 0, bIf(invK k, false, true),
      strictB (Nat.mod (Nat.sub v 1) 8) fun c => strictB (Nat.div (Nat.sub v 1) 8) fun c' =>
        bAnd(invK k, bAnd(Nat.blt c 6, bAnd(Nat.blt c' 1440,
          base2 fun p => Nat.beq (ev c' (ev (RK c) p)) (ev k (ev c' p))))))

@[expose] noncomputable def tgtK (t : Nat) : Nat :=
  nIf(Nat.beq t 0, WK wordA, nIf(Nat.beq t 1, WK wordZ, nIf(Nat.beq t 2, pc (WK wordA) (WK wordZ),
    nIf(Nat.beq t 3, WK wordB, WK wordZ₁))))

@[expose] noncomputable def repK (RK RT : Nat → Nat) (RW : List (List Nat)) (c : Nat) : Bool :=
  strictB (RK c) fun k => strictB (RT c) fun t =>
    bAnd(Nat.blt k 1440, bAnd(Nat.blt t 5, bAnd(lettersOK (RW.getD c []),
      Nat.beq (pc (WK (RW.getD c [])) (tgtK t)) (pc (elK k) (WK (RW.getD c []))))))

@[expose] noncomputable def ttK (RT : Nat → Nat) (v : Nat) : Nat :=
  nIf(Nat.beq v 0, 0, CFSG.KC.Loop.strictN (RT (Nat.mod (Nat.sub v 1) 8)) fun t =>
    nIf(Nat.beq t 0, 1, nIf(Nat.beq t 2, 1, nIf(Nat.beq t 4, 1, 0))))

@[expose] noncomputable def cntN (R RT : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => CFSG.KC.Loop.strictN acc fun a => Nat.add a (ttK RT (R k))) n

@[expose] noncomputable def cntK (R RT : Nat → Nat) : Bool := Nat.beq (cntN R RT 1440) 46

@[expose] noncomputable def xK (X : Nat → Nat) : Bool :=
  strictB (X 0) fun x => strictB (X 1) fun x2 =>
    bAnd(Nat.blt x 1440, bAnd(Nat.blt x2 1440, bAnd(
      strictB (WK fix3.rep) (fun Y => base2 fun p => Nat.beq (pt Y p) (ev x p)),
      bAnd(mulEq x x x2, base2 fun p => Nat.beq (ev x (ev x2 p)) p))))

@[expose] noncomputable def evPow (g n p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ q => ev g q) n

@[expose] noncomputable def pairK (n g h u : Nat) : Bool :=
  bAnd(Nat.blt g 1440, bAnd(Nat.blt h 1440, bAnd(Nat.blt u 1440,
    bAnd(bIf(Nat.beq g 0, false, true), bAnd(bIf(Nat.beq h 0, false, true),
      bAnd(base2 (fun p => Nat.beq (evPow g n p) p), bAnd(base2 (fun p => Nat.beq (evPow h n p) p),
        invK u)))))))

@[expose] noncomputable def p5K (P5 : Nat → Nat) : Bool :=
  bAnd(pairK 5 (P5 0) (P5 1) (P5 2), mulEq (P5 0) (P5 1) (P5 2))

@[expose] noncomputable def p3K (P3 : Nat → Nat) : Bool :=
  bAnd(pairK 3 (P3 0) (P3 1) (P3 2),
    base2 fun p => Nat.beq (ev (P3 0) (ev (P3 1) (ev (P3 0) (ev (P3 1) (ev (P3 0) (ev (P3 1) p))))))
      (ev (P3 2) p))

@[expose] noncomputable def mGenK (MG : Nat → Nat) : Bool := allN 2 fun l => Nat.blt (MG l) 1440

@[expose] noncomputable def mElK (E X : Nat → Nat) (n : Nat) : Bool :=
  strictB (E n) fun e =>
    bAnd(Nat.blt e 1440, bAnd(bIf(Nat.beq n 0, Nat.beq e 0, true),
      bAnd(allN n (fun n' => bIf(Nat.beq e (E n'), false, true)),
        bAnd(bIf(Nat.beq e (X 0), false, true), bIf(Nat.beq e (X 1), false, true)))))

@[expose] noncomputable def mTreeK (E EP MG : Nat → Nat) (n : Nat) : Bool :=
  bIf(Nat.beq n 0, true,
    strictB (EP n) fun w => strictB (fd w 0) fun p => strictB (fd w 1) fun l =>
      bAnd(Nat.blt p n, bAnd(Nat.blt l 2, mulEq (MG l) (E p) (E n))))

@[expose] noncomputable def mClK (E ECl MG : Nat → Nat) (n : Nat) : Bool :=
  strictB (ECl n) fun w => allN 2 fun l => strictB (fd w l) fun n' =>
    bAnd(Nat.blt n' 60, mulEq (MG l) (E n) (E n'))

@[expose] noncomputable def mCommK (E MC MG : Nat → Nat) (l : Nat) : Bool :=
  strictB (MC l) fun w => strictB (fd w 0) fun a => strictB (fd w 1) fun b =>
    bAnd(Nat.blt a 60, bAnd(Nat.blt b 60,
      base2 fun p => Nat.beq (ev (E a) (ev (E b) p)) (ev (MG l) (ev (E b) (ev (E a) p)))))

@[expose] noncomputable def wcK (R RT WC : Nat → Nat) : Bool :=
  bAnd(allN 5 (fun i => Nat.blt (WC i) 1440),
    bAnd(Nat.beq (ttK RT (R (WC 0))) 1, bAnd(Nat.beq (ttK RT (R (WC 1))) 1,
      bAnd(Nat.beq (ttK RT (R (WC 3))) 1, bAnd(Nat.beq (ttK RT (R (WC 4))) 1,
        bAnd(mulEq (WC 0) (WC 1) (WC 2),
          base2 fun p => Nat.beq (ev (WC 2) (ev (WC 3) p))
            (ev (WC 4) (ev (WC 3) (ev (WC 2) p)))))))))

end CFSG.KD.HN1408.Cent3

end
