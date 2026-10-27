module

public import Certificates.Kernel.Sporadic.ONC.Data
public import Certificates.Kernel.Sporadic.ONC.Mats
public import Certificates.Kernel.Sporadic.ON2.Neg
public import Certificates.Data.Kernel.Spor.ONCK
public import Certificates.Data.Kernel.Spor.PChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONC

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC

@[expose] noncomputable def LJ (l x : Nat) : Nat := r32 LT (Nat.add (Nat.mul l (nat_lit 245520)) x)

@[expose] noncomputable def BJ (i : Nat) : Nat := List.getD [0, 2, 4] i (nat_lit 0)

@[expose] noncomputable def LLK (l j : Nat) : Nat := r32 LF (LJ l (r32 RP j))

@[expose] noncomputable def slpOK : Bool :=
  CFSG.KS.ONC.slpK CFSG.Sporadic.ON.Native.prog (nat_lit 26) (fun j => List.getD ONW.LA j (nat_lit 0))
    (fun j => List.getD ONW.LB j (nat_lit 0)) MV ML CFSG.Sporadic.ON.Native.sel.toList

@[expose] noncomputable def letSl (s : Nat) : Bool :=
  CFSG.KS.ONC.letS ML LJ (key ONW.K) (nat_lit 245520) s

@[expose] noncomputable def invSl (s : Nat) : Bool :=
  allN (nat_lit 1000) fun d => strictB (Nat.add (Nat.mul s (nat_lit 1000)) d) fun x =>
    bIf(Nat.blt x (nat_lit 245520), allN (nat_lit 4) fun j =>
      strictB (LJ (Nat.mul (nat_lit 2) j) x) fun y =>
        bAnd(Nat.blt y (nat_lit 245520), bAnd(Nat.blt (LJ (Nat.succ (Nat.mul (nat_lit 2) j)) x) (nat_lit 245520),
          Nat.beq (LJ (Nat.succ (Nat.mul (nat_lit 2) j)) y) x)), true)

@[expose] noncomputable def selT (fs : List (Nat → Nat)) (i : Nat) : Nat → Nat :=
  List.getD fs i fun _ => nat_lit 0

@[expose] noncomputable def TPTS : Nat → Nat → Nat :=
  selT [CT0.PTS, CT1.PTS, CT2.PTS, ST0.PTS, ST1.PTS, ST2.PTS, ST3.PTS, ST4.PTS]
@[expose] noncomputable def TPOS : Nat → Nat → Nat :=
  selT [CT0.POS, CT1.POS, CT2.POS, ST0.POS, ST1.POS, ST2.POS, ST3.POS, ST4.POS]
@[expose] noncomputable def TPAR : Nat → Nat → Nat :=
  selT [CT0.PAR, CT1.PAR, CT2.PAR, ST0.PAR, ST1.PAR, ST2.PAR, ST3.PAR, ST4.PAR]
@[expose] noncomputable def TLAB : Nat → Nat → Nat :=
  selT [CT0.LAB, CT1.LAB, CT2.LAB, ST0.LAB, ST1.LAB, ST2.LAB, ST3.LAB, ST4.LAB]
@[expose] noncomputable def TTI : Nat → Nat → Nat :=
  selT [CT0.TI, CT1.TI, CT2.TI, ST0.TI, ST1.TI, ST2.TI, ST3.TI, ST4.TI]

@[expose] noncomputable def TCNT (i : Nat) : Nat :=
  List.getD [CT0.cnt, CT1.cnt, CT2.cnt, ST0.cnt, ST1.cnt, ST2.cnt, ST3.cnt, ST4.cnt] i (nat_lit 0)

@[expose] noncomputable def TROOT (i : Nat) : Nat := List.getD [0, 2, 4, 0, 1, 3, 11, 28] i (nat_lit 0)

@[expose] noncomputable def TN (i : Nat) : Nat := nIf(Nat.blt i (nat_lit 3), nat_lit 245520, nat_lit 122760)

@[expose] noncomputable def TL (i : Nat) : Nat → Nat → Nat :=
  Bool.rec (motive := fun _ => Nat → Nat → Nat) LLK LJ (Nat.blt i (nat_lit 3))

@[expose] noncomputable def TLV (i : Nat) : Nat := List.getD [0, 1, 2, 1, 1, 1, 1, 1] i (nat_lit 0)

@[expose] noncomputable def hdTop (i : Nat) : Bool :=
  bAnd(Nat.blt (nat_lit 0) (TCNT i), bAnd(Nat.ble (TCNT i) (TN i), bAnd(Nat.blt (TN i) none32K,
  bAnd(Nat.beq (r32 (TPTS i) (nat_lit 0)) (TROOT i), bAnd(Nat.beq (r32 (TPAR i) (nat_lit 0)) (nat_lit 0),
    Nat.beq (r32 (TLAB i) (nat_lit 0)) (nat_lit 0))))))

@[expose] noncomputable def hdZ (i z : Nat) : Bool :=
  strictB (r32 (TPOS i) z) fun q =>
    bIf(Nat.beq q none32K, true, bAnd(Nat.blt q (TCNT i), Nat.beq (r32 (TPTS i) q) z))

@[expose] noncomputable def hdSl (i s : Nat) : Bool :=
  allN (nat_lit 1000) fun d => strictB (Nat.add (Nat.mul s (nat_lit 1000)) d) fun z =>
    bIf(Nat.blt z (TN i), hdZ i z, true)

@[expose] noncomputable def trSl (i s : Nat) : Bool :=
  tbfsSlK (TN i) (TCNT i) (lvK LJ BJ (nat_lit 8) (TLV i)).length (TL i) (lvAt LJ BJ (nat_lit 8) (TLV i))
    (TPTS i) (TPOS i) (TPAR i) (TLAB i) (TTI i) (Nat.mul s (nat_lit 1000)) (nat_lit 1000)

@[expose] noncomputable def lnSl (s : Nat) : Bool :=
  allN (nat_lit 1000) fun d => strictB (Nat.add (Nat.mul s (nat_lit 1000)) d) fun k =>
    bIf(Nat.blt k (nat_lit 245520),
      strictB (r32 LF k) fun f => strictB (tab ONW2.NEG k) fun nk =>
        bAnd(Nat.blt f (nat_lit 122760), bAnd(Nat.beq (r32 LF nk) f,
          bIf(Nat.beq (r32 RP f) k, true, Nat.beq (r32 RP f) nk))), true)

@[expose] noncomputable def rpSl (s : Nat) : Bool :=
  allN (nat_lit 1000) fun d => strictB (Nat.add (Nat.mul s (nat_lit 1000)) d) fun j =>
    bIf(Nat.blt j (nat_lit 122760),
      strictB (r32 RP j) fun k => bAnd(Nat.blt k (nat_lit 245520), bAnd(Nat.beq (r32 LF k) j,
        bAnd(Nat.blt k (tab ONW2.NEG k),
          bIf(Nat.blt (Nat.succ j) (nat_lit 122760), Nat.blt k (r32 RP (Nat.succ j)), true)))), true)

@[expose] noncomputable def inTK (i p : Nat) : Bool :=
  strictB (r32 (TPOS i) p) fun q => bAnd(Nat.blt q (TCNT i), Nat.beq (r32 (TPTS i) q) p)

@[expose] noncomputable def lbSl (s : Nat) : Bool :=
  allN (nat_lit 1000) fun d => strictB (Nat.add (Nat.mul s (nat_lit 1000)) d) fun p =>
    bIf(Nat.blt p (nat_lit 122760), strictB (r32 LB p) fun b =>
      bAnd(Nat.blt b (nat_lit 5), inTK (Nat.add (nat_lit 3) b) p), true)

@[expose] noncomputable def lbTr (i s : Nat) : Bool :=
  allN (nat_lit 1000) fun d => strictB (Nat.add (Nat.mul s (nat_lit 1000)) d) fun k =>
    bIf(Nat.blt k (TCNT (Nat.add (nat_lit 3) i)),
      Nat.beq (r32 LB (r32 (TPTS (Nat.add (nat_lit 3) i)) k)) i, true)

@[expose] noncomputable def QL : List Nat := CFSG.Sporadic.ON.Native.chainQ.toList

@[expose] noncomputable def iterK (f : Nat → Nat) (e x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ acc => strictN acc f) e

@[expose] noncomputable def fixK (f : Nat → Nat) (e : Nat) : Bool := listEqK (mapK (iterK f e) QL) QL

@[expose] noncomputable def ordQ (f : Nat → Nat) (p e : Nat) : Bool :=
  bAnd(fixK f (Nat.pow p e), Bool.rec (motive := fun _ => Bool) true false (fixK f (Nat.pow p (Nat.sub e 1))))

@[expose] noncomputable def aQ (x : Nat) : Nat := tab ONW.A x

@[expose] noncomputable def bQ (x : Nat) : Nat := tab ONW.B (tab ONW.A (tab ONW.B x))

@[expose] noncomputable def siftQ (f : Nat → Nat) : Bool :=
  siftF LJ TPOS TPAR TLAB TCNT (fun i => i) QL (nat_lit 3) (nat_lit 0) (mapK f QL)

@[expose] noncomputable def miscOK : Bool :=
  bAnd(allN (nat_lit 8) hdTop,
  bAnd(Nat.beq (TCNT 0) (nat_lit 245520), bAnd(Nat.beq (TCNT 1) (nat_lit 11172),
  bAnd(Nat.beq (TCNT 2) (nat_lit 168), bAnd(Nat.beq (TCNT 3) (nat_lit 1),
  bAnd(Nat.beq (TCNT 4) (nat_lit 5586), bAnd(Nat.beq (TCNT 5) (nat_lit 58653),
  bAnd(Nat.beq (TCNT 6) (nat_lit 52136), bAnd(Nat.beq (TCNT 7) (nat_lit 6384),
  bAnd(Nat.beq (r32 LF (nat_lit 0)) (nat_lit 0),
  bAnd(siftQ (fun x => tab ONW.A x), bAnd(siftQ (fun x => tab ONW.B x),
  bAnd(Bool.rec (motive := fun _ => Bool) true false (siftQ (fun x => tab ONW2.NEG x)),
  bAnd(ordQ aQ (nat_lit 2) (nat_lit 1), bAnd(ordQ bQ (nat_lit 19) (nat_lit 1),
    ordQ (fun x => aQ (bQ x)) (nat_lit 11) (nat_lit 1))))))))))))))))

@[expose] noncomputable def tr0 (s : Nat) : Bool := trSl (nat_lit 0) s
@[expose] noncomputable def tr1 (s : Nat) : Bool := trSl (nat_lit 1) s
@[expose] noncomputable def tr2 (s : Nat) : Bool := trSl (nat_lit 2) s
@[expose] noncomputable def tr3 (s : Nat) : Bool := trSl (nat_lit 3) s
@[expose] noncomputable def tr4 (s : Nat) : Bool := trSl (nat_lit 4) s
@[expose] noncomputable def tr5 (s : Nat) : Bool := trSl (nat_lit 5) s
@[expose] noncomputable def tr6 (s : Nat) : Bool := trSl (nat_lit 6) s
@[expose] noncomputable def tr7 (s : Nat) : Bool := trSl (nat_lit 7) s

@[expose] noncomputable def hd0 (s : Nat) : Bool := hdSl (nat_lit 0) s
@[expose] noncomputable def hd1 (s : Nat) : Bool := hdSl (nat_lit 1) s
@[expose] noncomputable def hd2 (s : Nat) : Bool := hdSl (nat_lit 2) s
@[expose] noncomputable def hd3 (s : Nat) : Bool := hdSl (nat_lit 3) s
@[expose] noncomputable def hd4 (s : Nat) : Bool := hdSl (nat_lit 4) s
@[expose] noncomputable def hd5 (s : Nat) : Bool := hdSl (nat_lit 5) s
@[expose] noncomputable def hd6 (s : Nat) : Bool := hdSl (nat_lit 6) s
@[expose] noncomputable def hd7 (s : Nat) : Bool := hdSl (nat_lit 7) s

@[expose] noncomputable def lb0 (s : Nat) : Bool := lbTr (nat_lit 0) s
@[expose] noncomputable def lb1 (s : Nat) : Bool := lbTr (nat_lit 1) s
@[expose] noncomputable def lb2 (s : Nat) : Bool := lbTr (nat_lit 2) s
@[expose] noncomputable def lb3 (s : Nat) : Bool := lbTr (nat_lit 3) s
@[expose] noncomputable def lb4 (s : Nat) : Bool := lbTr (nat_lit 4) s

end CertificateChecks.KernelSpor.ONC

end
