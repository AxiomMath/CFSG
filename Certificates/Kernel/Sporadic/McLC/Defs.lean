module

public import Certificates.Kernel.Sporadic.McLC.Data
public import Certificates.Kernel.Sporadic.McLK.Data
public import Certificates.Data.Kernel.Spor.PChain

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLC

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC

@[expose] noncomputable def NL : Nat := 10

@[expose] noncomputable def LJ (l x : Nat) : Nat := r32 LT (Nat.add (Nat.mul l (nat_lit 275)) x)

@[expose] noncomputable def BJ (i : Nat) : Nat := List.getD [0, 14, 2] i (nat_lit 0)

@[expose] noncomputable def lvSel (fs : List (Nat → Nat)) (i : Nat) : Nat → Nat :=
  List.getD fs i fun _ => nat_lit 0
@[expose] noncomputable def PTSJ : Nat → Nat → Nat := lvSel [CT0.PTS, CT1.PTS, CT2.PTS]
@[expose] noncomputable def POSJ : Nat → Nat → Nat := lvSel [CT0.POS, CT1.POS, CT2.POS]
@[expose] noncomputable def PARJ : Nat → Nat → Nat := lvSel [CT0.PAR, CT1.PAR, CT2.PAR]
@[expose] noncomputable def LABJ : Nat → Nat → Nat := lvSel [CT0.LAB, CT1.LAB, CT2.LAB]
@[expose] noncomputable def TIJ : Nat → Nat → Nat := lvSel [CT0.TI, CT1.TI, CT2.TI]
@[expose] noncomputable def CNTJ (i : Nat) : Nat := List.getD [CT0.cnt, CT1.cnt, CT2.cnt] i (nat_lit 0)

@[expose] noncomputable def QL : List Nat := List.range 275

@[expose] noncomputable def QB (i : Nat) : Nat := BJ i

@[expose] noncomputable def pk (P x : Nat) : Nat := pg (nat_lit 9) (nat_lit 511) P x

@[expose] noncomputable def TT : Nat → Nat → Nat := lvSel [T0, T1, T2]
@[expose] noncomputable def TTI : Nat → Nat → Nat := lvSel [T0I, T1I, T2I]

@[expose] noncomputable def GA (l y : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 1), r32 McLK.AL y, r32 McLK.BE y)

@[expose] noncomputable def kOK : Bool :=
  allN (nat_lit 275) fun x =>
    bAnd(Nat.beq (LJ (nat_lit 0) x)
      (List.foldr GA x (List.getD CFSG.ClassicalInvolution.McLData.kWords (nat_lit 0) [])),
      Nat.beq (LJ (nat_lit 2) x)
        (List.foldr GA x (List.getD CFSG.ClassicalInvolution.McLData.kWords (nat_lit 1) [])))

@[expose] noncomputable def wordL (j : Nat) : List Nat :=
  List.map (fun i => WC (Nat.add (WS j) i)) (List.range (WN j))

@[expose] noncomputable def wordOK (j : Nat) : Bool :=
  bAnd(List.all (wordL j) (fun c => Nat.blt c (nat_lit 4)),
    allN (nat_lit 275) fun x => Nat.beq (LJ (Nat.mul (nat_lit 2) j) x) (List.foldr LJ x (wordL j)))

@[expose] noncomputable def invL : Bool := invK LJ (nat_lit 275) NL

@[expose] noncomputable def tree (i : Nat) : Bool :=
  bAnd(tbfsHdK (nat_lit 275) (BJ i) (CNTJ i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i),
    allN (CNTJ i) (tbfsPtK (nat_lit 275) (CNTJ i) (lvK LJ BJ NL i).length LJ
      (lvAt LJ BJ NL i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i) (TIJ i)))

@[expose] noncomputable def sch0 (s : Nat) : Bool :=
  schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (Nat.mul s (nat_lit 48)) (nat_lit 48)

@[expose] noncomputable def schR (i : Nat) : Bool :=
  schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) i (nat_lit 0) (CNTJ i)

@[expose] noncomputable def term : Bool := termK LJ BJ NL (nat_lit 3) QL

@[expose] noncomputable def trOK (i k : Nat) : Bool :=
  strictB (TT i k) fun P => strictB (TTI i k) fun PI =>
    bAnd(listEqK (walkK LJ (PARJ i) (LABJ i) k QL) (List.map (pk P) QL),
      allN (nat_lit 275) fun x => Nat.beq (pk PI (pk P x)) x)

@[expose] noncomputable def trAll : Bool := allN (nat_lit 3) fun i => allN (CNTJ i) (trOK i)

@[expose] noncomputable def GK (l y : Nat) : Nat := nIf(Nat.beq l (nat_lit 1), LJ (nat_lit 0) y, LJ (nat_lit 2) y)

@[expose] noncomputable def repOK : Bool :=
  allN (nat_lit 21) fun j => strictB (RP j) fun P => allN (nat_lit 275) fun x =>
    Nat.beq (pk P x) (List.foldr GK x (List.getD CFSG.ClassicalInvolution.McLData.repData j ([], [])).1)

@[expose] noncomputable def prod3 (A B C y : Nat) : Nat := pk A (pk B (pk C y))

@[expose] noncomputable def coverW (t w : Nat) : Bool :=
  strictB (Nat.land w (nat_lit 31)) fun j =>
  strictB (Nat.land (Nat.shiftRight w (nat_lit 5)) (nat_lit 255)) fun c0 =>
  strictB (Nat.land (Nat.shiftRight w (nat_lit 13)) (nat_lit 63)) fun c1 =>
  strictB (Nat.land (Nat.shiftRight w (nat_lit 19)) (nat_lit 3)) fun c2 =>
  strictB (T0 (Nat.div t (nat_lit 168))) fun X0 =>
  strictB (T1 (Nat.mod (Nat.div t (nat_lit 3)) (nat_lit 56))) fun X1 =>
  strictB (T2 (Nat.mod t (nat_lit 3))) fun X2 =>
  bIf(Nat.beq j (nat_lit 21),
    bAnd(Nat.beq (prod3 X0 X1 X2 (nat_lit 0)) (nat_lit 0),
      bAnd(Nat.beq (prod3 X0 X1 X2 (nat_lit 14)) (nat_lit 14),
        Nat.beq (prod3 X0 X1 X2 (nat_lit 2)) (nat_lit 2))),
  bIf(Nat.beq j (nat_lit 22),
    bAnd(Nat.beq (prod3 X0 X1 X2 (nat_lit 0)) (r32 McLK.AL (nat_lit 0)),
      bAnd(Nat.beq (prod3 X0 X1 X2 (nat_lit 14)) (r32 McLK.AL (nat_lit 14)),
        Nat.beq (prod3 X0 X1 X2 (nat_lit 2)) (r32 McLK.AL (nat_lit 2)))),
  bAnd(Nat.blt j (nat_lit 21), bAnd(Nat.blt c0 (nat_lit 240), bAnd(Nat.blt c1 (nat_lit 56),
    bAnd(Nat.blt c2 (nat_lit 3),
  strictB (RP j) fun R =>
  strictB (T2I c2) fun I2 => strictB (T1I c1) fun I1 => strictB (T0I c0) fun I0 =>
    bAnd(Nat.beq (prod3 I2 I1 I0 (prod3 X0 X1 X2 (nat_lit 0))) (pk R (prod3 I2 I1 I0 (nat_lit 0))),
      bAnd(Nat.beq (prod3 I2 I1 I0 (prod3 X0 X1 X2 (nat_lit 14)))
          (pk R (prod3 I2 I1 I0 (nat_lit 14))),
        Nat.beq (prod3 I2 I1 I0 (prod3 X0 X1 X2 (nat_lit 2))) (pk R (prod3 I2 I1 I0 (nat_lit 2)))))))))))

@[expose] noncomputable def coverSl (s : Nat) : Bool :=
  allN (nat_lit 2016) fun d => strictB (Nat.add (Nat.mul s (nat_lit 2016)) d) fun t =>
    coverW t (r32 WT t)

end CertificateChecks.KernelSpor.McLC

end
