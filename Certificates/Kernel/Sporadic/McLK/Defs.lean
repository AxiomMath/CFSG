module

public import Certificates.Kernel.Sporadic.McLK.Data
public import CFSG.Certificates.Kernel.Spor.VOrb3

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.McLK

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.VO CFSG.KS.VO3
  CFSG.KS.F3R CFSG.KS.Row CFSG.F3.Native
open CFSG.Sporadic.McL.Native

@[expose] noncomputable def PM (i : Nat) : Nat := rg (nat_lit 64) (mask (nat_lit 64)) PT (nat_lit 0) i

@[expose] noncomputable def ATM : Array V := transposeK 21 (rowsOfL 21 McLSeedA.chars)
@[expose] noncomputable def BTM : Array V := transposeK 21 (rowsOfL 21 McLSeedB.chars)

@[expose] noncomputable def LJ (l x : Nat) : Nat := r32 LT (Nat.add (Nat.mul l (nat_lit 275)) x)

@[expose] noncomputable def BJ (i : Nat) : Nat := i

@[expose] noncomputable def GJ (z : Int) (x : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => nIf(Nat.beq k (nat_lit 1), r32 AL x, nIf(Nat.beq k (nat_lit 2), r32 BE x, r32 BI x)))
    (fun k => nIf(Nat.beq k (nat_lit 0), r32 AL x, r32 BI x)) z

@[expose] noncomputable def lvSel (fs : List (Nat → Nat)) (i : Nat) : Nat → Nat :=
  List.getD fs i fun _ => nat_lit 0
@[expose] noncomputable def PTSJ : Nat → Nat → Nat :=
  lvSel [CT0.PTS, CT1.PTS, CT2.PTS, CT3.PTS, CT4.PTS, CT5.PTS]
@[expose] noncomputable def POSJ : Nat → Nat → Nat :=
  lvSel [CT0.POS, CT1.POS, CT2.POS, CT3.POS, CT4.POS, CT5.POS]
@[expose] noncomputable def PARJ : Nat → Nat → Nat :=
  lvSel [CT0.PAR, CT1.PAR, CT2.PAR, CT3.PAR, CT4.PAR, CT5.PAR]
@[expose] noncomputable def LABJ : Nat → Nat → Nat :=
  lvSel [CT0.LAB, CT1.LAB, CT2.LAB, CT3.LAB, CT4.LAB, CT5.LAB]
@[expose] noncomputable def TIJ : Nat → Nat → Nat :=
  lvSel [CT0.TI, CT1.TI, CT2.TI, CT3.TI, CT4.TI, CT5.TI]
@[expose] noncomputable def CNTJ (i : Nat) : Nat :=
  List.getD [CT0.cnt, CT1.cnt, CT2.cnt, CT3.cnt, CT4.cnt, CT5.cnt] i (nat_lit 0)

@[expose] noncomputable def QL : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 26]

@[expose] noncomputable def QB (i : Nat) : Nat := i

@[expose] noncomputable def orbHd : Bool := v3HdK 21 275 400 rootVec PM AL BE PA LA

@[expose] noncomputable def orbPt : Bool := allN (nat_lit 275) (v3PtK 21 275 ATM BTM PM AL BE)

@[expose] noncomputable def orbSort : Bool := allN (nat_lit 275) (vorbSortK (nat_lit 275) PM SO)

@[expose] noncomputable def invAB : Bool :=
  allN (nat_lit 275) fun x => bAnd(Nat.blt (r32 AL x) (nat_lit 275),
    bAnd(Nat.beq (r32 AL (r32 AL x)) x, bAnd(Nat.blt (r32 BE x) (nat_lit 275),
    bAnd(Nat.beq (r32 BI (r32 BE x)) x, Nat.blt (r32 BI x) (nat_lit 275)))))

@[expose] noncomputable def codeZ (z : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun k => Nat.mul (nat_lit 2) k)
    (fun k => Nat.succ (Nat.mul (nat_lit 2) k)) z

@[expose] noncomputable def decZ (c : Nat) : Int :=
  Bool.rec (motive := fun _ => Int) (Int.negSucc (Nat.div c (nat_lit 2)))
    (Int.ofNat (Nat.div c (nat_lit 2))) (Nat.beq (Nat.mod c (nat_lit 2)) (nat_lit 0))

@[expose] noncomputable def GC (c x : Nat) : Nat := GJ (decZ c) x

@[expose] noncomputable def WL (j : Nat) : List Nat := List.getD [W0, W1, W2, W3, W4, W5, W6, W7, W8] j []

@[expose] noncomputable def wordsSl (s : Nat) : Bool :=
  strictB (Nat.div s (nat_lit 11)) fun j => strictB (Nat.mul (Nat.mod s (nat_lit 11)) (nat_lit 25))
    fun lo => allN (nat_lit 25) fun d => strictB (Nat.add lo d) fun x =>
      bIf(Nat.blt x (nat_lit 275),
        Nat.beq (LJ (Nat.mul (nat_lit 2) j) x) (List.foldr GC x (WL j)), true)

@[expose] noncomputable def invL : Bool := invK LJ (nat_lit 275) (nat_lit 18)

@[expose] noncomputable def tree (i : Nat) : Bool :=
  bAnd(tbfsHdK (nat_lit 275) (BJ i) (CNTJ i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i),
    allN (CNTJ i) (tbfsPtK (nat_lit 275) (CNTJ i) (lvK LJ BJ (nat_lit 18) i).length LJ
      (lvAt LJ BJ (nat_lit 18) i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i) (TIJ i)))

@[expose] noncomputable def sch0 (s : Nat) : Bool :=
  schSlK LJ BJ (nat_lit 18) PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 6) (nat_lit 0)
    (Nat.mul s (nat_lit 55)) (nat_lit 55)

@[expose] noncomputable def schR (i : Nat) : Bool :=
  schSlK LJ BJ (nat_lit 18) PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 6) i (nat_lit 0) (CNTJ i)

@[expose] noncomputable def term : Bool := termK LJ BJ (nat_lit 18) (nat_lit 6) QL

@[expose] noncomputable def t2 : Bool :=
  bAnd(tbfsHdK (nat_lit 275) (nat_lit 2) T2.cnt T2.PTS T2.POS T2.PAR T2.LAB,
    allN T2.cnt (tbfsPtK (nat_lit 275) T2.cnt (lvK LJ BJ (nat_lit 18) (nat_lit 1)).length LJ
      (lvAt LJ BJ (nat_lit 18) (nat_lit 1)) T2.PTS T2.POS T2.PAR T2.LAB T2.TI))

@[expose] noncomputable def cover : Bool :=
  allN (nat_lit 275) fun p => bIf(Nat.beq p (nat_lit 0), true,
    bIf(bAnd(Nat.blt (r32 CT1.POS p) CT1.cnt, Nat.beq (r32 CT1.PTS (r32 CT1.POS p)) p), true,
      bAnd(Nat.blt (r32 T2.POS p) (nat_lit 112), Nat.beq (r32 T2.PTS (r32 T2.POS p)) p)))

end CertificateChecks.KernelSpor.McLK

end
