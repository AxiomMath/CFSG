module

public import Certificates.Kernel.Sporadic.J2K.Data
public import Certificates.Data.Kernel.Spor.VOrb
public import Certificates.Data.Kernel.Spor.PrimK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.VO CFSG.KS.PR CFSG.KS.Row
open CFSG.Sporadic.J2.Native
open CFSG.Sporadic.J1.Native (sgnKey mvL)

@[expose] noncomputable def PJ2 (i : Nat) : Nat := rg (nat_lit 64) (mask (nat_lit 64)) PT (nat_lit 0) i

@[expose] noncomputable def LJ (l x : Nat) : Nat := r32 LT (Nat.add (Nat.mul l (nat_lit 315)) x)

@[expose] noncomputable def BJ (i : Nat) : Nat :=
  nIf(Nat.beq i (nat_lit 0), nat_lit 0, nIf(Nat.beq i (nat_lit 1), nat_lit 4, nat_lit 3))

@[expose] noncomputable def GJ (z : Int) (x : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => nIf(Nat.beq k (nat_lit 1), r32 AL x, nIf(Nat.beq k (nat_lit 2), r32 BE x, r32 BI x)))
    (fun k => nIf(Nat.beq k (nat_lit 0), r32 AI x, r32 BI x)) z

@[expose] noncomputable def lvSel (fs : List (Nat → Nat)) (i : Nat) : Nat → Nat :=
  List.getD fs i fun _ => nat_lit 0
@[expose] noncomputable def PTSJ : Nat → Nat → Nat := lvSel [CT0.PTS, CT1.PTS, CT2.PTS]
@[expose] noncomputable def POSJ : Nat → Nat → Nat := lvSel [CT0.POS, CT1.POS, CT2.POS]
@[expose] noncomputable def PARJ : Nat → Nat → Nat := lvSel [CT0.PAR, CT1.PAR, CT2.PAR]
@[expose] noncomputable def LABJ : Nat → Nat → Nat := lvSel [CT0.LAB, CT1.LAB, CT2.LAB]
@[expose] noncomputable def TIJ : Nat → Nat → Nat := lvSel [CT0.TI, CT1.TI, CT2.TI]
@[expose] noncomputable def CNTJ (i : Nat) : Nat := List.getD [CT0.cnt, CT1.cnt, CT2.cnt] i (nat_lit 0)

@[expose] noncomputable def QL : List Nat := [0, 4, 3, 1, 2, 6, 7, 8, 10, 11, 12, 13, 15, 17]

@[expose] noncomputable def QB (i : Nat) : Nat := i

@[expose] noncomputable def SPTSJ : Nat → Nat → Nat :=
  lvSel [SB0.PTS, SB1.PTS, SB2.PTS, SB3.PTS, SB4.PTS, SB5.PTS]
@[expose] noncomputable def SPOSJ : Nat → Nat → Nat :=
  lvSel [SB0.POS, SB1.POS, SB2.POS, SB3.POS, SB4.POS, SB5.POS]
@[expose] noncomputable def SPARJ : Nat → Nat → Nat :=
  lvSel [SB0.PAR, SB1.PAR, SB2.PAR, SB3.PAR, SB4.PAR, SB5.PAR]
@[expose] noncomputable def SLABJ : Nat → Nat → Nat :=
  lvSel [SB0.LAB, SB1.LAB, SB2.LAB, SB3.LAB, SB4.LAB, SB5.LAB]
@[expose] noncomputable def STIJ : Nat → Nat → Nat :=
  lvSel [SB0.TI, SB1.TI, SB2.TI, SB3.TI, SB4.TI, SB5.TI]
@[expose] noncomputable def SCNTJ (l : Nat) : Nat :=
  List.getD [SB0.cnt, SB1.cnt, SB2.cnt, SB3.cnt, SB4.cnt, SB5.cnt] l (nat_lit 0)

@[expose] noncomputable def orbHd : Bool :=
  vorbHdK (nat_lit 5) (nat_lit 14) (nat_lit 315) (nat_lit 400) (mA ()) (mB ()) (root ()) PJ2 AL BE PA LA

@[expose] noncomputable def orbPt : Bool :=
  allN (nat_lit 315) (vorbPtK (nat_lit 5) (nat_lit 14) (nat_lit 315) id (mA ()) (mB ()) PJ2 AL BE)

@[expose] noncomputable def orbSort : Bool := allN (nat_lit 315) (vorbSortK (nat_lit 315) PJ2 SO)

@[expose] noncomputable def invAB : Bool :=
  allN (nat_lit 315) fun x => bAnd(Nat.blt (r32 AL x) (nat_lit 315),
    bAnd(Nat.beq (r32 AI (r32 AL x)) x, bAnd(Nat.blt (r32 BE x) (nat_lit 315),
    bAnd(Nat.beq (r32 BI (r32 BE x)) x, bAnd(Nat.blt (r32 AI x) (nat_lit 315),
      Nat.blt (r32 BI x) (nat_lit 315))))))

@[expose] noncomputable def wordsOK : Bool :=
  allN (nat_lit 8) fun j => allN (nat_lit 315) fun x =>
    Nat.beq (LJ (Nat.mul (nat_lit 2) j) x) (List.foldr GJ x (chainWords ())[j]!)

@[expose] noncomputable def invL : Bool := invK LJ (nat_lit 315) (nat_lit 16)

@[expose] noncomputable def tree (i : Nat) : Bool :=
  bAnd(tbfsHdK (nat_lit 315) (BJ i) (CNTJ i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i),
    allN (CNTJ i) (tbfsPtK (nat_lit 315) (CNTJ i) (lvK LJ BJ (nat_lit 16) i).length LJ
      (lvAt LJ BJ (nat_lit 16) i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i) (TIJ i)))

@[expose] noncomputable def sch0 (s : Nat) : Bool :=
  schSlK LJ BJ (nat_lit 16) PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 0)
    (Nat.mul s (nat_lit 45)) (nat_lit 45)

@[expose] noncomputable def sch12 : Bool :=
  bAnd(schSlK LJ BJ (nat_lit 16) PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 1) (nat_lit 0)
    (nat_lit 160),
    schSlK LJ BJ (nat_lit 16) PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 3) (nat_lit 2) (nat_lit 0)
      (nat_lit 12))

@[expose] noncomputable def term : Bool := termK LJ BJ (nat_lit 16) (nat_lit 3) QL

@[expose] noncomputable def subPt : Bool :=
  allN (nat_lit 315) (subPtK (nat_lit 6) LBL REP SPTSJ SPOSJ SCNTJ)

@[expose] noncomputable def subRep : Bool :=
  allN (nat_lit 6) (subRepK (nat_lit 315) (nat_lit 6) CT0.cnt LBL REP CT0.PTS CT0.POS)

@[expose] noncomputable def subTree (l : Nat) : Bool :=
  bAnd(tbfsHdK (nat_lit 315) (r32 REP l) (SCNTJ l) (SPTSJ l) (SPOSJ l) (SPARJ l) (SLABJ l),
    allN (SCNTJ l) (tbfsPtK (nat_lit 315) (SCNTJ l) (lvK LJ BJ (nat_lit 16) (nat_lit 1)).length LJ
      (lvAt LJ BJ (nat_lit 16) (nat_lit 1)) (SPTSJ l) (SPOSJ l) (SPARJ l) (SLABJ l) (STIJ l)))

@[expose] noncomputable def imAt (l : Nat) : Bool :=
  allN (nat_lit 315) (imAtK LJ CT0.PAR CT0.LAB CT0.POS REP IM (nat_lit 315) l)

@[expose] noncomputable def der : Bool :=
  allN (nat_lit 6) fun i => bIf(Nat.beq i (r32 LBL (nat_lit 0)), true,
    derK (nat_lit 315) (nat_lit 6) LBL IM DS DOFF DLEN i)

end CertificateChecks.KernelSpor.J2K

end
