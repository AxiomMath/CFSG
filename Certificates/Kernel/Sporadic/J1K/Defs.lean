module

public import Certificates.Kernel.Sporadic.J1K.Data
public import Certificates.Data.Kernel.Spor.VOrb
public import Certificates.Data.Kernel.Spor.PrimK

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J1K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.VO CFSG.KS.PR
open CFSG.Sporadic.J1.Native

@[expose] noncomputable def LJ (l x : Nat) : Nat := r32 LT (Nat.add (Nat.mul l (nat_lit 1540)) x)

@[expose] noncomputable def BJ (i : Nat) : Nat := nIf(Nat.beq i (nat_lit 0), nat_lit 0, nat_lit 1)

@[expose] noncomputable def GJ (z : Int) (x : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => nIf(Nat.beq k (nat_lit 1), r32 AL x, nIf(Nat.beq k (nat_lit 2), r32 BE x, r32 BI x)))
    (fun k => nIf(Nat.beq k (nat_lit 0), r32 AI x, r32 BI x)) z

@[expose] noncomputable def PTSJ (i : Nat) : Nat → Nat :=
  Bool.rec (motive := fun _ => Nat → Nat) CT1.PTS CT0.PTS (Nat.beq i (nat_lit 0))
@[expose] noncomputable def POSJ (i : Nat) : Nat → Nat :=
  Bool.rec (motive := fun _ => Nat → Nat) CT1.POS CT0.POS (Nat.beq i (nat_lit 0))
@[expose] noncomputable def PARJ (i : Nat) : Nat → Nat :=
  Bool.rec (motive := fun _ => Nat → Nat) CT1.PAR CT0.PAR (Nat.beq i (nat_lit 0))
@[expose] noncomputable def LABJ (i : Nat) : Nat → Nat :=
  Bool.rec (motive := fun _ => Nat → Nat) CT1.LAB CT0.LAB (Nat.beq i (nat_lit 0))
@[expose] noncomputable def TIJ (i : Nat) : Nat → Nat :=
  Bool.rec (motive := fun _ => Nat → Nat) CT1.TI CT0.TI (Nat.beq i (nat_lit 0))
@[expose] noncomputable def CNTJ (i : Nat) : Nat := nIf(Nat.beq i (nat_lit 0), CT0.cnt, CT1.cnt)

@[expose] noncomputable def QL : List Nat := [0, 1, 489, 1215, 1116, 269, 759, 2]

@[expose] noncomputable def QB (i : Nat) : Nat := i

@[expose] noncomputable def sbSel (fs : List (Nat → Nat)) (l : Nat) : Nat → Nat :=
  List.getD fs l fun _ => nat_lit 0
@[expose] noncomputable def SPTSJ : Nat → Nat → Nat := sbSel [SB0.PTS, SB1.PTS, SB2.PTS, SB3.PTS,
  SB4.PTS, SB5.PTS, SB6.PTS, SB7.PTS, SB8.PTS, SB9.PTS, SB10.PTS, SB11.PTS, SB12.PTS, SB13.PTS,
  SB14.PTS, SB15.PTS, SB16.PTS, SB17.PTS, SB18.PTS, SB19.PTS, SB20.PTS]
@[expose] noncomputable def SPOSJ : Nat → Nat → Nat := sbSel [SB0.POS, SB1.POS, SB2.POS, SB3.POS,
  SB4.POS, SB5.POS, SB6.POS, SB7.POS, SB8.POS, SB9.POS, SB10.POS, SB11.POS, SB12.POS, SB13.POS,
  SB14.POS, SB15.POS, SB16.POS, SB17.POS, SB18.POS, SB19.POS, SB20.POS]
@[expose] noncomputable def SPARJ : Nat → Nat → Nat := sbSel [SB0.PAR, SB1.PAR, SB2.PAR, SB3.PAR,
  SB4.PAR, SB5.PAR, SB6.PAR, SB7.PAR, SB8.PAR, SB9.PAR, SB10.PAR, SB11.PAR, SB12.PAR, SB13.PAR,
  SB14.PAR, SB15.PAR, SB16.PAR, SB17.PAR, SB18.PAR, SB19.PAR, SB20.PAR]
@[expose] noncomputable def SLABJ : Nat → Nat → Nat := sbSel [SB0.LAB, SB1.LAB, SB2.LAB, SB3.LAB,
  SB4.LAB, SB5.LAB, SB6.LAB, SB7.LAB, SB8.LAB, SB9.LAB, SB10.LAB, SB11.LAB, SB12.LAB, SB13.LAB,
  SB14.LAB, SB15.LAB, SB16.LAB, SB17.LAB, SB18.LAB, SB19.LAB, SB20.LAB]
@[expose] noncomputable def STIJ : Nat → Nat → Nat := sbSel [SB0.TI, SB1.TI, SB2.TI, SB3.TI,
  SB4.TI, SB5.TI, SB6.TI, SB7.TI, SB8.TI, SB9.TI, SB10.TI, SB11.TI, SB12.TI, SB13.TI,
  SB14.TI, SB15.TI, SB16.TI, SB17.TI, SB18.TI, SB19.TI, SB20.TI]
@[expose] noncomputable def SCNTJ (l : Nat) : Nat := List.getD [SB0.cnt, SB1.cnt, SB2.cnt, SB3.cnt,
  SB4.cnt, SB5.cnt, SB6.cnt, SB7.cnt, SB8.cnt, SB9.cnt, SB10.cnt, SB11.cnt, SB12.cnt, SB13.cnt,
  SB14.cnt, SB15.cnt, SB16.cnt, SB17.cnt, SB18.cnt, SB19.cnt, SB20.cnt] l (nat_lit 0)

@[expose] noncomputable def orbHd : Bool :=
  vorbHdK (nat_lit 11) (nat_lit 7) (nat_lit 1540) (nat_lit 2000) (mA ()) (mB ()) (root ()) (r32 PT) AL BE PA LA

@[expose] noncomputable def orbPt : Bool :=
  allN (nat_lit 1540) (vorbPtK (nat_lit 11) (nat_lit 7) (nat_lit 1540) (sgnKey (nat_lit 11)) (mA ()) (mB ())
    (r32 PT) AL BE)

@[expose] noncomputable def orbSort : Bool := allN (nat_lit 1540) (vorbSortK (nat_lit 1540) (r32 PT) SO)

@[expose] noncomputable def projSort : Bool :=
  allN (nat_lit 1540) (projSortK (nat_lit 11) (nat_lit 7) (nat_lit 1540) (r32 PT) SP)

@[expose] noncomputable def invAB : Bool :=
  allN (nat_lit 1540) fun x => bAnd(Nat.blt (r32 AL x) (nat_lit 1540),
    bAnd(Nat.beq (r32 AI (r32 AL x)) x, bAnd(Nat.blt (r32 BE x) (nat_lit 1540),
    bAnd(Nat.beq (r32 BI (r32 BE x)) x, bAnd(Nat.blt (r32 AI x) (nat_lit 1540),
      Nat.blt (r32 BI x) (nat_lit 1540))))))

@[expose] noncomputable def wordsOK : Bool :=
  allN (nat_lit 5) fun j => allN (nat_lit 1540) fun x =>
    Nat.beq (LJ (Nat.mul (nat_lit 2) j) x) (List.foldr GJ x (chainWords ())[j]!)

@[expose] noncomputable def invL : Bool := invK LJ (nat_lit 1540) (nat_lit 10)

@[expose] noncomputable def tree0 : Bool :=
  bAnd(tbfsHdK (nat_lit 1540) (nat_lit 0) CT0.cnt CT0.PTS CT0.POS CT0.PAR CT0.LAB,
    allN CT0.cnt (tbfsPtK (nat_lit 1540) CT0.cnt (lvK LJ BJ (nat_lit 10) (nat_lit 0)).length LJ
      (lvAt LJ BJ (nat_lit 10) (nat_lit 0)) CT0.PTS CT0.POS CT0.PAR CT0.LAB CT0.TI))

@[expose] noncomputable def tree1 : Bool :=
  bAnd(tbfsHdK (nat_lit 1540) (nat_lit 1) CT1.cnt CT1.PTS CT1.POS CT1.PAR CT1.LAB,
    allN CT1.cnt (tbfsPtK (nat_lit 1540) CT1.cnt (lvK LJ BJ (nat_lit 10) (nat_lit 1)).length LJ
      (lvAt LJ BJ (nat_lit 10) (nat_lit 1)) CT1.PTS CT1.POS CT1.PAR CT1.LAB CT1.TI))

@[expose] noncomputable def sch0 (s : Nat) : Bool :=
  schSlK LJ BJ (nat_lit 10) PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 2) (nat_lit 0)
    (Nat.mul s (nat_lit 55)) (nat_lit 55)

@[expose] noncomputable def sch1 : Bool :=
  schSlK LJ BJ (nat_lit 10) PTSJ POSJ PARJ LABJ CNTJ QB QL (nat_lit 2) (nat_lit 1) (nat_lit 0)
    (nat_lit 114)

@[expose] noncomputable def term : Bool := termK LJ BJ (nat_lit 10) (nat_lit 2) QL

@[expose] noncomputable def subPt : Bool :=
  allN (nat_lit 1540) (subPtK (nat_lit 21) LBL REP SPTSJ SPOSJ SCNTJ)

@[expose] noncomputable def subRep : Bool :=
  allN (nat_lit 21) (subRepK (nat_lit 1540) (nat_lit 21) CT0.cnt LBL REP CT0.PTS CT0.POS)

@[expose] noncomputable def subTree (l : Nat) : Bool :=
  bAnd(tbfsHdK (nat_lit 1540) (r32 REP l) (SCNTJ l) (SPTSJ l) (SPOSJ l) (SPARJ l) (SLABJ l),
    allN (SCNTJ l) (tbfsPtK (nat_lit 1540) (SCNTJ l) (lvK LJ BJ (nat_lit 10) (nat_lit 1)).length LJ
      (lvAt LJ BJ (nat_lit 10) (nat_lit 1)) (SPTSJ l) (SPOSJ l) (SPARJ l) (SLABJ l) (STIJ l)))

@[expose] noncomputable def imAt (l : Nat) : Bool :=
  allN (nat_lit 1540) (imAtK LJ CT0.PAR CT0.LAB CT0.POS REP IM (nat_lit 1540) l)

@[expose] noncomputable def der : Bool :=
  allN (nat_lit 21) fun i => bIf(Nat.beq i (r32 LBL (nat_lit 0)), true,
    derK (nat_lit 1540) (nat_lit 21) LBL IM DS DOFF DLEN i)

end CertificateChecks.KernelSpor.J1K

end
