module

public import Certificates.Kernel.Sporadic.J3K.Data
public import CFSG.Certificates.Kernel.Spor.J3Sound
public import CFSG.Certificates.Kernel.Bounds.J3Alt.Rels

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.J3K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.Row CFSG.KS.J3S
open CFSG.Sporadic.J3.Native CFSG.Sporadic.Th.Native

@[expose] def decodeLT (cs : List Char) : List Nat :=
  let body := (cs.dropWhile (· != '\n')).drop 1
  (body.filter fun c => !wsChar c).map fun c =>
    if '0' ≤ c && c ≤ '9' then c.toNat - '0'.toNat else 0

@[expose] def rowsOfPayloadL (d : Nat) (cs : List Char) : Array Nat :=
  let e := (decodeLT cs).toArray
  Array.ofFn (n := d) fun i => ofBits d fun j => (e[i.val * d + j]?.getD 0) % 2 == 1

@[expose] noncomputable def CAJ : Array Nat := CAL.toArray
@[expose] noncomputable def CBJ : Array Nat := CBL.toArray

@[expose] noncomputable def PJ (i : Nat) : Nat := rg (nat_lit 80) (mask (nat_lit 80)) PT (nat_lit 0) i

@[expose] noncomputable def LJ (l x : Nat) : Nat := r32 LT (Nat.add (Nat.mul l (nat_lit 20520)) x)

@[expose] noncomputable def BJ (i : Nat) : Nat := i

@[expose] noncomputable def GJ (z : Int) (x : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => nIf(Nat.beq k (nat_lit 1), r32 TA x, nIf(Nat.beq k (nat_lit 2), r32 TB x, r32 BI x)))
    (fun k => nIf(Nat.beq k (nat_lit 0), r32 AI x, r32 BI x)) z

@[expose] noncomputable def slpGK (z : Int) (v : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => nIf(Nat.ble k (nat_lit 2), GJ (Int.ofNat k) v,
      LJ (Nat.mul (nat_lit 2) (Nat.sub k (nat_lit 3))) v))
    (fun k => nIf(Nat.ble (Nat.succ k) (nat_lit 2), GJ (Int.negSucc k) v,
      LJ (Nat.succ (Nat.mul (nat_lit 2) (Nat.sub (Nat.succ k) (nat_lit 3)))) v)) z

@[expose] noncomputable def letK (l : Nat × Bool) (v : Nat) : Nat :=
  nIf(Nat.beq l.1 (nat_lit 0), Bool.rec (r32 AI v) (r32 TA v) l.2, Bool.rec (r32 BI v) (r32 TB v) l.2)

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

@[expose] noncomputable def sbSel (fs : List (Nat → Nat)) (l : Nat) : Nat → Nat :=
  List.getD fs l fun _ => nat_lit 0
@[expose] noncomputable def SPTSJ : Nat → Nat → Nat := sbSel [SB0.PTS, SB1.PTS, SB2.PTS, SB3.PTS,
  SB4.PTS, SB5.PTS, SB6.PTS, SB7.PTS, SB8.PTS, SB9.PTS, SB10.PTS, SB11.PTS, SB12.PTS, SB13.PTS,
  SB14.PTS, SB15.PTS, SB16.PTS, SB17.PTS, SB18.PTS, SB19.PTS, SB20.PTS, SB21.PTS]
@[expose] noncomputable def SPOSJ : Nat → Nat → Nat := sbSel [SB0.POS, SB1.POS, SB2.POS, SB3.POS,
  SB4.POS, SB5.POS, SB6.POS, SB7.POS, SB8.POS, SB9.POS, SB10.POS, SB11.POS, SB12.POS, SB13.POS,
  SB14.POS, SB15.POS, SB16.POS, SB17.POS, SB18.POS, SB19.POS, SB20.POS, SB21.POS]
@[expose] noncomputable def SPARJ : Nat → Nat → Nat := sbSel [SB0.PAR, SB1.PAR, SB2.PAR, SB3.PAR,
  SB4.PAR, SB5.PAR, SB6.PAR, SB7.PAR, SB8.PAR, SB9.PAR, SB10.PAR, SB11.PAR, SB12.PAR, SB13.PAR,
  SB14.PAR, SB15.PAR, SB16.PAR, SB17.PAR, SB18.PAR, SB19.PAR, SB20.PAR, SB21.PAR]
@[expose] noncomputable def SLABJ : Nat → Nat → Nat := sbSel [SB0.LAB, SB1.LAB, SB2.LAB, SB3.LAB,
  SB4.LAB, SB5.LAB, SB6.LAB, SB7.LAB, SB8.LAB, SB9.LAB, SB10.LAB, SB11.LAB, SB12.LAB, SB13.LAB,
  SB14.LAB, SB15.LAB, SB16.LAB, SB17.LAB, SB18.LAB, SB19.LAB, SB20.LAB, SB21.LAB]
@[expose] noncomputable def STIJ : Nat → Nat → Nat := sbSel [SB0.TI, SB1.TI, SB2.TI, SB3.TI,
  SB4.TI, SB5.TI, SB6.TI, SB7.TI, SB8.TI, SB9.TI, SB10.TI, SB11.TI, SB12.TI, SB13.TI,
  SB14.TI, SB15.TI, SB16.TI, SB17.TI, SB18.TI, SB19.TI, SB20.TI, SB21.TI]
@[expose] noncomputable def SCNTJ (l : Nat) : Nat := List.getD [SB0.cnt, SB1.cnt, SB2.cnt, SB3.cnt,
  SB4.cnt, SB5.cnt, SB6.cnt, SB7.cnt, SB8.cnt, SB9.cnt, SB10.cnt, SB11.cnt, SB12.cnt, SB13.cnt,
  SB14.cnt, SB15.cnt, SB16.cnt, SB17.cnt, SB18.cnt, SB19.cnt, SB20.cnt, SB21.cnt] l (nat_lit 0)

@[expose] noncomputable def REPJ (l : Nat) : Nat := ((j3Data ()).subReps)[l]!

@[expose] noncomputable def ptSl (s : Nat) : Bool :=
  allN (nat_lit 500) fun d => strictB (Nat.add (Nat.mul s (nat_lit 500)) d) fun i =>
    bIf(Nat.blt i (nat_lit 20520),
      decide (PJ i < 2 ^ 80) && decide (r32 TA i < 20520) && decide (r32 TB i < 20520) &&
        vecMulN 80 CAJ (PJ i) == PJ (r32 TA i) && vecMulN 80 CBJ (PJ i) == PJ (r32 TB i) &&
        (decide (20520 ≤ i + 1) || decide (PJ i < PJ (i + 1))), true)

@[expose] noncomputable def invAB : Bool :=
  allN (nat_lit 20520) fun x => bAnd(Nat.blt (r32 AI x) (nat_lit 20520),
    bAnd(Nat.beq (r32 AI (r32 TA x)) x, bAnd(Nat.blt (r32 BI x) (nat_lit 20520),
      Nat.beq (r32 BI (r32 TB x)) x)))

@[expose] noncomputable def bfs : Bool :=
  decide (r32 BO 0 < 20520) && PJ (r32 BO 0) == 16561281922307987041 &&
    allN (nat_lit 20520) fun k => decide (r32 BOI k < 20520) && r32 BO (r32 BOI k) == k &&
      (k == 0 || (decide (r32 BO k < 20520) && decide (r32 BQ k < k) &&
        (r32 BO k == r32 TA (r32 BO (r32 BQ k)) || r32 BO k == r32 TB (r32 BO (r32 BQ k)))))

@[expose] noncomputable def wordsSl (s : Nat) : Bool :=
  strictB (Nat.div s (nat_lit 10)) fun j => strictB (Nat.mul (Nat.mod s (nat_lit 10)) (nat_lit 2052))
    fun lo => allN (nat_lit 2052) fun d => strictB (Nat.add lo d) fun x =>
      bIf(Nat.blt x (nat_lit 20520),
        Nat.beq (LJ (Nat.mul (nat_lit 2) j) x) (List.foldr slpGK x ((j3Data ()).words)[j]!), true)

@[expose] noncomputable def invL : Bool := invK LJ (nat_lit 20520) (nat_lit 8)

@[expose] noncomputable def relSl (s : Nat) : Bool :=
  strictB (Nat.div s (nat_lit 10)) fun r => strictB (Nat.mul (Nat.mod s (nat_lit 10)) (nat_lit 2052))
    fun lo => allN (nat_lit 2052) fun d => strictB (Nat.add lo d) fun x =>
      bIf(Nat.blt x (nat_lit 20520),
        Nat.beq (List.foldr letK x (CFSG.KC.J3A.rels.getD r [])) x, true)

@[expose] noncomputable def tree0Sl (s : Nat) : Bool :=
  bAnd(tbfsHdK (nat_lit 20520) (nat_lit 0) CT0.cnt CT0.PTS CT0.POS CT0.PAR CT0.LAB,
    tbfsSlK (nat_lit 20520) CT0.cnt (lvK LJ BJ (nat_lit 8) (nat_lit 0)).length LJ
      (lvAt LJ BJ (nat_lit 8) (nat_lit 0)) CT0.PTS CT0.POS CT0.PAR CT0.LAB CT0.TI
      (Nat.mul s (nat_lit 2052)) (nat_lit 2052))

@[expose] noncomputable def tree1 : Bool :=
  bAnd(tbfsHdK (nat_lit 20520) (nat_lit 1) CT1.cnt CT1.PTS CT1.POS CT1.PAR CT1.LAB,
    allN CT1.cnt (tbfsPtK (nat_lit 20520) CT1.cnt (lvK LJ BJ (nat_lit 8) (nat_lit 1)).length LJ
      (lvAt LJ BJ (nat_lit 8) (nat_lit 1)) CT1.PTS CT1.POS CT1.PAR CT1.LAB CT1.TI))

@[expose] noncomputable def subTree (l : Nat) : Bool :=
  bAnd(tbfsHdK (nat_lit 20520) (REPJ l) (SCNTJ l) (SPTSJ l) (SPOSJ l) (SPARJ l) (SLABJ l),
    allN (SCNTJ l) (tbfsPtK (nat_lit 20520) (SCNTJ l) (lvK LJ BJ (nat_lit 8) (nat_lit 1)).length LJ
      (lvAt LJ BJ (nat_lit 8) (nat_lit 1)) (SPTSJ l) (SPOSJ l) (SPARJ l) (SLABJ l) (STIJ l)))

@[expose] noncomputable def labSl (s : Nat) : Bool :=
  allN (nat_lit 2052) fun d => strictB (Nat.add (Nat.mul s (nat_lit 2052)) d) fun z =>
    bIf(Nat.blt z (nat_lit 20520),
      strictB (r32 LBL z) fun l => decide (l < 22) && decide (r32 (SPOSJ l) z < SCNTJ l) &&
        r32 (SPTSJ l) (r32 (SPOSJ l) z) == z, true)

@[expose] noncomputable def labOK : Bool :=
  allN (nat_lit 22) fun l => decide (r32 CT0.POS (REPJ l) < CT0.cnt) &&
    r32 CT0.PTS (r32 CT0.POS (REPJ l)) == REPJ l &&
    allN (SCNTJ l) fun q => r32 LBL (r32 (SPTSJ l) q) == l

@[expose] noncomputable def der : Bool :=
  allN (nat_lit 21) fun c => derK3 20520 22 LJ (r32 LBL) REPJ CT0.PAR CT0.LAB CT0.POS (Nat.succ c)
    ((j3Data ()).derivs)[Nat.succ c]!

end CertificateChecks.KernelSpor.J3K

end
