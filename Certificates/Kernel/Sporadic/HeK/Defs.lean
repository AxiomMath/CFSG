module

public import Certificates.Kernel.Sporadic.HeK.Data
public import Certificates.Kernel.HeOrb.Data
public import Certificates.Kernel.HeTab.Data
public import Certificates.Data.Kernel.HeOrbK
public import Certificates.Data.Kernel.HeTabK
public import Certificates.Data.Kernel.He3168K
public import CFSG.Certificates.Kernel.Orders.He.Rels

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HeK

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.VO CFSG.KC.HeOrb
  CFSG.KS.SporSch.LyM CFSG.KD.HeOrb CFSG.KD.HeTab CFSG.KC.He3168
open CFSG.Sporadic.He.Native

@[expose] noncomputable def MAK : Nat := payRunP 7 50 12 600 SA.chars 0 0 0
@[expose] noncomputable def MBK : Nat := payRunP 7 50 12 600 SB.chars 0 0 0
@[expose] noncomputable def QK : Nat := MATS.getD 0 0
@[expose] noncomputable def YK : Nat := MATS.getD 1 0

@[expose] noncomputable def PH (i : Nat) : Nat := code PT i

@[expose] noncomputable def LJ (l x : Nat) : Nat := r32 LT (Nat.add (Nat.mul l (nat_lit 8330)) x)

@[expose] noncomputable def BJ (i : Nat) : Nat := List.getD [0, 1, 3, 4, 2] i (nat_lit 0)

@[expose] noncomputable def GJ (z : Int) (x : Nat) : Nat := CFSG.KC.HeTab.GK AL BE BI z x

@[expose] noncomputable def slpGK (z : Int) (v : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat)
    (fun k => nIf(Nat.ble k (nat_lit 2), GJ (Int.ofNat k) v,
      LJ (Nat.mul (nat_lit 2) (Nat.sub k (nat_lit 3))) v))
    (fun k => nIf(Nat.ble (Nat.succ k) (nat_lit 2), GJ (Int.negSucc k) v,
      LJ (Nat.succ (Nat.mul (nat_lit 2) (Nat.sub (Nat.succ k) (nat_lit 3)))) v)) z

@[expose] noncomputable def letK (l : Nat × Bool) (v : Nat) : Nat :=
  nIf(Nat.beq l.1 (nat_lit 0), r32 AL v, Bool.rec (r32 BI v) (r32 BE v) l.2)

@[expose] noncomputable def lvSel (fs : List (Nat → Nat)) (i : Nat) : Nat → Nat :=
  List.getD fs i fun _ => nat_lit 0
@[expose] noncomputable def PTSJ : Nat → Nat → Nat := lvSel [CT0.PTS, CT1.PTS, CT2.PTS, CT3.PTS, CT4.PTS]
@[expose] noncomputable def POSJ : Nat → Nat → Nat := lvSel [CT0.POS, CT1.POS, CT2.POS, CT3.POS, CT4.POS]
@[expose] noncomputable def PARJ : Nat → Nat → Nat := lvSel [CT0.PAR, CT1.PAR, CT2.PAR, CT3.PAR, CT4.PAR]
@[expose] noncomputable def LABJ : Nat → Nat → Nat := lvSel [CT0.LAB, CT1.LAB, CT2.LAB, CT3.LAB, CT4.LAB]
@[expose] noncomputable def TIJ : Nat → Nat → Nat := lvSel [CT0.TI, CT1.TI, CT2.TI, CT3.TI, CT4.TI]
@[expose] noncomputable def CNTJ (i : Nat) : Nat :=
  List.getD [CT0.cnt, CT1.cnt, CT2.cnt, CT3.cnt, CT4.cnt] i (nat_lit 0)

@[expose] noncomputable def SPTSJ : Nat → Nat → Nat :=
  lvSel [SB0.PTS, SB1.PTS, SB2.PTS, SB3.PTS, SB4.PTS, SB5.PTS, SB6.PTS]
@[expose] noncomputable def SPOSJ : Nat → Nat → Nat :=
  lvSel [SB0.POS, SB1.POS, SB2.POS, SB3.POS, SB4.POS, SB5.POS, SB6.POS]
@[expose] noncomputable def SPARJ : Nat → Nat → Nat :=
  lvSel [SB0.PAR, SB1.PAR, SB2.PAR, SB3.PAR, SB4.PAR, SB5.PAR, SB6.PAR]
@[expose] noncomputable def SLABJ : Nat → Nat → Nat :=
  lvSel [SB0.LAB, SB1.LAB, SB2.LAB, SB3.LAB, SB4.LAB, SB5.LAB, SB6.LAB]
@[expose] noncomputable def STIJ : Nat → Nat → Nat :=
  lvSel [SB0.TI, SB1.TI, SB2.TI, SB3.TI, SB4.TI, SB5.TI, SB6.TI]
@[expose] noncomputable def SCNTJ (l : Nat) : Nat :=
  List.getD [SB0.cnt, SB1.cnt, SB2.cnt, SB3.cnt, SB4.cnt, SB5.cnt, SB6.cnt] l (nat_lit 0)

@[expose] noncomputable def WJ (x : Nat) : Nat := List.foldr GJ x (witWord ())

@[expose] noncomputable def itv (f : Nat → Nat) (e x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun v => v) (fun _ ih v => strictN (f v) ih) e x

@[expose] noncomputable def matOK : Bool :=
  vldH MAK && vldH MBK && vldH QK && vldH YK &&
    Nat.beq (mulH MAK MAK) cONE &&
    Nat.beq (powR 7 12 600 50 8 cL cH cCM cRM cONE MBK 7) cONE &&
    Nat.beq (mulH QK YK) cONE &&
    allN 50 fun t => colK QK t (PH t)

@[expose] noncomputable def invA : Bool :=
  allN (nat_lit 8330) fun x => Nat.beq (r32 AL (r32 AL x)) x

@[expose] noncomputable def wordsSl (s : Nat) : Bool :=
  strictB (Nat.div s (nat_lit 9)) fun j => strictB (Nat.mul (Nat.mod s (nat_lit 9)) (nat_lit 1000))
    fun lo => allN (nat_lit 1000) fun d => strictB (Nat.add lo d) fun x =>
      bIf(Nat.blt x (nat_lit 8330),
        Nat.beq (LJ (Nat.mul (nat_lit 2) j) x) (List.foldr slpGK x (chainWords ())[j]!), true)

@[expose] noncomputable def invL : Bool := invK LJ (nat_lit 8330) (nat_lit 16)

@[expose] noncomputable def relSl (s : Nat) : Bool :=
  strictB (Nat.div s (nat_lit 5)) fun r => strictB (Nat.mul (Nat.mod s (nat_lit 5)) (nat_lit 1700))
    fun lo => allN (nat_lit 1700) fun d => strictB (Nat.add lo d) fun x =>
      bIf(Nat.blt x (nat_lit 8330),
        Nat.beq (List.foldr letK x (CFSG.KD.OrdHe.rels.getD r [])) x, true)

@[expose] noncomputable def treeSl (i s : Nat) : Bool :=
  bAnd(tbfsHdK (nat_lit 8330) (BJ i) (CNTJ i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i),
    tbfsSlK (nat_lit 8330) (CNTJ i) (lvK LJ BJ (nat_lit 16) i).length LJ (lvAt LJ BJ (nat_lit 16) i)
      (PTSJ i) (POSJ i) (PARJ i) (LABJ i) (TIJ i) (Nat.mul s (nat_lit 1000)) (nat_lit 1000))

@[expose] noncomputable def treesSl (s : Nat) : Bool := treeSl (Nat.div s (nat_lit 9)) (Nat.mod s (nat_lit 9))

@[expose] noncomputable def subTree (l : Nat) : Bool :=
  bAnd(tbfsHdK (nat_lit 8330) (subRoots[l]!) (SCNTJ l) (SPTSJ l) (SPOSJ l) (SPARJ l) (SLABJ l),
    allN (SCNTJ l) (tbfsPtK (nat_lit 8330) (SCNTJ l) (lvK LJ BJ (nat_lit 16) (nat_lit 1)).length LJ
      (lvAt LJ BJ (nat_lit 16) (nat_lit 1)) (SPTSJ l) (SPOSJ l) (SPARJ l) (SLABJ l) (STIJ l)))

@[expose] noncomputable def labOK : Bool :=
  (allN (nat_lit 8330) fun z => strictB (r32 LBL z) fun l => decide (l < 7) &&
    decide (r32 (SPOSJ l) z < SCNTJ l) && r32 (SPTSJ l) (r32 (SPOSJ l) z) == z) &&
  allN (nat_lit 7) fun l => allN (SCNTJ l) fun q => r32 LBL (r32 (SPTSJ l) q) == l

@[expose] noncomputable def miscOK : Bool :=
  r32 LBL (WJ 0) == 5 && r32 LBL 21 == 3 && r32 LBL (WJ 21) == 1 && r32 LBL 24 == 4 &&
    r32 LBL (WJ 24) == 3 &&
    !(allN (nat_lit 8330) fun x => r32 AL x == x) &&
    (allN (nat_lit 8330) fun x => itv (r32 BE) 7 x == x) &&
    !(allN (nat_lit 8330) fun x => r32 BE x == x) &&
    (allN (nat_lit 8330) fun x => itv (fun y => r32 AL (r32 BE y)) 17 x == x) &&
    !(allN (nat_lit 8330) fun x => r32 AL (r32 BE x) == x)

end CertificateChecks.KernelSpor.HeK

end
