module

public import Certificates.Kernel.SporSch.HN.Pt2108Data
public import Certificates.Kernel.SporSch.HN.Pt2108Tab
public import Certificates.Kernel.SporSch.HN.PtR
public import Certificates.Kernel.SporSch.HN.Pt2109Data
public import Certificates.Data.Kernel.SporSch.HNXSyl
public import Certificates.Data.Kernel.SporSch.HNXPtL
public import Certificates.Data.Kernel.Spor.EnumBase
public import CFSG.Certificates.Kernel.Local.HN.X.Data
public import CFSG.Sporadic.HNSchreier.FAData
public import CFSG.Sporadic.HNSchreier.SylowData
public import CFSG.Sporadic.HNSchreier.Data
import Certificates.Kernel.SporSch.HN.Pt2108RowCmd

public section

namespace CertificateChecks.KernelSporSch.HNPt2108

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KC.LL.HNXT4 CFSG.KC.LL.HNXSyl CFSG.KS.EnumBase
open CFSG.KD.HNPt2108 CFSG.Sporadic.HNSchreier CFSG.KD.LgHNX

@[expose] noncomputable def g0 (l : List Nat) (i : Nat) : Nat := l.getD i (nat_lit 0)

@[expose] noncomputable def PARf (i : Nat) : Nat := (FAData.pParents[i]!).1
@[expose] noncomputable def LABf (i : Nat) : Nat := (FAData.pParents[i]!).2

#hn_rowtab VRT CFSG.KD.HNPt2108.VR
#hn_rowtab WRT CFSG.KD.HNPt2108.WR

@[expose] noncomputable def VRf (i : Nat) : Nat := VRT i
@[expose] noncomputable def WRf (i : Nat) : Nat := WRT i
@[expose] noncomputable def SGf (j : Nat) : Nat := g0 SG j

@[expose] noncomputable def Lf (j i : Nat) : Nat := lane (LPt j) 10 1023 i
@[expose] noncomputable def Cf (j i : Nat) : Nat := lane (CPt j) 10 1023 i

theorem Lf_eq (j i : Nat) : Lf j i = (FAData.pLeft[j]!)[i]! := (left_get j i).symm

theorem Cf_eq (j i : Nat) : Cf j i = (SylowData.conj[j]!)[i]! := (conj_get j i).symm

@[expose] noncomputable def f42 (P i : Nat) : Nat := fldW P (Nat.mul (nat_lit 42) i) (nat_lit 42)

@[expose] noncomputable def vS (s : Nat) : Bool :=
  allN 61 fun d => strictB (Nat.add (Nat.add (Nat.mul 61 s) d) 1) fun i =>
    bIf(Nat.blt i 729, rowK SGf VRf PARf LABf 22 i, true)

@[expose] noncomputable def wS (s : Nat) : Bool :=
  allN 61 fun d => strictB (Nat.add (Nat.add (Nat.mul 61 s) d) 1) fun i =>
    bIf(Nat.blt i 729, rowK SGf WRf PARf LABf 132 i, true)

@[expose] noncomputable def lS (q : Nat) : Bool :=
  strictB (Nat.div q 3) fun j => strictB (Nat.mod q 3) fun s =>
    allN 243 fun d => strictB (Nat.add (Nat.mul 243 s) d) fun i =>
      imgK SGf VRf 22 j (Lf j i) i

@[expose] noncomputable def cS (q : Nat) : Bool :=
  strictB (Nat.div q 3) fun j => strictB (Nat.mod q 3) fun s =>
    allN 243 fun d => strictB (Nat.add (Nat.mul 243 s) d) fun i =>
      blockK SGf VRf WRf 22 j (Cf j i) i

@[expose] noncomputable def dS (s : Nat) : Bool :=
  allN 61 fun d => strictB (Nat.add (Nat.mul 61 s) d) fun i =>
    bIf(Nat.blt i 729, allN i fun k => Bool.not (Nat.beq (f42 KY i) (f42 KY k)), true)

@[expose] noncomputable def C3S (j : Nat) : Nat :=
  [CFSG.KD.HNPt2109.C3_0, CFSG.KD.HNPt2109.C3_1, CFSG.KD.HNPt2109.C3_2, CFSG.KD.HNPt2109.C3_3,
    CFSG.KD.HNPt2109.C3_4, CFSG.KD.HNPt2109.C3_5, CFSG.KD.HNPt2109.C3_6].getD j 0

@[expose] noncomputable def GMf (j : Nat) : Nat := g0 GM j

@[expose] def scodeK (l : Int) : Nat := if 0 < l then l.toNat - 1 else 16 + (-l).toNat

@[expose] noncomputable def liftM (w : List Nat) : Nat :=
  w.foldl (fun acc l => CFSG.KC.LL.HN.mm acc (C3S (l - 1))) CFSG.KD.OrdHN.ONE

@[expose] noncomputable def pS (q : Nat) : Bool :=
  strictB (Nat.div q 15) fun j => strictB (Nat.mod q 15) fun s =>
    ptsFn TX MS CM3 M (trM (GMf j)) (fun t => f21 OM (Nat.add (Nat.mul 1024 s) t))
      (fun t => f21 OM (f14 (SGf j) (Nat.add (Nat.mul 1024 s) t)))
      (nIf(Nat.blt s 14, 1024, 976))

@[expose] noncomputable def EM (i : Nat) : Nat := emat GMf PARf LABf 729 i

@[expose] noncomputable def cubF (mk : Bool) (i c b y : Nat) : Bool :=
  bIf(mk, Nat.beq c CFSG.KD.OrdHN.ONE,
    bIf(Nat.beq i 0, true, bAnd(ptsImg TX MS CM3 M (trM c) b y 1, Bool.not (Nat.beq y b))))

@[expose] noncomputable def cub (i : Nat) : Bool :=
  cubF (memL SylowData.order3 i) i (CFSG.KC.LL.HN.mm (EM i) (CFSG.KC.LL.HN.mm (EM i) (EM i)))
    (g0 Data.baseList (fldW CK (Nat.mul 5 i) 5)) (f21 CY i)

@[expose] noncomputable def qS (s : Nat) : Bool :=
  allN 27 fun d => cub (Nat.add (Nat.mul 27 s) d)

@[expose] noncomputable def rep (c : Nat) : Bool :=
  strictB (wordC CFSG.KD.HNPt.R ((FAData.wRoot[c]!).map (33 + ·))) fun S =>
  strictB (wordC CFSG.KD.HNPt.R ((FAData.wHWord[c]!).map scodeK)) fun H =>
    Nat.beq (CFSG.KC.LL.HN.mm (EM FAData.wRep[c]!) S) (CFSG.KC.LL.HN.mm S H)

@[expose] noncomputable def rS (s : Nat) : Bool := allN 8 fun d => rep (Nat.add (Nat.mul 8 s) d)

end CertificateChecks.KernelSporSch.HNPt2108

end
