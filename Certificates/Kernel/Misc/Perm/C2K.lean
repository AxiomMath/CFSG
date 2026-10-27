module

public import Certificates.Kernel.Misc.Perm.C2Bind
public import CFSG.RankThree.Native.F2Enum
public import CFSG.RankThree.Native.F2K
public import CFSG.RankThree.Native.F2Bind
public import Certificates.Data.Kernel.Misc.ArrEnum

public section

namespace CertificateChecks.KernelMisc.Co2K

open CFSG.KC.Enum CFSG.RankThree.Native.F2

@[expose] noncomputable def M22 : ℕ := nat_lit 4194303

@[expose] noncomputable def L22 : ℕ :=
  nat_lit 11908528498073666995947969347157480251659827695481117700305989184378417062648132460131015248306064568667840854116287251142124832390176047105

@[expose] noncomputable def I22 : ℕ :=
  nat_lit 24973991379659707467621756579723706896969316949376236904045051527405272766968242940994766581490570014503808294292943339053779062356439532262391809

@[expose] noncomputable def M484 : ℕ :=
  nat_lit 49947976805055875702105555676690660891977570282639538413746511354005947821116249921924897649015871538557230897942505966327167610868612564900642815

@[expose] noncomputable def vmK (v M : ℕ) : ℕ := vmulK (nat_lit 22) M22 v M

@[expose] noncomputable def mmK (A B : ℕ) : ℕ := mulK (nat_lit 22) M22 L22 A B

@[expose] noncomputable def f12 (P i : ℕ) : ℕ := fld(P, Nat.mul (nat_lit 12) i, nat_lit 4095)

@[expose] noncomputable def VG (i : ℕ) : ℕ := fld(HV.F (nat_lit 0), Nat.mul (nat_lit 22) i, M22)

@[expose] noncomputable def lkPos (w : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun j acc => strictN acc fun pos =>
    (fun q => nIf(bAnd(Nat.blt q (nat_lit 2300),
        Nat.ble (fld(SVt (nat_lit 0), Nat.mul (nat_lit 22) q, M22)) w), q, pos))
      (Nat.add pos (Nat.shiftRight (nat_lit 2048) j))) (nat_lit 12)

@[expose] noncomputable def LK (w : ℕ) : ℕ := f12 (SPt (nat_lit 0)) (lkPos w)

@[expose] noncomputable def MS (j : ℕ) : ℕ := MSt j

@[expose] noncomputable def MSI (j : ℕ) : ℕ := MSt (Nat.add (nat_lit 11) j)

@[expose] noncomputable def AM (k : ℕ) : ℕ := AMt k

@[expose] noncomputable def AMI (k : ℕ) : ℕ := AMt (Nat.add (nat_lit 38) k)

@[expose] noncomputable def BS (t : ℕ) : ℕ := [0, 1, 2, 3, 5, 4].getD t 0

@[expose] noncomputable def mL (i : ℕ) : ℕ := [2300, 1408, 567, 192, 30, 4].getD i 0

@[expose] noncomputable def cL (i : ℕ) : ℕ := [11, 10, 8, 7, 4, 1].getD i 0

@[expose] noncomputable def rL (i : ℕ) : ℕ := [22, 20, 16, 14, 8, 2].getD i 0

@[expose] noncomputable def oL (i : ℕ) : ℕ := [0, 2300, 3708, 4275, 4467, 4497].getD i 0

@[expose] noncomputable def IX (i t : ℕ) : ℕ :=
  ([[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], [0, 2, 3, 4, 5, 6, 7, 8, 9, 10], [3, 4, 5, 6, 7, 8, 9, 10],
    [4, 5, 6, 7, 8, 9, 10], [6, 8, 9, 10], [9]].getD i []).getD t 0

@[expose] noncomputable def PT (i k : ℕ) : ℕ := f12 (LVt (Nat.mul (nat_lit 5) i)) k

@[expose] noncomputable def PO (i z : ℕ) : ℕ := f12 (LVt (Nat.add (Nat.mul (nat_lit 5) i) 1)) z

@[expose] noncomputable def PA (i k : ℕ) : ℕ := f12 (LVt (Nat.add (Nat.mul (nat_lit 5) i) 2)) k

@[expose] noncomputable def LB (i k : ℕ) : ℕ := f12 (LVt (Nat.add (Nat.mul (nat_lit 5) i) 3)) k

@[expose] noncomputable def ED (i h j : ℕ) : ℕ :=
  f12 (LVt (Nat.add (Nat.mul (nat_lit 5) i) 4)) (Nat.add (Nat.mul h (rL i)) j)

@[expose] noncomputable def TM (i k : ℕ) : ℕ := TMt (Nat.add (oL i) k)

@[expose] noncomputable def TIM (i k : ℕ) : ℕ := TMt (Nat.add (nat_lit 4501) (Nat.add (oL i) k))

@[expose] noncomputable def SM (i : ℕ) : ℕ → ℕ := stepM MS MSI (IX i) (cL i)

@[expose] noncomputable def SIM (i : ℕ) : ℕ → ℕ := stepIM MS MSI (IX i) (cL i)

@[expose] noncomputable def levK (i : ℕ) : Bool :=
  stepsM vmK VG MS 11 BS i (cL i) (IX i) &&
    levelM vmK mmK I22 2300 VG (BS i) (mL i) (rL i) (PT i) (PO i) (PA i) (LB i) (ED i) (SM i)
      (SIM i) (TM i) (TIM i)

@[expose] noncomputable def bindK (P M MI : ℕ) : Bool :=
  allN (nat_lit 2300) (fun i => Nat.blt (f12 P i) (nat_lit 2300) &&
    Nat.beq (VG (f12 P i)) (vmK (VG i) M)) &&
  Nat.beq (mmK M MI) I22 && Nat.beq (mmK MI M) I22 && Nat.ble M M484

@[expose] noncomputable def vecK : Bool := allN (nat_lit 2300) fun i => Nat.beq (LK (VG i)) i

@[expose] noncomputable def spanK : Bool :=
  allN (nat_lit 22) fun k => (spanLists.getD k []).all (fun i => Nat.blt i 2300) &&
    Nat.beq ((spanLists.getD k []).foldr (fun i acc => VG i ^^^ acc) 0)
      (Nat.shiftLeft 1 k)

@[expose] noncomputable def pwK (A e : ℕ) : ℕ := mpowW mmK I22 A e

@[expose] noncomputable def ZM : ℕ := mmK (mmK (AMI 8) (AM 1)) (AM 8)

@[expose] noncomputable def seRow (A : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) (nat_lit 0) (fun j acc => strictN acc fun pos =>
    (fun q => nIf(bAnd(Nat.blt q (nat_lit 3000), Nat.ble (SEt q) A), q, pos))
      (Nat.add pos (Nat.shiftRight (nat_lit 2048) j))) (nat_lit 12)

@[expose] noncomputable def memC0 (A : ℕ) : Bool :=
  Nat.blt (seRow A) (nat_lit 3000) && Nat.beq (SEt (seRow A)) A

@[expose] noncomputable def memZ (A : ℕ) : Bool :=
  (List.range 5).any fun e => Nat.beq A (pwK ZM e)

@[expose] noncomputable def pvf (i : ℕ) : Bool := Nat.blt 0 i && Nat.blt i 5

@[expose] noncomputable def pve (i : ℕ) : ℕ := [0, 1, 4, 2, 3].getD i 0

@[expose] noncomputable def comm (A X : ℕ) : Bool := Nat.beq (mmK X A) (mmK A X)

@[expose] noncomputable def siftK : Bool :=
  siftM vmK mmK I22 2300 VG BS LK mL PO TIM 6 0 I22 &&
    allN 38 fun k => siftM vmK mmK I22 2300 VG BS LK mL PO TIM 6 0 (AM k)

@[expose] noncomputable def fixK : Bool :=
  fixZ.all (fun q => Nat.blt q 2300 && Nat.beq (vmK (VG q) ZM) (VG q)) &&
    allN 2300 (fun q => !(Nat.beq (vmK (VG q) ZM) (VG q)) || fixZ.contains q) &&
    Nat.beq (fixZ.filter fun q => Nat.blt (PO 0 q) (mL 0)).length 10 &&
    Nat.beq (fixZ.filter fun q => Nat.blt (PO 1 q) (mL 1)).length 3 &&
    Nat.beq (fixZ.filter fun q => Nat.blt (PO 2 q) (mL 2)).length 2 &&
    Nat.beq (fixZ.filter fun q => Nat.blt (PO 3 q) (mL 3)).length 2 &&
    allN 4 fun k => Nat.beq (vmK (VG k) ZM) (VG k)

@[expose] noncomputable def tailK : Bool := tailM mmK ZM memZ mL TM 2 4 I22

@[expose] noncomputable def relsK : Bool :=
  CFSG.RankThree.Native.co2FiveRels.all fun r => Nat.blt r.2.2 5 && Nat.blt r.1 6 &&
    Nat.blt r.2.1 6 && Nat.beq (vmK (VG (BS r.1)) (pwK (AM 0) r.2.2)) (VG (BS r.2.1))

@[expose] noncomputable def ptR : ℕ → ℕ → ℕ → ℕ → Bool :=
  ptailM vmK mmK 2300 VG BS LK (pwK (AM 0)) CFSG.RankThree.Native.co2FiveRels (AM 0) memC0 pvf
    (fun _ => 0) pve mL PT PO TM TIM

@[expose] noncomputable def ptBody (k : ℕ) : Bool :=
  !(relM vmK VG BS (pwK (AM 0)) CFSG.RankThree.Native.co2FiveRels 0 I22 (PT 0 k)) ||
    ptR 5 1 (mmK (TM 0 k) I22) (mmK I22 (TIM 0 k))

@[expose] noncomputable def levHd0 : Bool :=
  stepsM vmK VG MS 11 BS 0 (cL 0) (IX 0) &&
    levelHd vmK mmK I22 2300 VG (BS 0) (mL 0) (rL 0) (PT 0) (PO 0) (PA 0) (LB 0) (SM 0)
      (SIM 0) (TM 0) (TIM 0)

@[expose] noncomputable def edge0 (h : ℕ) : Bool :=
  edgeM vmK VG (mL 0) (rL 0) (PT 0) (PA 0) (LB 0) (ED 0) (SM 0) h

@[expose] noncomputable def strongK : Bool :=
  Nat.beq CFSG.Sporadic.Co2Cert.co2StrongArrs.size 11 &&
    (CFSG.Sporadic.Co2Cert.co2BaseArr == #[0, 1, 2, 3, 5, 4]) &&
    allN 11 fun j => CFSG.KC.Misc.ArrEnum.arrBind CFSG.Sporadic.Co2Cert.co2StrongArrs[j]! 2300 12
      (SS j) && bindK (SS j) (MS j) (MSI j)

@[expose] noncomputable def PQ (i : ℕ) : ℕ := Nat.land (HQP.F i) M484

@[expose] noncomputable def PC0 (i : ℕ) : ℕ := Nat.land (HC0P.F i) M484

@[expose] noncomputable def PC1 (i : ℕ) : ℕ := Nat.land (HC1P.F i) M484

@[expose] noncomputable def PD (i : ℕ) : ℕ := Nat.land (HDP.F i) M484

@[expose] noncomputable def GQ (k : ℕ) : ℕ := [AM 4, AM 5].getD k 0

@[expose] noncomputable def GQI (k : ℕ) : ℕ := [AMI 4, AMI 5].getD k 0

@[expose] noncomputable def GC0 (k : ℕ) : ℕ := [AM 2, AM 3].getD k 0

@[expose] noncomputable def GC0I (k : ℕ) : ℕ := [AMI 2, AMI 3].getD k 0

@[expose] noncomputable def GC1 (k : ℕ) : ℕ := [AM 1, AM 6, AM 7].getD k 0

@[expose] noncomputable def GC1I (k : ℕ) : ℕ := [AMI 1, AMI 6, AMI 7].getD k 0

@[expose] noncomputable def DG0 : ℕ := mmK (mmK (AMI 7) (AMI 6)) (mmK (AM 7) (AM 6))

@[expose] noncomputable def DGI0 : ℕ := mmK (mmK (AMI 6) (AMI 7)) (mmK (AM 6) (AM 7))

@[expose] noncomputable def GD (k : ℕ) : ℕ := [DG0, AM 7].getD k 0

@[expose] noncomputable def GDI (k : ℕ) : ℕ := [DGI0, AMI 7].getD k 0

@[expose] noncomputable def SO (c j : ℕ) : ℕ := f12 (CSt (Nat.mul 2 c)) j

@[expose] noncomputable def SOI (c j : ℕ) : ℕ := f12 (CSt (Nat.add (Nat.mul 2 c) 1)) j

@[expose] noncomputable def ptsK (ngen N : ℕ) (GM PM : ℕ → ℕ) (HE HR HL : ℕ → ℕ) (lo cnt : ℕ) :
    Bool :=
  allN cnt fun t => pointM mmK ngen N GM PM (fun i k => f12 (HE i) k) (fun i => f12 (HR 0) i)
    (fun i => f12 (HL 0) i) (Nat.add lo t)

@[expose] noncomputable def keyK (PM : ℕ → ℕ) (i : ℕ) : ℕ :=
  keyM vmK 2300 VG LK [0, 1, 2, 3, 5, 4] PM i

@[expose] noncomputable def keysK (c N : ℕ) (PM : ℕ → ℕ) (lo cnt : ℕ) : Bool :=
  allN cnt fun t => (fun j => Nat.blt (SO c j) N && Nat.beq (SOI c (SO c j)) j &&
    (!(Nat.blt (Nat.add j 1) N) || Nat.blt (keyK PM (SO c j)) (keyK PM (SO c (Nat.add j 1)))))
    (Nat.add lo t)

@[expose] noncomputable def seK : Bool :=
  allN 3000 fun j => Nat.blt (f12 (SEPt 0) j) 3000 && Nat.beq (SEt j) (PC0 (f12 (SEPt 0) j))

@[expose] noncomputable def dinvK : Bool :=
  Nat.beq (DIt 0) I22 && allN 59 fun t => (fun i => Nat.beq (DIt i)
    (mmK (GDI (f12 (HDL.F 0) i)) (DIt (f12 (HDR.F 0) i)))) (Nat.add t 1)

@[expose] noncomputable def wordsK : Bool :=
  conjWordsM mmK I22 2 60 GD PD DIt CFSG.RankThree.Native.co2FiveSimpSel
    CFSG.RankThree.Native.co2FiveSimpW

@[expose] noncomputable def XL (j : ℕ) : ℕ :=
  nIf(Nat.beq j 0, AM 0, nIf(Nat.beq j 1, AM 1,
    mmK (mmK (AMI (Nat.add j 7)) (AM 1)) (AM (Nat.add j 7))))

@[expose] noncomputable def WT (r i : ℕ) : ℕ := f12 (WTt r) i

@[expose] noncomputable def qK : Bool :=
  allN 125 (fun k => Nat.beq (pwK (PQ k) 5) I22 && (Nat.beq (PQ k) I22 ||
    (Nat.blt (WT 0 k) 155 && Nat.beq (PQ k) (pwK (XL (Nat.div (WT 0 k) 5)) (Nat.mod (WT 0 k) 5))))) &&
  allN 31 (fun j => allN 31 fun j' => Nat.beq j j' || allN 5 fun e => !(Nat.beq (XL j) (pwK (XL j') e))) &&
  allN 31 (fun j => Nat.beq (pwK (XL j) 5) I22 && !(Nat.beq (XL j) I22) && Nat.blt (WT 1 j) 125 &&
    Nat.beq (PQ (WT 1 j)) (XL j))

@[expose] noncomputable def c0K : Bool :=
  allN 2 (fun k => comm (GC0 k) (AM 0)) &&
  allN 2 (fun k => Nat.blt (WT 2 k) 3000 && Nat.beq (PC0 (WT 2 k)) (GQ k)) &&
  allN 2 (fun k => allN 2 fun l => Nat.blt (WT 3 (Nat.add (Nat.mul 2 k) l)) 125 &&
    Nat.beq (PQ (WT 3 (Nat.add (Nat.mul 2 k) l))) (mmK (mmK (GC0I k) (GQ l)) (GC0 k))) &&
  allN 3000 (fun k => !(comm (PC0 k) (AM 4) && comm (PC0 k) (AM 5)) ||
    (List.range 5).any fun e => Nat.beq (PC0 k) (pwK (AM 0) e))

@[expose] noncomputable def BG : ℕ := mmK (mmK (AMI 7) (AMI 7)) (AM 6)

@[expose] noncomputable def BH : ℕ := mmK (mmK (mmK (AM 7) (AM 6)) (AM 7)) (AM 6)

@[expose] noncomputable def c1K : Bool :=
  allN 3 (fun k => comm (GC1 k) (AM 1)) &&
  Nat.beq (mmK BH BG) (mmK (mmK BG BH) (AM 7)) &&
  allN 3 (fun k => allN 2 fun l => Nat.blt (WT 4 (Nat.add (Nat.mul 2 k) l)) 60 &&
    Nat.beq (PD (WT 4 (Nat.add (Nat.mul 2 k) l))) (mmK (mmK (GC1I k) (GD l)) (GC1 k))) &&
  allN 3 (fun k => allN 3 fun l => Nat.blt (WT 5 (Nat.add (Nat.mul 3 k) l)) 60 &&
    Nat.beq (PD (WT 5 (Nat.add (Nat.mul 3 k) l)))
      (mmK (mmK (GC1I l) (GC1I k)) (mmK (GC1 l) (GC1 k)))) &&
  !(comm DG0 (AM 7)) &&
  allN 600 (fun k => !(comm (PC1 k) DG0 && comm (PC1 k) (AM 7)) ||
    (List.range 5).any fun e => Nat.beq (PC1 k) (pwK (AM 1) e))

end CertificateChecks.KernelMisc.Co2K

end
