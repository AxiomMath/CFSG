module

public import Certificates.Kernel.Sporadic.ON8.Data
public import Certificates.Kernel.Sporadic.ON.Span
public import Certificates.Kernel.Sporadic.ON3.Small
public import Certificates.Data.Kernel.Spor.ImgEnum
public import Certificates.Kernel.Sporadic.ON5.Data

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON8

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.IE CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.ONSchreier
open CertificateChecks.KernelSpor.ON3 (ZT QT CT CIT DT M2T M3T mG trW bposK blkK)

@[expose] noncomputable def sp (t : Nat) : Nat := List.getD CertificateChecks.KernelSpor.ON.SP t 0

@[expose] noncomputable def dcK (j x : Nat) : Nat := CIT (DT j (CT x))

@[expose] noncomputable def dIK (j x : Nat) : Nat := trW (Nat.add (nat_lit 26) j) x

@[expose] noncomputable def dcIK (j x : Nat) : Nat := CIT (dIK j (CT x))

@[expose] noncomputable def hIK (x : Nat) : Nat := trW (nat_lit 30) x

@[expose] noncomputable def dhG (j x : Nat) : Nat := nIf(Nat.blt j 4, dcK j x, M2T x)

@[expose] noncomputable def dhI (j x : Nat) : Nat := nIf(Nat.blt j 4, dcIK j x, hIK x)

@[expose] noncomputable def wDH (k x : Nat) : Nat := trace dhG dhI (ON8W.WC k) (ON8W.WL k) x

@[expose] noncomputable def hGK (i x : Nat) : Nat := wDH i x

@[expose] noncomputable def mLK (x : Nat) : Nat := wDH (nat_lit 4) x

@[expose] noncomputable def mwK (j x : Nat) : Nat := wDH (Nat.add (nat_lit 5) j) x

@[expose] noncomputable def vK (x : Nat) : Nat := CIT (ZT (CT x))

@[expose] noncomputable def qK (k x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ acc => QT acc) k

@[expose] noncomputable def PD (i : Nat) : Nat := tab ON8T.PD i
@[expose] noncomputable def LD (i : Nat) : Nat := tab ON8T.LD i
@[expose] noncomputable def IDf (i : Nat) : Nat := tab ON8T.ID i
@[expose] noncomputable def QD (i : Nat) : Nat := tab ON8T.QD i
@[expose] noncomputable def PH (i : Nat) : Nat := tab ON8T.PH i
@[expose] noncomputable def LH (i : Nat) : Nat := tab ON8T.LH i
@[expose] noncomputable def IHf (i : Nat) : Nat := tab ON8T.IH i
@[expose] noncomputable def QH (i : Nat) : Nat := tab ON8T.QH i

@[expose] noncomputable def eD (k x : Nat) : Nat := eltR dcK PD LD k k x

@[expose] noncomputable def eH (k x : Nat) : Nat := eltR hGK PH LH k k x

@[expose] noncomputable def flD : Nat := List.getD FL 0 0
@[expose] noncomputable def flH : Nat := List.getD FL 1 0

@[expose] noncomputable def dSl (s : Nat) : Bool :=
  ieSl dcK sp IDf PD LD QD 4 144 (Nat.mul s 16) 16

@[expose] noncomputable def hSl (s : Nat) : Bool :=
  ieSl hGK sp IHf PH LH QH 4 144 (Nat.mul s 16) 16

@[expose] noncomputable def dDist : Bool := bAnd(Nat.ble flD 154, distK (fpK IDf flD) 144)

@[expose] noncomputable def hDist : Bool := bAnd(Nat.ble flH 154, distK (fpK IHf flH) 144)

@[expose] noncomputable def cjI (k t : Nat) : Nat := M2T (eD k (hIK (sp t)))

@[expose] noncomputable def cjF (k : Nat) : Nat := fpF (cjI k) flD

@[expose] noncomputable def aAt (k : Nat) : Bool :=
  strictB (tab ON8T.AS k) fun a => bIf(Nat.beq a 0,
    strictB (cjF k) fun f => allN 144 fun u => Bool.not (Nat.beq f (fpK IDf flD u)),
    bAnd(Nat.ble a 144, allN 154 fun t => Nat.beq (cjI k t) (imgAt IDf (Nat.sub a 1) t)))

@[expose] noncomputable def aSl (s : Nat) : Bool := allN 16 fun d => aAt (Nat.add (Nat.mul s 16) d)

@[expose] noncomputable def asl (i : Nat) : Nat := List.getD ASL i 0

@[expose] noncomputable def bpt (b : Nat) : Nat :=
  nIf(Nat.beq b 0, nat_lit 0, nIf(Nat.beq b 1, nat_lit 227759, nat_lit 100817))

@[expose] noncomputable def hvhvK (x : Nat) : Nat := hIK (vK (M2T (vK x)))

@[expose] noncomputable def it7 (c p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ acc => M2T (eH c acc)) (nat_lit 7)

@[expose] noncomputable def tAt (c : Nat) : Bool :=
  strictB (tab ON8T.HT c) fun g => bIf(Nat.beq g 0,
    allN 154 (fun t => Nat.beq (imgAt IHf c t) (sp t)),
    bIf(Nat.beq g 1, allN 154 (fun t => Nat.beq (imgAt IHf c t) (hvhvK (sp t))),
      bAnd(Nat.blt (Nat.sub g 2) 3,
        Bool.not (Nat.beq (it7 c (bpt (Nat.sub g 2))) (bpt (Nat.sub g 2))))))

@[expose] noncomputable def tSl (s : Nat) : Bool := allN 16 fun d => tAt (Nat.add (Nat.mul s 16) d)

@[expose] noncomputable def onP (F G : Nat → Nat) : Bool :=
  allN 154 fun t => Nat.beq (F (sp t)) (G (sp t))

@[expose] noncomputable def wit (i : Nat) : Nat := List.getD WIT i 0

@[expose] noncomputable def neAt (F G : Nat → Nat) (i : Nat) : Bool :=
  strictB (wit i) fun x => bAnd(Nat.blt x 245520, Bool.not (Nat.beq (F x) (G x)))

@[expose] noncomputable def nePair (m : Nat) (F G : Nat → Nat → Nat) (i : Nat) : Bool :=
  strictB (wit i) fun j => strictB (wit (Nat.succ i)) fun x =>
    bAnd(Nat.blt j m, bAnd(Nat.blt x 245520, Bool.not (Nat.beq (F j x) (G j x))))

@[expose] noncomputable def relOK : Bool :=
  bAnd(allN 5 (fun j => onP (fun x => dhI j (dhG j x)) (fun x => x)),
  bAnd(allN 3 (fun j => onP (mwK j) (mG j)),
  bAnd(onP (fun x => Nat.rec (motive := fun _ => Nat) x (fun _ acc => M2T acc) (nat_lit 7))
    (fun x => x),
  bAnd(onP (fun x => vK (vK x)) (fun x => x),
  bAnd(allN 4 (fun j => onP (fun x => vK (dcK j x)) (fun x => dcK j (vK x))),
  bAnd(onP ZT (fun x => QT (QT x)),
    allN 4 fun i => allN 4 fun a =>
      onP (fun x => hGK i (eD (asl a) x)) (fun x => eD (asl a) (hGK i x))))))))

@[expose] noncomputable def witOK : Bool :=
  bAnd(neAt vK (fun x => x) 0, bAnd(neAt vK ZT 1, bAnd(neAt (fun x => vK (M2T x)) (fun x => M2T (vK x)) 2,
  bAnd(nePair 3 (fun j x => QT (mG j x)) (fun j x => mG j (QT x)) 3,
  bAnd(nePair 3 (fun j x => qK 3 (mG j x)) (fun j x => mG j (qK 3 x)) 5,
  bAnd(nePair 4 (fun j x => QT (dcK j x)) (fun j x => dcK j (QT x)) 7,
  bAnd(nePair 4 (fun j x => qK 3 (dcK j x)) (fun j x => dcK j (qK 3 x)) 9,
  bAnd(nePair 4 (fun j x => QT (eD (asl j) x)) (fun j x => eD (asl j) (QT x)) 11,
  bAnd(nePair 4 (fun j x => qK 3 (eD (asl j) x)) (fun j x => eD (asl j) (qK 3 x)) 13,
    allN 4 fun k => nePair 4 (fun j x => mLK (qK k (eD (asl j) x)))
      (fun j x => eD (asl j) (mLK (qK k x))) (Nat.add 15 (Nat.mul 2 k)))))))))))

@[expose] noncomputable def abF (i x : Nat) : Nat := nIf(Nat.blt i 4, eD (asl i) x, mLK x)

@[expose] noncomputable def abK (i b : Nat) : Nat :=
  bposK (abF i (Data.quotientBlocks[b]!)[0]!)

@[expose] noncomputable def abP (i : Nat) : Nat := List.getD AB i 0

@[expose] noncomputable def blkOK : Bool :=
  bAnd(Nat.beq (List.length ASL) 4, bAnd(Nat.beq (List.length AB) 5,
  bAnd(allN 5 (fun i => bAnd(blkK (abF i) (abK i), bAnd(canonK 120 7 (mask 7) 840 (abP i),
    allN 120 fun b => Nat.beq (abK i b) (pg 7 (mask 7) (abP i) b)))),
    allN 4 fun a => Nat.beq (pcomp 120 7 (mask 7) (abP 4) (abP a))
      (pcomp 120 7 (mask 7) (abP a) (abP 4)))))

@[expose] noncomputable def qA (i : Nat) : Bool :=
  strictB (ON5M.T i) fun t => allN 4 fun a =>
    Nat.beq (pcomp 120 7 (mask 7) t (abP a)) (pcomp 120 7 (mask 7) (abP a) t)

@[expose] noncomputable def mselIn (s : Nat) : List Nat :=
  MSel.filter fun i => decide (2016 * s ≤ i) && decide (i < 2016 * s + 2016)

@[expose] noncomputable def mSel (s : Nat) : Bool := selFrom qA 2016 (Nat.mul s 2016) (mselIn s)

end CertificateChecks.KernelSpor.ON8

end
