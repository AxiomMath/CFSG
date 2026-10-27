module

public import Certificates.Kernel.G24B.Checks733011
public import Certificates.Kernel.G24B.DData
public import Certificates.Data.G24IdentDC
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.G24B

open CFSG.KC.Misc.G24 CFSG.KC.F2BfsRec CFSG.KLie.CT CFSG.KC.M1F2 CFSG.Quasithin.St84.G24Ident

@[expose] noncomputable def dcNth {α : Type} (d : α) (L : List α) (i : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih i => Nat.rec (motive := fun _ => α) x (fun j _ => ih j) i) L i

@[expose] noncomputable def dcHead {α : Type} (d : α) (L : List α) : α :=
  List.rec (motive := fun _ => α) d (fun a _ _ => a) L

@[expose] noncomputable def dcTail {α : Type} (L : List α) : List α :=
  List.rec (motive := fun _ => List α) List.nil (fun _ t _ => t) L

@[expose] noncomputable def dcZipK {α : Type} (d : α) (f : Nat → α → Bool) (L : List Nat) :
    List α → Bool :=
  List.rec (motive := fun _ => List α → Bool) (fun _ => true)
    (fun x _ ih D => andB (f x (dcHead d D)) (ih (dcTail D))) L

@[expose] noncomputable def dcX (x : Nat) : Nat :=
  mulF2 28 (sortedAt 28 12 6 10 EQ2.CF (Nat.mod x 1024)) (repK rw (nthV dcI4 (Nat.div x 1024)))

@[expose] noncomputable def dcBit (M x : Nat) : Bool := Nat.blt 0 (Nat.land M (Nat.shiftLeft 1 x))

@[expose] noncomputable def dcMaskOf (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.lor (Nat.shiftLeft 1 x) ih) L

@[expose] noncomputable def dcPow (X e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (oneF2 28) (fun _ acc => mulF2 28 acc X) e

@[expose] noncomputable def dcIn4 (i : Nat) : Bool :=
  orB (Nat.beq i (nthV dcI4 0)) (orB (Nat.beq i (nthV dcI4 1))
    (orB (Nat.beq i (nthV dcI4 2)) (Nat.beq i (nthV dcI4 3))))

@[expose] noncomputable def dcCosK (gp : List Nat) : Bool :=
  andB (allN 4 fun c => Nat.blt (nthV dcI4 c) 36)
    (allN 36 fun i => bIf(dcIn4 i, true, strictB (repK rw i) fun R =>
      gapK 28 12 6 10 EQ2.CF 1024 (nthV gp i) (mulF2 28 R R)))

@[expose] noncomputable def dcHK : Bool :=
  allN 3 fun s => allN 3 fun t =>
    Nat.beq (nthV dcHm (Nat.add (Nat.mul 3 s) t)) (mulF2 28 (dcPow (blowW k1) s) (dcPow (blowW k2) t))

@[expose] def dcWords : List (List (List Nat)) :=
  CFSG.Quasithin.St84.G24DC.wWords.map fun row => row.map fun w => w.map fun l => 2 * l.val

@[expose] noncomputable def dcRowK (wr : List (List Nat)) : Bool :=
  andB (dcWl == dcWords)
    (allN 12 fun i => allN 4 fun k =>
      Nat.beq (nthV (nthL wr i) k) (wordF4 gK (nthL (nthLL dcWl i) k)))

@[expose] noncomputable def dcLet (im : List Nat) (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nthV im (Nat.div c 2))
    (mulF2 28 (nthV im (Nat.div c 2)) (nthV im (Nat.div c 2))) (Nat.beq (Nat.mod c 2) 1)

@[expose] noncomputable def dcEvS (im : List Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (oneF2 28) (fun c _ ih => mulF2 28 (dcLet im c) ih) w

@[expose] noncomputable def dcRelsK : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun r _ ih => andB (Nat.beq (dcEvS gK r) (oneF2 28)) ih) dcRl

@[expose] noncomputable def dcXcK (im : List Nat) : Bool :=
  strictB (dcEvS im dcXh) fun W => Nat.beq (mulF2 28 W W) (oneF2 28)

@[expose] noncomputable def dcMaskK : Bool :=
  allN 8 fun a => Nat.beq (dcMaskOf (nthL dcCl a)) (nthV dcCm a)

@[expose] noncomputable def dcScanK (cm : List Nat) (lo n : Nat) : Bool :=
  allN n fun i => strictB (dcX (Nat.add lo i)) fun X =>
    bIf(ord2K X, allN 8 fun a =>
      bIf(commK X (nthV dcHm (Nat.succ a)), dcBit (nthV cm a) (Nat.add lo i), true), true)

@[expose] noncomputable def dcLt8 (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => andB (Nat.blt c 8) ih) w

@[expose] noncomputable def dcLt8L (L : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w _ ih => andB (dcLt8 w) ih) L

@[expose] noncomputable def dcDec4K (im : List Nat) (d : Nat) (row : List Nat) (ws : List (List Nat))
    (hW : Nat) : Bool :=
  andB (Nat.blt d 4) (allN 4 fun k =>
    strictB (mulF2 28 (mulF2 28 hW (nthV row k)) (mulF2 28 hW hW)) fun T =>
      bIf(Nat.beq d 0, Nat.beq (nthV im k) T,
        andB (dcLt8 (nthL ws k)) (andB (Nat.beq (wordF4 gK (nthL ws k)) (nthV im k))
          (Nat.beq (wordF4 (nthL dcWr d) (nthL ws k)) T))))

@[expose] noncomputable def dcDecK (im : List Nat) (f : Nat) (ws : List (List Nat)) : Bool :=
  dcDec4K im (Nat.div f 72) (nthL dcWr (Nat.add 4 (Nat.mod (Nat.div f 9) 8))) ws
    (mulF2 28 (dcPow (nthV (nthL dcWr (Nat.add 4 (Nat.mod (Nat.div f 9) 8))) 0) (Nat.mod (Nat.div f 3) 3))
      (dcPow (nthV (nthL dcWr (Nat.add 4 (Nat.mod (Nat.div f 9) 8))) 1) (Nat.mod f 3)))

@[expose] noncomputable def dcRecK (im : List Nat) (r : Nat × List (List Nat)) : Bool :=
  bIf(Nat.blt r.1 12,
    bIf(Nat.beq r.1 0, dcXcK im,
      notB (Nat.beq (dcEvS im (nthL dcRl (Nat.sub r.1 1))) (oneF2 28))),
    dcDecK im (Nat.sub r.1 12) r.2)

@[expose] noncomputable def dcDet (a b : Nat) : Bool :=
  notB (Nat.beq (Nat.mod (Nat.mul (Nat.div a 3) (Nat.mod b 3)) 3)
    (Nat.mod (Nat.mul (Nat.mod a 3) (Nat.div b 3)) 3))

@[expose] noncomputable def dcPairK (a b : Nat) (D : List (List (Nat × List (List Nat)))) : Bool :=
  strictB (nthV dcHm a) fun Ha => strictB (nthV dcHm b) fun Hb =>
    dcZipK List.nil (fun x Dx => strictB (dcX x) fun Xx =>
      dcZipK (0, List.nil) (fun y r => strictB (dcX y) fun Xy => dcRecK [Ha, Hb, Xx, Xy] r)
        (nthL dcCl (Nat.sub b 1)) Dx) (nthL dcCl (Nat.sub a 1)) D

@[expose] noncomputable def dcCandK (dd : List (List (List (Nat × List (List Nat))))) (a : Nat) : Bool :=
  allN 9 fun b => bIf(dcDet a b, dcPairK a b (dcNth List.nil dd (Nat.add (Nat.mul 9 a) b)), true)

theorem ch733007_cos : dcCosK dcGp = true := by quickRfl
theorem ch733007_h : dcHK = true := by quickRfl
theorem ch733007_rows : dcRowK dcWr = true := by quickRfl
theorem ch733007_rels : dcRelsK = true := by quickRfl
theorem ch733007_letters : andB (dcLt8L dcRl) (dcLt8 dcXh) = true := by quickRfl
theorem ch733007_xc : notB (dcXcK gK) = true := by quickRfl
theorem ch733007_mask : dcMaskK = true := by quickRfl

theorem ch733007_scan0 : dcScanK dcCm (512 * 0) 512 = true := by quickRfl
theorem ch733007_scan1 : dcScanK dcCm (512 * 1) 512 = true := by quickRfl
theorem ch733007_scan2 : dcScanK dcCm (512 * 2) 512 = true := by quickRfl
theorem ch733007_scan3 : dcScanK dcCm (512 * 3) 512 = true := by quickRfl
theorem ch733007_scan4 : dcScanK dcCm (512 * 4) 512 = true := by quickRfl
theorem ch733007_scan5 : dcScanK dcCm (512 * 5) 512 = true := by quickRfl
theorem ch733007_scan6 : dcScanK dcCm (512 * 6) 512 = true := by quickRfl
theorem ch733007_scan7 : dcScanK dcCm (512 * 7) 512 = true := by quickRfl

theorem ch733007_cand1 : dcCandK dcDd 1 = true := by quickRfl
theorem ch733007_cand2 : dcCandK dcDd 2 = true := by quickRfl
theorem ch733007_cand3 : dcCandK dcDd 3 = true := by quickRfl
theorem ch733007_cand4 : dcCandK dcDd 4 = true := by quickRfl
theorem ch733007_cand5 : dcCandK dcDd 5 = true := by quickRfl
theorem ch733007_cand6 : dcCandK dcDd 6 = true := by quickRfl
theorem ch733007_cand7 : dcCandK dcDd 7 = true := by quickRfl
theorem ch733007_cand8 : dcCandK dcDd 8 = true := by quickRfl

end CFSG.KD.G24B

end
