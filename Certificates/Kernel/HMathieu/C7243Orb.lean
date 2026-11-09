module

public import Certificates.Kernel.HMathieu.T24
public import Certificates.Data.Kernel.HMathieu.Normal
public import Certificates.Data.Kernel.HMathieu.PredHF
public import Certificates.Data.Kernel.HMathieu.FixTab
public meta import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000

public section

#kc_repo #kc_natBin CertificateChecks.KernelHMathieu.C7243Orb repsN
  "Certificates/Kernel/HMathieu/data/C7243.reps" 4512 1336653517506997215
#kc_repo #kc_natBin CertificateChecks.KernelHMathieu.C7243Orb masksN
  "Certificates/Kernel/HMathieu/data/C7243.masks" 18048 5943471071829788224
#kc_repo #kc_natBin CertificateChecks.KernelHMathieu.C7243Orb recsN
  "Certificates/Kernel/HMathieu/data/C7243.recs" 76522 8591353660969416561
#kc_repo #kc_natBin CertificateChecks.KernelHMathieu.C7243Orb rowsN
  "Certificates/Kernel/HMathieu/data/C7243.rows" 12224 5903499972924044110
#kc_repo #kc_natBin CertificateChecks.KernelHMathieu.C7243Orb gidxN
  "Certificates/Kernel/HMathieu/data/C7243.gidx" 128 3989742397135843949

namespace CertificateChecks.KernelHMathieu.C7243Orb

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu

@[expose] noncomputable def byte (N o : Nat) : Nat := Nat.land (Nat.shiftRight N (Nat.mul 8 o)) 255

@[expose] noncomputable def word (N o : Nat) : Nat :=
  Nat.land (Nat.shiftRight N (Nat.mul 8 o)) 65535

@[expose] noncomputable def repX (i : Nat) : Nat := byte repsN (Nat.mul 6 i)
@[expose] noncomputable def repRank (i : Nat) : Nat := byte repsN (Nat.add (Nat.mul 6 i) 1)
@[expose] noncomputable def repPar (i : Nat) : Nat := word repsN (Nat.add (Nat.mul 6 i) 2)
@[expose] noncomputable def repOff (i : Nat) : Nat := word repsN (Nat.add (Nat.mul 6 i) 4)

@[expose] noncomputable def mask (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight masksN (Nat.mul 192 i)) (2 ^ 192 - 1)

@[expose] noncomputable def rowSlice (r : Nat) : Nat :=
  Nat.land (Nat.shiftRight rowsN (Nat.mul 1528 r)) (2 ^ 1528 - 1)

@[expose] noncomputable def rowAt (r y : Nat) : Nat := byte (rowSlice r) y
@[expose] noncomputable def gAt (r : Nat) : Nat := word gidxN (Nat.mul 2 r)

@[expose] noncomputable def cmT (x : Nat) : Nat := (T24.rows.getD x (0, 0)).1
@[expose] noncomputable def mkT (x s : Nat) : Nat :=
  bif Nat.beq s 191 then x else byte (T24.rows.getD x (0, 0)).2 s

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def strictBo (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def mems : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, i => strictL (repX i) fun x => strictL (repPar i) fun p => x :: mems k p

@[expose] noncomputable def cmOf : Nat → Nat → Nat
  | 0, _ => 2 ^ 191 - 1
  | k + 1, i => Nat.land (cmT (repX i)) (cmOf k (repPar i))

@[expose] noncomputable def spanAdd (x S : Nat) : Nat :=
  (List.range 192).foldl (fun acc s => bif Nat.testBit S s then Nat.lor acc (2 ^ mkT x s) else acc) S

@[expose] noncomputable def rowOK (r : Nat) : Bool :=
  Nat.blt (gAt r) T24.E.length &&
    strictBo (T24.E.getD (gAt r) 0) fun g => strictBo (rowSlice r) fun R =>
      (List.range 191).all fun y => Nat.blt (byte R y) 192 &&
        Nat.beq (conjP g (T24.P.getD y 0)) (T24.P.getD (byte R y) 0)

@[expose] noncomputable def recOK (j : Nat) (l : List Nat) (x e : Nat) : Bool :=
  let r := Nat.land e 63
  let t := Nat.shiftRight e 6
  Nat.blt t 752 && Nat.beq (repRank t) (j + 1) &&
    strictBo (mask t) fun M => strictBo (rowSlice r) fun R =>
      (x :: l).all fun y => Nat.testBit M (byte R y)

@[expose] noncomputable def scan (j : Nat) (l : List Nat) (c S : Nat) : List Nat → Nat → Bool
  | [], _ => true
  | x :: xs, R =>
    bif Nat.testBit c x && !Nat.testBit S x then
      recOK j l x (Nat.land R 65535) && scan j l c S xs (Nat.shiftRight R 16)
    else scan j l c S xs R

@[expose] noncomputable def repRecs (i : Nat) : Nat :=
  Nat.land (Nat.shiftRight recsN (Nat.mul 16 (repOff i)))
    (2 ^ (Nat.mul 16 (repOff (i + 1) - repOff i)) - 1)

@[expose] noncomputable def structOK (i : Nat) : Bool :=
  bif Nat.beq i 0 then Nat.beq (repRank 0) 0 && Nat.beq (mask 0) (2 ^ 191)
  else
    let p := repPar i
    let x := repX i
    Nat.blt p i && Nat.beq (repRank i) (repRank p + 1) && Nat.blt x 191 &&
      Nat.testBit (cmOf (repRank p) p) x &&
      strictBo (mask p) fun S => !Nat.testBit S x && Nat.beq (mask i) (spanAdd x S)

@[expose] noncomputable def repOK (i : Nat) : Bool :=
  structOK i && (Nat.beq (repRank i) 6 ||
    strictBo (cmOf (repRank i) i) fun c => strictBo (mask i) fun S =>
      scan (repRank i) (mems (repRank i) i) c S (List.range 191) (repRecs i))

@[expose] noncomputable def blkOK (a n : Nat) : Bool := (List.range' a n).all repOK

@[expose] noncomputable def spanL : List Nat → List Nat
  | [] => [191]
  | x :: l => spanL l ++ (spanL l).map (mkT x)

@[expose] noncomputable def fixL : Nat → Nat → List Nat
  | 0, _ => List.range (2 ^ 11)
  | k + 1, i => strictL (repX i) fun x => strictL (repPar i) fun p =>
    (fixL k p).filter fun m => Nat.beq (actK (T24.Md.getD x []) m) m

@[expose] noncomputable def expOf (n : Nat) : Nat :=
  ((List.range 12).filter fun d => Nat.beq (2 ^ d) n).headD 12

theorem strictBo_eq_app (y : Nat) (k : Nat → Bool) : strictBo y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def normKF (E P L S : List Nat) : Bool :=
  E.all fun e => L.all fun a =>
    strictBo (conjP e (P.getD a 0)) fun v => (S.map fun s => P.getD s 0).contains v

theorem normKF_eq (E P L S : List Nat) : normKF E P L S = normK E P L S := by
  simp only [normKF, normK, strictBo_eq_app]

@[expose] noncomputable def predD (E P L S : List Nat) (d : Nat) : Bool :=
  let k := L.length
  (k == 0 || !decide (11 - d ≤ k + 1) || decide (7 ≤ 11 - d)) &&
    (k != 4 || decide (7 ≤ 11 - d)) && (k != 6 || (d % 2 == 0 && normKF E P L S))

@[expose] noncomputable def predOK (i : Nat) : Bool :=
  let n := (fixL (repRank i) i).length
  Nat.beq (2 ^ expOf n) n &&
    predD T24.E T24.P (mems (repRank i) i) (spanL (mems (repRank i) i)) (expOf n)

theorem predHF24K_eq_predD (E P L S : List Nat) (st : List (List Nat) × List Nat) {d : Nat}
    (h : st.2.length = 2 ^ d) : predHF24K E P L S st = predD E P L S d := by
  simp only [predHF24K, predD, normKF_eq, h, Nat.log_pow (by decide : 1 < 2) d]

@[expose] noncomputable def predBlk (a n : Nat) : Bool := (List.range' a n).all predOK

theorem r0 : (List.range' 0 16).all rowOK = true := by decide +kernel
theorem r1 : (List.range' 16 16).all rowOK = true := by decide +kernel
theorem r2 : (List.range' 32 16).all rowOK = true := by decide +kernel
theorem r3 : (List.range' 48 16).all rowOK = true := by decide +kernel

theorem b0 : blkOK 0 100 = true := by decide +kernel
theorem b1 : blkOK 100 100 = true := by decide +kernel
theorem b2 : blkOK 200 100 = true := by decide +kernel
theorem b3 : blkOK 300 100 = true := by decide +kernel
theorem b4 : blkOK 400 100 = true := by decide +kernel
theorem b5 : blkOK 500 100 = true := by decide +kernel
theorem b6 : blkOK 600 100 = true := by decide +kernel
theorem b7 : blkOK 700 52 = true := by decide +kernel

theorem p0 : predBlk 0 100 = true := by decide +kernel
theorem p1 : predBlk 100 100 = true := by decide +kernel
theorem p2 : predBlk 200 100 = true := by decide +kernel
theorem p3 : predBlk 300 100 = true := by decide +kernel
theorem p4 : predBlk 400 100 = true := by decide +kernel
theorem p5 : predBlk 500 100 = true := by decide +kernel
theorem p6 : predBlk 600 100 = true := by decide +kernel
theorem p7 : predBlk 700 50 = true := by decide +kernel
theorem p8 : predBlk 750 1 = true := by decide +kernel
theorem p9 : predBlk 751 1 = true := by decide +kernel

end CertificateChecks.KernelHMathieu.C7243Orb

end
