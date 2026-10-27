
module

public import Certificates.Kernel.SporSch.J4S.Eta
public import Certificates.Kernel.SporSch.J4S.Orbits
public import Certificates.Kernel.SporSch.J4S.FiveT
public import CFSG.Certificates.Kernel.SporSch.J4SPowSound
public import CFSG.Certificates.Kernel.SporSch.J4SFormSound
public import CFSG.Sporadic.Schreier.J4SOddData
meta import Certificates.Kernel.SporSch.J4S.OddData
import CFSG.Certificates.Kernel.Common.Harness
import Init.Data.Nat.Fold
import Init.Data.Range.Basic
import Init.Data.Array.Basic
public import CFSG.Sporadic.Schreier.J4SCommGenBase
public import CFSG.Sporadic.Schreier.J4SPrimes
meta import CFSG.Sporadic.Schreier.J4SCommGenBase
meta import CFSG.Sporadic.Schreier.J4SPrimes
meta import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option maxRecDepth 400000

#kss_pairs CertificateChecks.KernelSporSch.J4CP CertificateChecks.KernelSporSch.J4Odd.certPairs
#kss_pairs CertificateChecks.KernelSporSch.J4EE CertificateChecks.KernelSporSch.J4Odd.eRowsA
#kss_pairs CertificateChecks.KernelSporSch.J4CS CertificateChecks.KernelSporSch.J4Odd.csA

namespace CertificateChecks.KernelSporSch.J4Odd

open CFSG.KC.Enum CFSG.KS CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Eta

@[expose] noncomputable def pathAppK (w : List Nat) (a : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun m _ ih a => ih (CFSG.KS.SporSch.C11.appK (J4G1 (Nat.sub m 1)) a)) w a

@[expose] noncomputable def pvK (p : Nat × List (List Nat)) : List Nat :=
  Prod.rec (motive := fun _ => List Nat) (fun a ws =>
    List.rec (motive := fun _ => List Nat) List.nil (fun w _ ih => List.cons (pathAppK w a) ih) ws) p

@[expose] noncomputable def cmK (l : Nat) : Nat :=
  Prod.rec (motive := fun _ => Nat) (fun a b => Nat.xor a (CFSG.KS.SporSch.C11.appK (J4GC b) a))
    (commPairs.getD l (0, 0))

@[expose] noncomputable def uK (l : Nat) : Bool :=
  bAnd(canonJ pad (getN one J4CP (Nat.add 10 l)), allN 112 (fun j =>
    Nat.beq (rowJ rm (getN one J4CP (Nat.add 10 l)) j) ((List.range colSel.size).foldl
      (fun acc c => if colSel[c]! = (l, j) then acc ||| 2 ^ c else acc) 0)))

@[expose] noncomputable def csK (ls : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (getN one J4EE 0) (fun l _ ih =>
    Nat.xor (Nat.xor (mulJ c rm (getN one J4CP l) (getN one J4CP (Nat.add 10 l)))
      (getN one J4CP (Nat.add 10 l))) ih) ls

end CertificateChecks.KernelSporSch.J4Odd

#kss_slices CertificateChecks.KernelSporSch.J4US CertificateChecks.KernelSporSch.J4Odd.uK 1 10

namespace CertificateChecks.KernelSporSch.J4Odd

open CFSG.KC.Enum CFSG.KS CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B
open CFSG.Sporadic.J4Schreier CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.J4Eta

theorem a1 : Nat.beq (CFSG.KS.SporSch.C11.powKF 32 (J4XY.W a276Word) 11)
    CFSG.KS.SporSch.C11.pidK = true := by quickRfl
theorem a2 : Nat.beq (CFSG.KS.SporSch.C11.appK (J4XY.W a276Word) 14) 14 = true := by quickRfl
theorem a3 : allN 2048 (fun n => bIf(Nat.beq (CFSG.KS.SporSch.C11.appK (J4XY.W a276Word) n) n,
    bIf(Nat.beq n 0, true, Nat.beq n 14), true)) = true := by quickRfl

theorem spans : List.rec (motive := fun _ => Bool) true
    (fun p _ ih => bAnd(CFSG.KS.SporSch.C11.spanK (pvK p), ih)) wPaths = true := by quickRfl

theorem gfix : allN 4 (fun i => Nat.beq (CFSG.KS.SporSch.C11.appK (J4GC i) 1) 1) = true := by
  quickRfl

theorem mk : allN 10 (fun l => Nat.beq (prodSK c rm one (es (cmK l))) (getN one J4CP l)) = true := by
  quickRfl

theorem ek : bAnd(canonJ pad (getN one J4EE 0), allN 112 (fun r =>
    Nat.beq (rowJ rm (getN one J4EE 0) r)
      ((if r = unitCols.1 then 2 ^ 110 else 0) ||| (if r = unitCols.2 then 2 ^ 111 else 0)))) =
    true := by quickRfl

theorem ti : packNK tInvRows.toList (getN one J4EE 1) = true := by quickRfl

theorem cs : Nat.beq (csK [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]) (getN one J4CS 0) = true := by quickRfl

theorem fin : Nat.beq (mulJ c rm (getN one J4CS 0) (getN one J4EE 1)) one = true := by quickRfl

theorem wset : wSet.length = 16 ∧ wSet.Nodup ∧ (∀ a ∈ wSet, a < 2048) ∧
    ∀ a ∈ wSet, ∀ b ∈ wSet, a ^^^ b ∈ wSet := by decide +kernel

theorem misc : (rootBits = tInvRows[110]! ∨ rootBits = tInvRows[111]! ∨
      rootBits = tInvRows[110]! ^^^ tInvRows[111]!) ∧
    (∀ p ∈ commPairs, p.1 < 2048 ∧ p.2 < 4) ∧ rootBits ≠ 0 ∧ rootBits < 2 ^ 112 ∧
    commPairs.length = 10 := by decide +kernel

theorem pathLetters : ∀ p ∈ wPaths, ∀ w ∈ p.2, ∀ m ∈ w, 1 ≤ m ∧ m < 9 := by decide +kernel

end CertificateChecks.KernelSporSch.J4Odd

end
