module

public import Certificates.Kernel.SporSch.Ly.BSData
public import CFSG.Sporadic.Schreier.LyCheckCover
import all Init.Data.Nat.Fold
import all Init.Data.Range.Basic
import all Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LyCv

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.Th.Native
open CertificateChecks.KernelSporSch.LyBS

theorem bB : Nat.beq (mul B B4) ONE = true := by quickRfl

theorem c0A : Nat.beq (mul A (CF 0)) (mul (CF 0) A) = true := by quickRfl
theorem c1A : Nat.beq (mul A (CF 1)) (mul (CF 1) A) = true := by quickRfl
theorem c0n1 : Bool.not (Nat.beq (CF 0) ONE) = true := by quickRfl
theorem c0nA : Bool.not (Nat.beq (CF 0) A) = true := by quickRfl

@[expose] noncomputable def carYK (i : Nat) : Nat :=
  wordR 5 12 1332 111 8 L H CM RM (CFx 12) (CIx 12) ONE
    (CFSG.Sporadic.LySchreier.carWordsL.getD i [])

@[expose] noncomputable def oneOrAK (X : Nat) : Bool := bIf(Nat.beq X ONE, true, Nat.beq X A)

@[expose] noncomputable def carSq (X : Nat) : Nat := mul X X

@[expose] noncomputable def carFoldK (w : List (Fin 9)) : Nat :=
  w.foldl (fun X n => mul X (carYK n.val)) ONE

@[expose] noncomputable def carPairK (i j : Nat) : Bool :=
  bIf(Nat.blt i j, oneOrAK (carSq (mul (carYK i) (carYK j))), true)

theorem carCube : allN 9 (fun i => oneOrAK (mul (carSq (carYK i)) (carYK i))) = true := by quickRfl
theorem carP0 : allN 9 (carPairK 0) = true := by quickRfl
theorem carP1 : allN 9 (carPairK 1) = true := by quickRfl
theorem carP2 : allN 9 (carPairK 2) = true := by quickRfl
theorem carP3 : allN 9 (carPairK 3) = true := by quickRfl
theorem carP4 : allN 9 (carPairK 4) = true := by quickRfl
theorem carP5 : allN 9 (carPairK 5) = true := by quickRfl
theorem carP6 : allN 9 (carPairK 6) = true := by quickRfl
theorem carP7 : allN 9 (carPairK 7) = true := by quickRfl
theorem carG0 :
    Nat.beq (carFoldK (CFSG.Sporadic.LySchreier.carGenWords 0)) (mul (CF 0) A) = true := by
  quickRfl
theorem carG1 : Nat.beq (carFoldK (CFSG.Sporadic.LySchreier.carGenWords 1)) (CF 1) = true := by
  quickRfl
theorem carZ : Nat.beq (carSq (mul (carYK 0) (carYK 1))) A = true := by quickRfl

end CertificateChecks.KernelSporSch.LyCv

end
