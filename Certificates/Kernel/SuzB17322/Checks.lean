module

public import Certificates.Kernel.SuzB17322.Enum
public import Certificates.Kernel.SuzB17322.Class
public import Certificates.Kernel.SuzB17322.Data
public import Certificates.Kernel.SuzPump.Pair
public import Certificates.Data.Kernel.HeDihK
public import Certificates.Data.Kernel.K426K
public import Certificates.Data.Kernel.Misc.CentHead
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSuzB17322

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.K426K
open CFSG.KC.CentSrch CFSG.KC.CentHead CertificateChecks.KernelSpor CertificateChecks.KernelSuzPump
open CFSG.HardMathSupport.Dickson.I271.TabSuzB CFSG.HardMathSupport.Dickson.I271.TabSuzFuse

@[expose] noncomputable def X : Nat := (reb xBTuple).1

@[expose] noncomputable def H (k : Nat) : Nat := (reb hT[k]!).1

@[expose] noncomputable def DP : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j ih => Nat.lor ih (Nat.shiftLeft (cm 1782 11 (pw 1782 11 X (Nat.mod (Nat.succ j) 3))
      (pw 1782 11 X (Nat.div (Nat.succ j) 3))) (Nat.mul (Nat.mul 1782 11) j))) 8

@[expose] noncomputable def bits (M k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i ih => Nat.add ih (Nat.land (Nat.shiftRight M i) (nat_lit 1))) k

theorem nE : Nat.beq AE.N 729 = true ∧ Nat.beq AE.ng 4 = true ∧ Nat.beq QE.N 16 = true ∧
    Nat.beq QE.ng 3 = true ∧ Nat.beq BE.N 81 = true ∧ Nat.beq BE.ng 4 = true ∧
    Nat.beq KC.N 432 = true ∧ Nat.beq KC.ng 2 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl, by quickRfl,
    by quickRfl⟩

theorem rbA : ∀ k < 4, (reb aTuples[k]!).2.2 = true ∧ Nat.beq (reb aTuples[k]!).1 (AE.G k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl⟩

theorem rbX : (reb xBTuple).2.2 = true := by quickRfl

theorem rbH : ∀ k < 9, (reb hT[k]!).2.2 = true := by
  intro k hk
  interval_cases k <;> quickRfl

theorem bindC : (∀ k < 3, Nat.beq (H (k + 1)) (QE.G k) = true) ∧ Nat.beq (H 4) (BE.G 0) = true ∧
    (∀ k < 3, Nat.beq (H (k + 6)) (BE.G (k + 1)) = true) ∧ Nat.beq (H 5) (KC.G 0) = true ∧
    Nat.beq (H 2) (KC.G 1) = true ∧ Nat.beq (H 4) (KC.T KC.r0) = true := by
  refine ⟨fun k hk => ?_, by quickRfl, fun k hk => ?_, by quickRfl, by quickRfl, by quickRfl⟩
  · interval_cases k <;> quickRfl
  · interval_cases k <;> quickRfl

theorem pXH : permB 1782 11 X = true ∧ ∀ k < 9, permB 1782 11 (H k) = true := by
  refine ⟨by quickRfl, fun k hk => ?_⟩
  interval_cases k <;> quickRfl

theorem siftAG : ∀ k < 4, Nat.beq (Nat.shiftRight (AE.G k) (1782 * 11)) 0 = true ∧
    allN 1782 (fun t => Nat.blt (pg 11 (mask 11) (AE.G k) t) 1782) = true ∧
    siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 (AE.G k) =
      true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftH : ∀ k < 6, Nat.beq (Nat.shiftRight (H k) (1782 * 11)) 0 = true ∧
    allN 1782 (fun t => Nat.blt (pg 11 (mask 11) (H k) t) 1782) = true ∧
    siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 (H k) =
      true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem commA : ∀ k < 4, Nat.beq (cm 1782 11 (AE.G k) X) (cm 1782 11 X (AE.G k)) = true := by
  intro k hk
  interval_cases k <;> quickRfl

theorem commH : ∀ k < 6, Nat.beq (cm 1782 11 (H k) X) (cm 1782 11 X (H k)) = true := by
  intro k hk
  interval_cases k <;> quickRfl

theorem memX : memIdxK AE.N AE.T AE.S X = true := by decide +kernel

theorem memB : ∀ k < 4, memIdxK AE.N AE.T AE.S (BE.G k) = true := by
  intro k hk
  interval_cases k <;> decide +kernel

theorem commB : ∀ k < 4, Nat.beq (cm 1782 11 (BE.G k) (H 4)) (cm 1782 11 (H 4) (BE.G k)) = true := by
  intro k hk
  interval_cases k <;> quickRfl

theorem normA : ∀ k < 4, ∀ l < 4, memIdxK AE.N AE.T AE.S (cj 1782 11 (H k) (AE.G l)) = true := by
  intro k hk l hl
  interval_cases k <;> interval_cases l <;> decide +kernel

theorem gOut : allN AE.N (fun i => !(Nat.beq (AE.T i) (H 0))) = true := by quickRfl

theorem gCube : Nat.beq (pw 1782 11 (H 0) 3) (pidn 1782 11) = true := by quickRfl

theorem head : headK 1782 11 SuzC.LR SuzC.TRI X (pw 1782 11 X 2) D.LM = true := by quickRfl

theorem headCnt : Nat.beq (bits D.LM 1782) 324 = true ∧
    Nat.beq (Nat.shiftRight D.LM 1782) 0 = true := ⟨by quickRfl, by quickRfl⟩

theorem dX : dOK 1782 11 X X DP = true := by quickRfl

theorem plan : planOK 1782 11 6 SuzC.BP DP [2, 2, 2] 3 = true := by quickRfl

theorem idPre : idPrefixOK 1782 11 SuzC.LR SuzC.TR SuzC.BP 3 = true := by quickRfl

theorem tail : Nat.beq (srch 1782 11 6 SuzC.LR SuzC.TR SuzC.TRI SuzC.BP DP [X, X] [2, 2, 2] 3
    (idWord 1782 11 SuzC.LR SuzC.BP 3) (idImgs 11 SuzC.BP 3)) 108 = true := by quickRfl

end CertificateChecks.KernelSuzB17322

end
