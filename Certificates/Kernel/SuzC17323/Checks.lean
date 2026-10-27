module

public import Certificates.Kernel.SuzC17323.Enum
public import Certificates.Kernel.SuzPump.Pair
public import Certificates.Kernel.SuzThree13637.CEnum
public import Certificates.Data.Kernel.HeDihK
public import Certificates.Data.Kernel.K426K
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSuzC17323

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.B3S3K CFSG.KC.HeDih
open CFSG.KC.K426K CertificateChecks.KernelSpor CertificateChecks.KernelSuzPump
open CFSG.HardMathSupport.Dickson.I271.TabSuzC CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
open CFSG.RankThree.PartTwo.KFacts.K426 CFSG.KD.SuzThree13637

@[expose] noncomputable def TP : Nat := (reb tTuple).1

theorem nE : Nat.beq AE.N 360 = true ∧ Nat.beq AE.ng 2 = true ∧ Nat.beq SE.N 9 = true ∧
    Nat.beq SE.ng 2 = true := ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem rbA : ∀ k < 2, (reb aTuples[k]!).2.2 = true ∧ Nat.beq (reb aTuples[k]!).1 (AE.G k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl⟩

theorem rbS : ∀ k < 2, (reb sTuples[k]!).2.2 = true ∧ Nat.beq (reb sTuples[k]!).1 (SE.G k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl⟩

theorem rbY : (reb yTuple).2.2 = true ∧ Nat.beq (reb yTuple).1 (CE.G 0) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem rbT : (reb tTuple).2.2 = true := by quickRfl

theorem pAS : ∀ k < 2, permB 1782 11 (AE.G k) = true ∧ permB 1782 11 (SE.G k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl⟩

theorem pT : permB 1782 11 TP = true := by quickRfl

theorem siftAG : ∀ k < 2, Nat.beq (Nat.shiftRight (AE.G k) (1782 * 11)) 0 = true ∧
    allN 1782 (fun t => Nat.blt (pg 11 (mask 11) (AE.G k) t) 1782) = true ∧
    siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 (AE.G k) =
      true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem siftT : Nat.beq (Nat.shiftRight TP (1782 * 11)) 0 = true ∧
    allN 1782 (fun t => Nat.blt (pg 11 (mask 11) TP t) 1782) = true ∧
    siftK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) SuzC.LR SuzC.TRI SuzC.BP 6 0 TP = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem commY : ∀ k < 2, Nat.beq (cm 1782 11 (AE.G k) (CE.G 0)) (cm 1782 11 (CE.G 0) (AE.G k)) =
    true := by
  intro k hk
  interval_cases k <;> quickRfl

theorem derA : derivedLeK 1782 11 AE.N CE.ng AE.ng AE.T AE.S CE.G AE.G = true := by
  decide +kernel

theorem relA : j3tLiftRels.all (fun wd => Nat.beq (evalWK 1782 11 AE.G wd) (pidn 1782 11)) = true := by
  decide +kernel

theorem memS : allN SE.ng (fun l => memIdxK AE.N AE.T AE.S (SE.G l)) = true := by
  decide +kernel

theorem commS : Nat.beq (cm 1782 11 (SE.G 0) (SE.G 1)) (cm 1782 11 (SE.G 1) (SE.G 0)) = true := by
  quickRfl

theorem cubeS : ∀ l < 2, Nat.beq (pw 1782 11 (SE.G l) 3) (pidn 1782 11) = true := by
  intro l hl
  interval_cases l <;> quickRfl

theorem conjTA : ∀ l < 2, memIdxK AE.N AE.T AE.S (cj 1782 11 TP (AE.G l)) = true ∧
    memIdxK AE.N AE.T AE.S (cm 1782 11 (pinvS 1782 11 (mask 11) TP) (cm 1782 11 (AE.G l) TP)) =
      true := by
  intro l hl
  interval_cases l <;> exact ⟨by decide +kernel, by decide +kernel⟩

theorem conjTS : Nat.beq (cj 1782 11 TP (SE.G 0)) (SE.G 0) = true ∧
    Nat.beq (cj 1782 11 TP (SE.G 1)) (pw 1782 11 (SE.G 1) 2) = true :=
  ⟨by quickRfl, by quickRfl⟩

end CertificateChecks.KernelSuzC17323

end
