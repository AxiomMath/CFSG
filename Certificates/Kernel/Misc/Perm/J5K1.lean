module

public import Certificates.Kernel.Misc.Perm.J5K
public import Certificates.Kernel.Misc.Perm.J5C1
public import Certificates.Data.Kernel.Misc.ChainTail
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Misc.ArrEnum

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.RankThree.PartOne
open CFSG.KC.Misc.Clos (allR)

theorem rsz1 : Nat.beq (j2FiveRS 1).size 8 = true := by quickRfl

theorem rbind1 : ∀ j < 8, arrBind (j2FiveRS 1)[j]! 315 9 (C1.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bsz1 : ((j2FiveRBase 1).map Fin.val).toArray.size = 4 := by decide +kernel

theorem bget1 : ∀ t < 4, ((j2FiveRBase 1).map Fin.val).toArray[t]! = pg 9 (mask 9) C1.BP t := by
  decide +kernel

theorem perm1 : allN 8 (fun j => permOK 315 9 (mask 9) (315 * 9) (C1.S j) (C1.SI j)) = true := by
  quickRfl

theorem gens1 : ∀ k < 3, permB 315 9 (C1.S k) = true ∧ permB 315 9 (GR k) = true ∧
    Nat.beq (C1.S k) (GR k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

@[expose] noncomputable def br1 (k : ℕ) : Bool :=
  ptailBranchK 315 9 C1.LR C1.TR C1.BP (LX 1) (pw (LX 1)) (j2FiveRRels 1) 50 C1P.F 4 k

theorem br1_0 : allR 0 63 br1 = true := by quickRfl
theorem br1_1 : allR 63 63 br1 = true := by quickRfl
theorem br1_2 : allR 126 63 br1 = true := by quickRfl
theorem br1_3 : allR 189 63 br1 = true := by quickRfl
theorem br1_4 : allR 252 63 br1 = true := by quickRfl

theorem lx1 : permB 315 9 (LX 1) = true := by quickRfl

theorem rels1 : relsK C1.BP (LX 1) 4 (j2FiveRRels 1) = true := by quickRfl

theorem bpt1 : ∀ t < 4, pg 9 (mask 9) C1.BP t < 315 := by decide +kernel

theorem rc1 : Nat.beq (rcnt (C1.LR 0)) 315 = true := by quickRfl

theorem cgs1 : (j2FiveCG 1).size = 2 := by decide

theorem comm1 : ∀ k < 2, permB 315 9 (CGP1 k) = true ∧
    Nat.beq (cm (CGP1 k) (LX 1)) (cm (LX 1) (CGP1 k)) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl⟩

theorem sift1 : ∀ k < 2, Nat.beq (Nat.shiftRight (CGP1 k) (315 * 9)) 0 = true ∧
    allN 315 (fun t => Nat.blt (pg 9 (mask 9) (CGP1 k) t) 315) = true ∧
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) C1.LR C1.TRI C1.BP 4 0 (CGP1 k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelMisc.J2F

end
