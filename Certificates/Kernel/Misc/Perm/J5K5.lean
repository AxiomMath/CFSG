module

public import Certificates.Kernel.Misc.Perm.J5K
public import Certificates.Kernel.Misc.Perm.J5C5
public import Certificates.Data.Kernel.Misc.ChainTail
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Misc.ArrEnum

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.RankThree.PartOne
open CFSG.KC.Misc.Clos (allR)

theorem rsz5 : Nat.beq (j2FiveRS 5).size 8 = true := by quickRfl

theorem rbind5 : ∀ j < 8, arrBind (j2FiveRS 5)[j]! 315 9 (C5.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bsz5 : ((j2FiveRBase 5).map Fin.val).toArray.size = 4 := by decide +kernel

theorem bget5 : ∀ t < 4, ((j2FiveRBase 5).map Fin.val).toArray[t]! = pg 9 (mask 9) C5.BP t := by
  decide +kernel

theorem perm5 : allN 8 (fun j => permOK 315 9 (mask 9) (315 * 9) (C5.S j) (C5.SI j)) = true := by
  quickRfl

theorem gens5 : ∀ k < 3, permB 315 9 (C5.S k) = true ∧ permB 315 9 (GR k) = true ∧
    Nat.beq (C5.S k) (GR k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

@[expose] noncomputable def br5 (k : ℕ) : Bool :=
  ptailBranchK 315 9 C5.LR C5.TR C5.BP (LX 5) (pw (LX 5)) (j2FiveRRels 5) 300 C5P.F 4 k

theorem br5_0 : allR 0 63 br5 = true := by quickRfl
theorem br5_1 : allR 63 63 br5 = true := by quickRfl
theorem br5_2 : allR 126 63 br5 = true := by quickRfl
theorem br5_3 : allR 189 63 br5 = true := by quickRfl
theorem br5_4 : allR 252 63 br5 = true := by quickRfl

theorem lx5 : permB 315 9 (LX 5) = true := by quickRfl

theorem rels5 : relsK C5.BP (LX 5) 4 (j2FiveRRels 5) = true := by quickRfl

theorem bpt5 : ∀ t < 4, pg 9 (mask 9) C5.BP t < 315 := by decide +kernel

theorem rc5 : Nat.beq (rcnt (C5.LR 0)) 315 = true := by quickRfl

theorem cgs5 : (j2FiveCG 5).size = 3 := by decide

theorem comm5 : ∀ k < 3, permB 315 9 (CGP5 k) = true ∧
    Nat.beq (cm (CGP5 k) (LX 5)) (cm (LX 5) (CGP5 k)) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl⟩

theorem sift5 : ∀ k < 3, Nat.beq (Nat.shiftRight (CGP5 k) (315 * 9)) 0 = true ∧
    allN 315 (fun t => Nat.blt (pg 9 (mask 9) (CGP5 k) t) 315) = true ∧
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) C5.LR C5.TRI C5.BP 4 0 (CGP5 k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelMisc.J2F

end
