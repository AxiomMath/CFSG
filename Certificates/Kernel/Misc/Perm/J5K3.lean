module

public import Certificates.Kernel.Misc.Perm.J5K
public import Certificates.Kernel.Misc.Perm.J5C3
public import Certificates.Data.Kernel.Misc.ChainTail
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Misc.ArrEnum

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.RankThree.PartOne
open CFSG.KC.Misc.Clos (allR)

theorem rsz3 : Nat.beq (j2FiveRS 3).size 7 = true := by quickRfl

theorem rbind3 : ∀ j < 7, arrBind (j2FiveRS 3)[j]! 315 9 (C3.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bsz3 : ((j2FiveRBase 3).map Fin.val).toArray.size = 4 := by decide +kernel

theorem bget3 : ∀ t < 4, ((j2FiveRBase 3).map Fin.val).toArray[t]! = pg 9 (mask 9) C3.BP t := by
  decide +kernel

theorem perm3 : allN 7 (fun j => permOK 315 9 (mask 9) (315 * 9) (C3.S j) (C3.SI j)) = true := by
  quickRfl

theorem gens3 : ∀ k < 3, permB 315 9 (C3.S k) = true ∧ permB 315 9 (GR k) = true ∧
    Nat.beq (C3.S k) (GR k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

@[expose] noncomputable def br3 (k : ℕ) : Bool :=
  ptailBranchK 315 9 C3.LR C3.TR C3.BP (LX 3) (pw (LX 3)) (j2FiveRRels 3) 300 C3P.F 4 k

theorem br3_0 : allR 0 63 br3 = true := by quickRfl
theorem br3_1 : allR 63 63 br3 = true := by quickRfl
theorem br3_2 : allR 126 63 br3 = true := by quickRfl
theorem br3_3 : allR 189 63 br3 = true := by quickRfl
theorem br3_4 : allR 252 63 br3 = true := by quickRfl

theorem lx3 : permB 315 9 (LX 3) = true := by quickRfl

theorem rels3 : relsK C3.BP (LX 3) 4 (j2FiveRRels 3) = true := by quickRfl

theorem bpt3 : ∀ t < 4, pg 9 (mask 9) C3.BP t < 315 := by decide +kernel

theorem rc3 : Nat.beq (rcnt (C3.LR 0)) 315 = true := by quickRfl

theorem cgs3 : (j2FiveCG 3).size = 2 := by decide

theorem comm3 : ∀ k < 2, permB 315 9 (CGP3 k) = true ∧
    Nat.beq (cm (CGP3 k) (LX 3)) (cm (LX 3) (CGP3 k)) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl⟩

theorem sift3 : ∀ k < 2, Nat.beq (Nat.shiftRight (CGP3 k) (315 * 9)) 0 = true ∧
    allN 315 (fun t => Nat.blt (pg 9 (mask 9) (CGP3 k) t) 315) = true ∧
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) C3.LR C3.TRI C3.BP 4 0 (CGP3 k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelMisc.J2F

end
