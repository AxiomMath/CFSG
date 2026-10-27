module

public import Certificates.Kernel.Misc.Perm.J5K
public import Certificates.Kernel.Misc.Perm.J5C4
public import Certificates.Data.Kernel.Misc.ChainTail
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Misc.ArrEnum

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.RankThree.PartOne
open CFSG.KC.Misc.Clos (allR)

theorem rsz4 : Nat.beq (j2FiveRS 4).size 7 = true := by quickRfl

theorem rbind4 : ∀ j < 7, arrBind (j2FiveRS 4)[j]! 315 9 (C4.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bsz4 : ((j2FiveRBase 4).map Fin.val).toArray.size = 4 := by decide +kernel

theorem bget4 : ∀ t < 4, ((j2FiveRBase 4).map Fin.val).toArray[t]! = pg 9 (mask 9) C4.BP t := by
  decide +kernel

theorem perm4 : allN 7 (fun j => permOK 315 9 (mask 9) (315 * 9) (C4.S j) (C4.SI j)) = true := by
  quickRfl

theorem gens4 : ∀ k < 3, permB 315 9 (C4.S k) = true ∧ permB 315 9 (GR k) = true ∧
    Nat.beq (C4.S k) (GR k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

@[expose] noncomputable def br4 (k : ℕ) : Bool :=
  ptailBranchK 315 9 C4.LR C4.TR C4.BP (LX 4) (pw (LX 4)) (j2FiveRRels 4) 50 C4P.F 4 k

theorem br4_0 : allR 0 63 br4 = true := by quickRfl
theorem br4_1 : allR 63 63 br4 = true := by quickRfl
theorem br4_2 : allR 126 63 br4 = true := by quickRfl
theorem br4_3 : allR 189 63 br4 = true := by quickRfl
theorem br4_4 : allR 252 63 br4 = true := by quickRfl

theorem lx4 : permB 315 9 (LX 4) = true := by quickRfl

theorem rels4 : relsK C4.BP (LX 4) 4 (j2FiveRRels 4) = true := by quickRfl

theorem bpt4 : ∀ t < 4, pg 9 (mask 9) C4.BP t < 315 := by decide +kernel

theorem rc4 : Nat.beq (rcnt (C4.LR 0)) 315 = true := by quickRfl

theorem cgs4 : (j2FiveCG 4).size = 3 := by decide

theorem comm4 : ∀ k < 3, permB 315 9 (CGP4 k) = true ∧
    Nat.beq (cm (CGP4 k) (LX 4)) (cm (LX 4) (CGP4 k)) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl⟩

theorem sift4 : ∀ k < 3, Nat.beq (Nat.shiftRight (CGP4 k) (315 * 9)) 0 = true ∧
    allN 315 (fun t => Nat.blt (pg 9 (mask 9) (CGP4 k) t) 315) = true ∧
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) C4.LR C4.TRI C4.BP 4 0 (CGP4 k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelMisc.J2F

end
