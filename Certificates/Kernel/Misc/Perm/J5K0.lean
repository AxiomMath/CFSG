module

public import Certificates.Kernel.Misc.Perm.J5K
public import Certificates.Kernel.Misc.Perm.J5C0
public import Certificates.Data.Kernel.Misc.ChainTail
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Misc.ArrEnum

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.RankThree.PartOne
open CFSG.KC.Misc.Clos (allR)

theorem rsz0 : Nat.beq (j2FiveRS 0).size 6 = true := by quickRfl

theorem rbind0 : ∀ j < 6, arrBind (j2FiveRS 0)[j]! 315 9 (C0.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bsz0 : ((j2FiveRBase 0).map Fin.val).toArray.size = 4 := by decide +kernel

theorem bget0 : ∀ t < 4, ((j2FiveRBase 0).map Fin.val).toArray[t]! = pg 9 (mask 9) C0.BP t := by
  decide +kernel

theorem perm0 : allN 6 (fun j => permOK 315 9 (mask 9) (315 * 9) (C0.S j) (C0.SI j)) = true := by
  quickRfl

theorem gens0 : ∀ k < 3, permB 315 9 (C0.S k) = true ∧ permB 315 9 (GR k) = true ∧
    Nat.beq (C0.S k) (GR k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

@[expose] noncomputable def br0 (k : ℕ) : Bool :=
  ptailBranchK 315 9 C0.LR C0.TR C0.BP (LX 0) (pw (LX 0)) (j2FiveRRels 0) 50 C0P.F 4 k

theorem br0_0 : allR 0 63 br0 = true := by quickRfl
theorem br0_1 : allR 63 63 br0 = true := by quickRfl
theorem br0_2 : allR 126 63 br0 = true := by quickRfl
theorem br0_3 : allR 189 63 br0 = true := by quickRfl
theorem br0_4 : allR 252 63 br0 = true := by quickRfl

theorem lx0 : permB 315 9 (LX 0) = true := by quickRfl

theorem rels0 : relsK C0.BP (LX 0) 4 (j2FiveRRels 0) = true := by quickRfl

theorem bpt0 : ∀ t < 4, pg 9 (mask 9) C0.BP t < 315 := by decide +kernel

theorem rc0 : Nat.beq (rcnt (C0.LR 0)) 315 = true := by quickRfl

theorem cgs0 : (j2FiveCG 0).size = 2 := by decide

theorem comm0 : ∀ k < 2, permB 315 9 (CGP0 k) = true ∧
    Nat.beq (cm (CGP0 k) (LX 0)) (cm (LX 0) (CGP0 k)) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl⟩

theorem sift0 : ∀ k < 2, Nat.beq (Nat.shiftRight (CGP0 k) (315 * 9)) 0 = true ∧
    allN 315 (fun t => Nat.blt (pg 9 (mask 9) (CGP0 k) t) 315) = true ∧
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) C0.LR C0.TRI C0.BP 4 0 (CGP0 k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelMisc.J2F

end
