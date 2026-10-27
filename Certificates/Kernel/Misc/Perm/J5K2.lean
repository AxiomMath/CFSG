module

public import Certificates.Kernel.Misc.Perm.J5K
public import Certificates.Kernel.Misc.Perm.J5C2
public import Certificates.Data.Kernel.Misc.ChainTail
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Misc.ArrEnum

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2F

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum CFSG.KC.Misc.ChainTail
open CFSG.RankThree.PartOne
open CFSG.KC.Misc.Clos (allR)

theorem rsz2 : Nat.beq (j2FiveRS 2).size 8 = true := by quickRfl

theorem rbind2 : ∀ j < 8, arrBind (j2FiveRS 2)[j]! 315 9 (C2.S j) = true := by
  intro j hj
  interval_cases j <;> quickRfl

theorem bsz2 : ((j2FiveRBase 2).map Fin.val).toArray.size = 4 := by decide +kernel

theorem bget2 : ∀ t < 4, ((j2FiveRBase 2).map Fin.val).toArray[t]! = pg 9 (mask 9) C2.BP t := by
  decide +kernel

theorem perm2 : allN 8 (fun j => permOK 315 9 (mask 9) (315 * 9) (C2.S j) (C2.SI j)) = true := by
  quickRfl

theorem gens2 : ∀ k < 3, permB 315 9 (C2.S k) = true ∧ permB 315 9 (GR k) = true ∧
    Nat.beq (C2.S k) (GR k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

@[expose] noncomputable def br2 (k : ℕ) : Bool :=
  ptailBranchK 315 9 C2.LR C2.TR C2.BP (LX 2) (pw (LX 2)) (j2FiveRRels 2) 300 C2P.F 4 k

theorem br2_0 : allR 0 63 br2 = true := by quickRfl
theorem br2_1 : allR 63 63 br2 = true := by quickRfl
theorem br2_2 : allR 126 63 br2 = true := by quickRfl
theorem br2_3 : allR 189 63 br2 = true := by quickRfl
theorem br2_4 : allR 252 63 br2 = true := by quickRfl

theorem lx2 : permB 315 9 (LX 2) = true := by quickRfl

theorem rels2 : relsK C2.BP (LX 2) 4 (j2FiveRRels 2) = true := by quickRfl

theorem bpt2 : ∀ t < 4, pg 9 (mask 9) C2.BP t < 315 := by decide +kernel

theorem rc2 : Nat.beq (rcnt (C2.LR 0)) 315 = true := by quickRfl

theorem cgs2 : (j2FiveCG 2).size = 3 := by decide

theorem comm2 : ∀ k < 3, permB 315 9 (CGP2 k) = true ∧
    Nat.beq (cm (CGP2 k) (LX 2)) (cm (LX 2) (CGP2 k)) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl⟩

theorem sift2 : ∀ k < 3, Nat.beq (Nat.shiftRight (CGP2 k) (315 * 9)) 0 = true ∧
    allN 315 (fun t => Nat.blt (pg 9 (mask 9) (CGP2 k) t) 315) = true ∧
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) C2.LR C2.TRI C2.BP 4 0 (CGP2 k) = true := by
  intro k hk
  interval_cases k <;> exact ⟨by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelMisc.J2F

end
