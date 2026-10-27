
module

public import Certificates.Kernel.SporSch.HeT.CntGlue
public import Certificates.Kernel.SporSch.HeT.CntU
public import Certificates.Kernel.SporSch.HeT.CntS1
public import CFSG.Sporadic.HeldB.HeBlocks
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import Certificates.Data.CFSGNative.HeldB.Tests
public meta import CFSG.Sporadic.HeldB.HeBlocks
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import Certificates.Data.CFSGNative.HeldB.Tests
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeF18

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB
open CFSG.Sporadic.HeldB.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSpor
open CertificateChecks.KernelSporSch.HeO16 CertificateChecks.KernelSporSch.HeCn

theorem kU5 : Nat.beq (pp R 5) U5 = true := by quickRfl
theorem kU0 : Nat.beq (pm U5 0) 0 = true := by quickRfl
theorem kA0 : Nat.beq (pm (HeC.S 0) 0) 0 = true := by quickRfl
theorem kFixU : Nat.beq (CFSG.KC.HeFixK.fixK 8330 14 U5) 98 = true := by quickRfl
theorem kFixA : Nat.beq (CFSG.KC.HeFixK.fixK 8330 14 (HeC.S 0)) 346 = true := by quickRfl
theorem kP2 : Nat.beq (pp (HeC.S 0) 2) (pidn 8330 14) = true := by quickRfl
theorem kP7 : Nat.beq (pp (HeC.S 1) 7) (pidn 8330 14) = true := by quickRfl
theorem kXU : permOK 8330 14 (mask 14) (8330 * 14) XU XUI = true := by quickRfl
theorem kFU : nfValidK 5 HeC.LR FU = true := by quickRfl
theorem kVU : Nat.beq (sumN 8330 VU) 15120 = true := by quickRfl
theorem kXU01 : bAnd(Nat.beq (pmR HeCnRXU 0) 0, Nat.beq (pmR HeCnRXU 1) 2) = true := by quickRfl
theorem kRXU : rbAll HeCnRXU XU = true := by quickRfl
theorem kRYU : rbAll HeCnRYU U5 = true := by quickRfl
theorem kS1 : Nat.beq (sumN 35 S1) 3136 = true := by quickRfl

theorem U_eq : heUArr = unpack 8330 14 U5 := by
  rw [heUArr, R_eq, (pow_unpack kCanon 5).1, Nat.eq_of_beq_eq_true kU5]

theorem gen0_fix0 : (heGen 0)[0]! = 0 := by
  rw [gen_eq 0 (by norm_num), unpackGet (by norm_num)]
  exact Nat.eq_of_beq_eq_true kA0

theorem u_fix0 : heUArr[0]! = 0 := by
  rw [U_eq, unpackGet (by norm_num)]
  exact Nat.eq_of_beq_eq_true kU0

theorem pow_id {j e : Nat} (hj : j < 2) (he : Nat.beq (pp (HeC.S j) e) (pidn 8330 14) = true) :
    eqA 8330 (hePowA (heGen j) e) (idA 8330) = true := by
  rw [gen_eq j hj, (pow_unpack (canonS j (by omega)) e).1, Nat.eq_of_beq_eq_true he, ← hid]
  exact eqK_sound (Nat.beq_refl _)

theorem repU : RepF 8330 (pm U5) heAutU := by
  have h := rep_heU
  rw [U_eq] at h
  exact repF_of_rep h

theorem cardU : Nat.card {x : heP // heAutU * (x : Equiv.Perm (Fin 8330)) = x * heAutU} =
    15120 := by
  have hX := repF_of_rb kRXU (rep_pm kXU)
  have hY := repF_of_rb kRYU repU
  have hc : ∀ s < 49, cjB HeCnRXU HeCnRYU FU s = true := CU.all
  rw [cent_of_or hX hY kFU hc (Nat.eq_of_beq_eq_true ((bAnd_iff (Nat.beq (pmR HeCnRXU 0) 0) (Nat.beq (pmR HeCnRXU 1) 2)).1 kXU01).1)
    (Nat.eq_of_beq_eq_true ((bAnd_iff (Nat.beq (pmR HeCnRXU 0) 0) (Nat.beq (pmR HeCnRXU 1) 2)).1 kXU01).2) (hxy_u hX hY kFU hc) (e := 8330) (fun h => absurd h (by norm_num)) OU.all]
  exact Nat.eq_of_beq_eq_true kVU

theorem cardW : Nat.card {x : heP // (heAutU * x) ^ 2 = 1 ∧ (x : Equiv.Perm (Fin 8330)) 0 = 0} =
    3136 := by
  rw [tw_of_cnt (repF_of_rb kRYU repU) (fun g hg => heAutU_twist_sq_mem hg) SS1.all]
  exact Nat.eq_of_beq_eq_true kS1

theorem blocks : ((heBlock1.all fun t => t[0]! == 0) && (heBlock2.all fun t => t[0]! == 0) &&
    countWPar 25 (commB heUArr heBase) (heBlock0.filter fun t0 => heUArr[t0[0]!]! == t0[0]!)
      [heBlock1, heBlock2] == 15120 &&
    countWPar 1 (twistInvB heUArr heBase) (heBlock0.filter fun t0 => t0[0]! == 0)
      [heBlock1, heBlock2] == 3136) = true := by
  have hC := (card_heP_eq_count_filter (f := commB heUArr heBase) (g := commB heUArr heBase)
    (fun x => heAutU * x = x * heAutU) _ (sz := 25) (by norm_num)
    (fun w x hw hx => commB_iff heP_baseFaithful rep_heU hw heBase_lt (heAutU_comm_mem hx))
    fun t0 _ t1 h1 t2 h2 => commB_prune u_fix0 (heBlock12_fix0' h1 h2).1
      (heBlock12_fix0' h1 h2).2).symm.trans cardU
  have hW := (card_heP_eq_count_filter (f := twistInvB heUArr heBase)
    (g := fun w => twistInvB heUArr heBase w && (evR w 0 == 0))
    (fun x => (heAutU * x) ^ 2 = 1 ∧ x 0 = 0) _ (sz := 1) (by norm_num)
    (fun w x hw hx => by
      rw [Bool.and_eq_true, twistInvB_iff heP_baseFaithful rep_heU hw heBase_lt
        (heAutU_twist_sq_mem hx), evR_zero_iff hw])
    fun t0 _ t1 h1 t2 h2 => zero_prune _ (heBlock12_fix0' h1 h2).1
      (heBlock12_fix0' h1 h2).2).symm.trans cardW
  have hB := heBlocks_fix0'
  rw [Bool.and_eq_true] at hB
  rw [hC, hW, hB.1, hB.2]
  rfl

theorem facts : (heUArr[0]! = 0)
    ∧ ((heGen 0)[0]! = 0)
    ∧ ((List.range 8330).countP (fun i => heUArr[i]! == i) = 98)
    ∧ ((List.range 8330).countP (fun i => (heGen 0)[i]! == i) = 346)
    ∧ (eqA 8330 (hePowA (heGen 0) 2) (idA 8330) = true)
    ∧ (eqA 8330 (hePowA (heGen 1) 7) (idA 8330) = true)
    ∧ (((heBlock1.all fun t => t[0]! == 0) && (heBlock2.all fun t => t[0]! == 0) &&
      countWPar 25 (commB heUArr heBase) (heBlock0.filter fun t0 => heUArr[t0[0]!]! == t0[0]!)
        [heBlock1, heBlock2] == 15120 &&
      countWPar 1 (twistInvB heUArr heBase) (heBlock0.filter fun t0 => t0[0]! == 0)
        [heBlock1, heBlock2] == 3136) = true) := by
  refine ⟨u_fix0, gen0_fix0, ?_, ?_, pow_id (by norm_num) kP2, pow_id (by norm_num) kP7, blocks⟩
  · rw [U_eq, CFSG.KC.HeFixK.countP_fix]
    exact Nat.eq_of_beq_eq_true kFixU
  · rw [gen_eq 0 (by norm_num), CFSG.KC.HeFixK.countP_fix]
    exact Nat.eq_of_beq_eq_true kFixA

end CertificateChecks.KernelSporSch.HeF18

end
