module

public import Certificates.Kernel.Sporadic.Fi24R2W.Data
public import Certificates.Kernel.Sporadic.Fi24Net.Data
public import Certificates.Kernel.Sporadic.Fi24K.K2077
public import Certificates.Data.Kernel.Spor.Fi24R2W
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option Elab.async false

namespace CertificateChecks.KernelSpor.Fi24R2W

open CFSG.KC.Fi24R2W CFSG.KD.Fi24Net

theorem stA_t : stageOK NW (bray BA 10) SA = true := by quickRfl

theorem stB_0 : Nat.beq (walkN NW (bray BB 13).reverse 0) (walkN NW SB.reverse 0) = true := by
  quickRfl

theorem stB_1 : Nat.beq (walkN NW (bray BB 13).reverse 305530) (walkN NW SB.reverse 305530) = true := by
  quickRfl

theorem stB_2 : Nat.beq (walkN NW (bray BB 13).reverse 5604) (walkN NW SB.reverse 5604) = true := by
  quickRfl

theorem stB_3 : Nat.beq (walkN NW (bray BB 13).reverse 221549) (walkN NW SB.reverse 221549) = true := by
  quickRfl

theorem stB_4 : Nat.beq (walkN NW (bray BB 13).reverse 266275) (walkN NW SB.reverse 266275) = true := by
  quickRfl

theorem stB_5 : Nat.beq (walkN NW (bray BB 13).reverse 186844) (walkN NW SB.reverse 186844) = true := by
  quickRfl

theorem stB_t : stageOK NW (bray BB 13) SB = true := by
  unfold stageOK
  rw [List.all_eq_true]
  intro b hb
  simp only [base, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · exact stB_0
  · exact stB_1
  · exact stB_2
  · exact stB_3
  · exact stB_4
  · exact stB_5

theorem plA_t : plOK NW SA FP.F (krow (Fi24KC.S 0)) = true := by quickRfl

theorem plB_t : plOK NW SB FP.F (krow (Fi24KC.S 1)) = true := by quickRfl

end CertificateChecks.KernelSpor.Fi24R2W

end
