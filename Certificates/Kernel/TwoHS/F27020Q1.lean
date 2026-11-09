module

public import Certificates.Kernel.TwoHS.F27020QC
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

#kc_repo #kc_decls CFSG.KD.TwoHS "Certificates/Kernel/TwoHS/data/f27020q1.txt" 627360 2596910882297037770

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Recognition.HSMultiplier

@[expose] noncomputable def T271 : Fin 6 → Nat := sel6 R271T0 R271T1 R271T2 R271T3 R271T4 R271T5

@[expose] noncomputable def A271 : Fin 6 → Nat := sel6 R271A0 R271A1 R271A2 R271A3 R271A4 R271A5

@[expose] noncomputable def E271 : Fin 4 → Nat := sel4 R271E0 R271E1 R271E2 R271E3

theorem q1t0 : Nat.beq (EVKC HYF HYF (hfxW 1 0)) (T271 0) = true := by quickRfl
theorem q1t1 : Nat.beq (EVKC HYF HYF (hfxW 1 1)) (T271 1) = true := by quickRfl
theorem q1t2 : Nat.beq (EVKC HYF HYF (hfxW 1 2)) (T271 2) = true := by quickRfl
theorem q1t3 : Nat.beq (EVKC HYF HYF (hfxW 1 3)) (T271 3) = true := by quickRfl
theorem q1t4 : Nat.beq (EVKC HYF HYF (hfxW 1 4)) (T271 4) = true := by quickRfl
theorem q1t5 : Nat.beq (EVKC HYF HYF (hfxW 1 5)) (T271 5) = true := by quickRfl
theorem q1a0 : Nat.beq (EVKC T271 T271 (hsCommWord 0)) (A271 0) = true := by quickRfl
theorem q1a1 : Nat.beq (EVKC T271 T271 (hsCommWord 1)) (A271 1) = true := by quickRfl
theorem q1a2 : Nat.beq (EVKC T271 T271 (hsCommWord 2)) (A271 2) = true := by quickRfl
theorem q1a3 : Nat.beq (EVKC T271 T271 (hsCommWord 3)) (A271 3) = true := by quickRfl
theorem q1a4 : Nat.beq (EVKC T271 T271 (hsCommWord 4)) (A271 4) = true := by quickRfl
theorem q1a5 : Nat.beq (EVKC T271 T271 (hsCommWord 5)) (A271 5) = true := by quickRfl
theorem q1e0 : Nat.beq (EVKC HYF HYF (hfxE 1 0)) (E271 0) = true := by quickRfl
theorem q1e1 : Nat.beq (EVKC HYF HYF (hfxE 1 1)) (E271 1) = true := by quickRfl
theorem q1e2 : Nat.beq (EVKC HYF HYF (hfxE 1 2)) (E271 2) = true := by quickRfl
theorem q1e3 : Nat.beq (EVKC HYF HYF (hfxE 1 3)) (E271 3) = true := by quickRfl
theorem q1f0 : Nat.beq (EVKC A271 A271 (hfxE 1 0)) (E271 0) = true := by quickRfl
theorem q1f1 : Nat.beq (EVKC A271 A271 (hfxE 1 1)) (E271 1) = true := by quickRfl
theorem q1f2 : Nat.beq (EVKC A271 A271 (hfxE 1 2)) (E271 2) = true := by quickRfl
theorem q1f3 : Nat.beq (EVKC A271 A271 (hfxE 1 3)) (E271 3) = true := by quickRfl
theorem q1body : ckBodyQC idK T271 A271 E271 E271 (fun m => prodKC E271 m.val) = true := by
  quickRfl

theorem ok27020Q_1 : ck27020Q 1 = true :=
  ck27020Q_of_pins (T := T271) (A := A271) (E := E271) (EVK_pin q1t0) (EVK_pin q1t1)
    (EVK_pin q1t2) (EVK_pin q1t3) (EVK_pin q1t4) (EVK_pin q1t5) (EVK_pin q1a0) (EVK_pin q1a1)
    (EVK_pin q1a2) (EVK_pin q1a3) (EVK_pin q1a4) (EVK_pin q1a5) (EVK_pin q1e0) (EVK_pin q1e1)
    (EVK_pin q1e2) (EVK_pin q1e3) (EVK_pin q1f0) (EVK_pin q1f1) (EVK_pin q1f2) (EVK_pin q1f3)
    q1body

end CFSG.KD.TwoHS

end
