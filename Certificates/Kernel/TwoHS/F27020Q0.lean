module

public import Certificates.Kernel.TwoHS.F27020QC
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

#kc_repo #kc_decls CFSG.KD.TwoHS "Certificates/Kernel/TwoHS/data/f27020q0.txt" 627360 17211091072214740959

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Recognition.HSMultiplier

@[expose] noncomputable def T270 : Fin 6 → Nat := sel6 R270T0 R270T1 R270T2 R270T3 R270T4 R270T5

@[expose] noncomputable def A270 : Fin 6 → Nat := sel6 R270A0 R270A1 R270A2 R270A3 R270A4 R270A5

@[expose] noncomputable def E270 : Fin 4 → Nat := sel4 R270E0 R270E1 R270E2 R270E3

theorem q0t0 : Nat.beq (EVKC HYF HYF (hfxW 0 0)) (T270 0) = true := by quickRfl
theorem q0t1 : Nat.beq (EVKC HYF HYF (hfxW 0 1)) (T270 1) = true := by quickRfl
theorem q0t2 : Nat.beq (EVKC HYF HYF (hfxW 0 2)) (T270 2) = true := by quickRfl
theorem q0t3 : Nat.beq (EVKC HYF HYF (hfxW 0 3)) (T270 3) = true := by quickRfl
theorem q0t4 : Nat.beq (EVKC HYF HYF (hfxW 0 4)) (T270 4) = true := by quickRfl
theorem q0t5 : Nat.beq (EVKC HYF HYF (hfxW 0 5)) (T270 5) = true := by quickRfl
theorem q0a0 : Nat.beq (EVKC T270 T270 (hsCommWord 0)) (A270 0) = true := by quickRfl
theorem q0a1 : Nat.beq (EVKC T270 T270 (hsCommWord 1)) (A270 1) = true := by quickRfl
theorem q0a2 : Nat.beq (EVKC T270 T270 (hsCommWord 2)) (A270 2) = true := by quickRfl
theorem q0a3 : Nat.beq (EVKC T270 T270 (hsCommWord 3)) (A270 3) = true := by quickRfl
theorem q0a4 : Nat.beq (EVKC T270 T270 (hsCommWord 4)) (A270 4) = true := by quickRfl
theorem q0a5 : Nat.beq (EVKC T270 T270 (hsCommWord 5)) (A270 5) = true := by quickRfl
theorem q0e0 : Nat.beq (EVKC HYF HYF (hfxE 0 0)) (E270 0) = true := by quickRfl
theorem q0e1 : Nat.beq (EVKC HYF HYF (hfxE 0 1)) (E270 1) = true := by quickRfl
theorem q0e2 : Nat.beq (EVKC HYF HYF (hfxE 0 2)) (E270 2) = true := by quickRfl
theorem q0e3 : Nat.beq (EVKC HYF HYF (hfxE 0 3)) (E270 3) = true := by quickRfl
theorem q0f0 : Nat.beq (EVKC A270 A270 (hfxE 0 0)) (E270 0) = true := by quickRfl
theorem q0f1 : Nat.beq (EVKC A270 A270 (hfxE 0 1)) (E270 1) = true := by quickRfl
theorem q0f2 : Nat.beq (EVKC A270 A270 (hfxE 0 2)) (E270 2) = true := by quickRfl
theorem q0f3 : Nat.beq (EVKC A270 A270 (hfxE 0 3)) (E270 3) = true := by quickRfl
theorem q0body : ckBodyQC idK T270 A270 E270 E270 (fun m => prodKC E270 m.val) = true := by
  quickRfl

theorem ok27020Q_0 : ck27020Q 0 = true :=
  ck27020Q_of_pins (T := T270) (A := A270) (E := E270) (EVK_pin q0t0) (EVK_pin q0t1)
    (EVK_pin q0t2) (EVK_pin q0t3) (EVK_pin q0t4) (EVK_pin q0t5) (EVK_pin q0a0) (EVK_pin q0a1)
    (EVK_pin q0a2) (EVK_pin q0a3) (EVK_pin q0a4) (EVK_pin q0a5) (EVK_pin q0e0) (EVK_pin q0e1)
    (EVK_pin q0e2) (EVK_pin q0e3) (EVK_pin q0f0) (EVK_pin q0f1) (EVK_pin q0f2) (EVK_pin q0f3)
    q0body

end CFSG.KD.TwoHS

end
