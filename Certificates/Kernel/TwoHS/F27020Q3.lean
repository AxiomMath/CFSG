module

public import Certificates.Kernel.TwoHS.F27020QC
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

#kc_repo #kc_decls CFSG.KD.TwoHS "Certificates/Kernel/TwoHS/data/f27020q3.txt" 627360 132244704891582541

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Recognition.HSMultiplier

@[expose] noncomputable def T273 : Fin 6 → Nat := sel6 R273T0 R273T1 R273T2 R273T3 R273T4 R273T5

@[expose] noncomputable def A273 : Fin 6 → Nat := sel6 R273A0 R273A1 R273A2 R273A3 R273A4 R273A5

@[expose] noncomputable def E273 : Fin 4 → Nat := sel4 R273E0 R273E1 R273E2 R273E3

theorem q3t0 : Nat.beq (EVKC HYF HYF (hfxW 3 0)) (T273 0) = true := by quickRfl
theorem q3t1 : Nat.beq (EVKC HYF HYF (hfxW 3 1)) (T273 1) = true := by quickRfl
theorem q3t2 : Nat.beq (EVKC HYF HYF (hfxW 3 2)) (T273 2) = true := by quickRfl
theorem q3t3 : Nat.beq (EVKC HYF HYF (hfxW 3 3)) (T273 3) = true := by quickRfl
theorem q3t4 : Nat.beq (EVKC HYF HYF (hfxW 3 4)) (T273 4) = true := by quickRfl
theorem q3t5 : Nat.beq (EVKC HYF HYF (hfxW 3 5)) (T273 5) = true := by quickRfl
theorem q3a0 : Nat.beq (EVKC T273 T273 (hsCommWord 0)) (A273 0) = true := by quickRfl
theorem q3a1 : Nat.beq (EVKC T273 T273 (hsCommWord 1)) (A273 1) = true := by quickRfl
theorem q3a2 : Nat.beq (EVKC T273 T273 (hsCommWord 2)) (A273 2) = true := by quickRfl
theorem q3a3 : Nat.beq (EVKC T273 T273 (hsCommWord 3)) (A273 3) = true := by quickRfl
theorem q3a4 : Nat.beq (EVKC T273 T273 (hsCommWord 4)) (A273 4) = true := by quickRfl
theorem q3a5 : Nat.beq (EVKC T273 T273 (hsCommWord 5)) (A273 5) = true := by quickRfl
theorem q3e0 : Nat.beq (EVKC HYF HYF (hfxE 3 0)) (E273 0) = true := by quickRfl
theorem q3e1 : Nat.beq (EVKC HYF HYF (hfxE 3 1)) (E273 1) = true := by quickRfl
theorem q3e2 : Nat.beq (EVKC HYF HYF (hfxE 3 2)) (E273 2) = true := by quickRfl
theorem q3e3 : Nat.beq (EVKC HYF HYF (hfxE 3 3)) (E273 3) = true := by quickRfl
theorem q3f0 : Nat.beq (EVKC A273 A273 (hfxE 3 0)) (E273 0) = true := by quickRfl
theorem q3f1 : Nat.beq (EVKC A273 A273 (hfxE 3 1)) (E273 1) = true := by quickRfl
theorem q3f2 : Nat.beq (EVKC A273 A273 (hfxE 3 2)) (E273 2) = true := by quickRfl
theorem q3f3 : Nat.beq (EVKC A273 A273 (hfxE 3 3)) (E273 3) = true := by quickRfl
theorem q3body : ckBodyQC idK T273 A273 E273 E273 (fun m => prodKC E273 m.val) = true := by
  quickRfl

theorem ok27020Q_3 : ck27020Q 3 = true :=
  ck27020Q_of_pins (T := T273) (A := A273) (E := E273) (EVK_pin q3t0) (EVK_pin q3t1)
    (EVK_pin q3t2) (EVK_pin q3t3) (EVK_pin q3t4) (EVK_pin q3t5) (EVK_pin q3a0) (EVK_pin q3a1)
    (EVK_pin q3a2) (EVK_pin q3a3) (EVK_pin q3a4) (EVK_pin q3a5) (EVK_pin q3e0) (EVK_pin q3e1)
    (EVK_pin q3e2) (EVK_pin q3e3) (EVK_pin q3f0) (EVK_pin q3f1) (EVK_pin q3f2) (EVK_pin q3f3)
    q3body

end CFSG.KD.TwoHS

end
