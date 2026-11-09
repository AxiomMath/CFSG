module

public import Certificates.Kernel.TwoHS.F27020QC
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.Harness

#kc_repo #kc_decls CFSG.KD.TwoHS "Certificates/Kernel/TwoHS/data/f27020q2.txt" 627360 18109690011280383746

public section

set_option maxRecDepth 400000

namespace CFSG.KD.TwoHS

open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Recognition.HSMultiplier

@[expose] noncomputable def T272 : Fin 6 → Nat := sel6 R272T0 R272T1 R272T2 R272T3 R272T4 R272T5

@[expose] noncomputable def A272 : Fin 6 → Nat := sel6 R272A0 R272A1 R272A2 R272A3 R272A4 R272A5

@[expose] noncomputable def E272 : Fin 4 → Nat := sel4 R272E0 R272E1 R272E2 R272E3

theorem q2t0 : Nat.beq (EVKC HYF HYF (hfxW 2 0)) (T272 0) = true := by quickRfl
theorem q2t1 : Nat.beq (EVKC HYF HYF (hfxW 2 1)) (T272 1) = true := by quickRfl
theorem q2t2 : Nat.beq (EVKC HYF HYF (hfxW 2 2)) (T272 2) = true := by quickRfl
theorem q2t3 : Nat.beq (EVKC HYF HYF (hfxW 2 3)) (T272 3) = true := by quickRfl
theorem q2t4 : Nat.beq (EVKC HYF HYF (hfxW 2 4)) (T272 4) = true := by quickRfl
theorem q2t5 : Nat.beq (EVKC HYF HYF (hfxW 2 5)) (T272 5) = true := by quickRfl
theorem q2a0 : Nat.beq (EVKC T272 T272 (hsCommWord 0)) (A272 0) = true := by quickRfl
theorem q2a1 : Nat.beq (EVKC T272 T272 (hsCommWord 1)) (A272 1) = true := by quickRfl
theorem q2a2 : Nat.beq (EVKC T272 T272 (hsCommWord 2)) (A272 2) = true := by quickRfl
theorem q2a3 : Nat.beq (EVKC T272 T272 (hsCommWord 3)) (A272 3) = true := by quickRfl
theorem q2a4 : Nat.beq (EVKC T272 T272 (hsCommWord 4)) (A272 4) = true := by quickRfl
theorem q2a5 : Nat.beq (EVKC T272 T272 (hsCommWord 5)) (A272 5) = true := by quickRfl
theorem q2e0 : Nat.beq (EVKC HYF HYF (hfxE 2 0)) (E272 0) = true := by quickRfl
theorem q2e1 : Nat.beq (EVKC HYF HYF (hfxE 2 1)) (E272 1) = true := by quickRfl
theorem q2e2 : Nat.beq (EVKC HYF HYF (hfxE 2 2)) (E272 2) = true := by quickRfl
theorem q2e3 : Nat.beq (EVKC HYF HYF (hfxE 2 3)) (E272 3) = true := by quickRfl
theorem q2f0 : Nat.beq (EVKC A272 A272 (hfxE 2 0)) (E272 0) = true := by quickRfl
theorem q2f1 : Nat.beq (EVKC A272 A272 (hfxE 2 1)) (E272 1) = true := by quickRfl
theorem q2f2 : Nat.beq (EVKC A272 A272 (hfxE 2 2)) (E272 2) = true := by quickRfl
theorem q2f3 : Nat.beq (EVKC A272 A272 (hfxE 2 3)) (E272 3) = true := by quickRfl
theorem q2body : ckBodyQC idK T272 A272 E272 E272 (fun m => prodKC E272 m.val) = true := by
  quickRfl

theorem ok27020Q_2 : ck27020Q 2 = true :=
  ck27020Q_of_pins (T := T272) (A := A272) (E := E272) (EVK_pin q2t0) (EVK_pin q2t1) (EVK_pin q2t2) (EVK_pin q2t3) (EVK_pin q2t4)
    (EVK_pin q2t5) (EVK_pin q2a0) (EVK_pin q2a1) (EVK_pin q2a2) (EVK_pin q2a3) (EVK_pin q2a4)
    (EVK_pin q2a5) (EVK_pin q2e0) (EVK_pin q2e1) (EVK_pin q2e2) (EVK_pin q2e3) (EVK_pin q2f0)
    (EVK_pin q2f1) (EVK_pin q2f2) (EVK_pin q2f3) q2body

end CFSG.KD.TwoHS

end
