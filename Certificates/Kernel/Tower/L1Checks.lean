module

public import Certificates.Data.Kernel.Tower.L1
public import Certificates.Kernel.Tower.WData
public import Certificates.Kernel.Tower.L1Data

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

theorem ch36409_l1 : l1OK slSM slAC slPS slRW slMR = true := by decide +kernel
theorem ch36409_reps : repsOK slSM slAC slMR = true := by decide +kernel
theorem ch36408_l1 : l1OK wrSM wrAC wrPS wrRW wrMR = true := by decide +kernel
theorem ch36408_reps : repsOK wrSM wrAC wrMR = true := by decide +kernel

theorem ch36409_l1_neg_rw :
    (!l1OK slSM slAC slPS (Nat.xor slRW (Nat.shiftLeft 1 1664)) slMR) = true := by decide +kernel
theorem ch36409_l1_neg_ps : (!l1OK slSM slAC (Nat.xor slPS 2) slRW slMR) = true := by
  decide +kernel
theorem ch36409_reps_neg : (!repsOK slSM slAC (Nat.xor slMR (Nat.shiftLeft 1 64))) = true := by
  decide +kernel
theorem ch36408_l1_neg_rw :
    (!l1OK wrSM wrAC wrPS (Nat.xor wrRW (Nat.shiftLeft 1 1664)) wrMR) = true := by decide +kernel

end Certificates.KernelTower
