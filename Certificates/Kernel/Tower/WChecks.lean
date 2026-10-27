module

public import Certificates.Data.Kernel.Tower.W
public import Certificates.Kernel.Tower.WData
public import Certificates.Data.CFSGNative.SCATWreathData

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

theorem ch36409_lp : lpOK slLP CFSG.SCATWreath.slList = true := by decide +kernel
theorem ch36409_sm : smOK slLP slSM = true := by decide +kernel
theorem ch36409_ac : acOK slLP slAC = true := by decide +kernel
theorem ch36408_lp : lpOK wrLP CFSG.SCATWreath.wrList = true := by decide +kernel
theorem ch36408_sm : smOK wrLP wrSM = true := by decide +kernel
theorem ch36408_ac : acOK wrLP wrAC = true := by decide +kernel

theorem ch36409_lp_neg : (!lpOK (Nat.xor slLP 1) CFSG.SCATWreath.slList) = true := by decide +kernel
theorem ch36409_sm_neg : (!smOK slLP (Nat.xor slSM 1)) = true := by decide +kernel
theorem ch36409_ac_neg : (!acOK slLP (Nat.xor slAC 1)) = true := by decide +kernel
theorem ch36408_sm_neg : (!smOK wrLP (Nat.xor wrSM 1)) = true := by decide +kernel
theorem ch36408_ac_neg : (!acOK wrLP (Nat.xor wrAC 1)) = true := by decide +kernel

end Certificates.KernelTower
