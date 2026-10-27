module

public import Certificates.Data.Kernel.Tower.Search
public import Certificates.Kernel.Tower.WData
public import Certificates.Kernel.Tower.AData
public import Certificates.Kernel.Tower.SData

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

@[expose] noncomputable def slL2 (r1 : Nat) : Bool :=
  lvl2At (wm slSM slAC) 64 (slSD 0) (slSD 4) (slSD 7) 576 (slSD 12) (slSD 14) (slSD 17) 672
    (slSD (Nat.add 18 r1)) r1

@[expose] noncomputable def slL3 (r2 : Nat) : Bool :=
  lvl3At (wm slSM slAC) 64 (slSD 0) (slSD 4) (slSD 8) 208 (slSD 12) (slSD 14) (slSD 15) (slSD 17)
    16128 (slSD (Nat.add 24 r2)) r2

@[expose] noncomputable def slR3 (r3 : Nat) : Bool :=
  Nat.blt (Nat.land (r3L (slSD 15) r3) 4095) 672 &&
    outC 8192 (wm slSM slAC) wGS slPT slIM 32 (r3IM 64 (slSD 12) (slSD 14) (slSD 15) r3)
      (Nat.shiftRight (r3L (slSD 15) r3) 25)

@[expose] noncomputable def slCM (i c : Nat) : Bool :=
  cmOK 8192 (wm slSM slAC) 64 (slSD 0) (slSD 1) (slSD 3) (slSD 4) (l16 wGS i)
    (lane (slSD 5) 8 255 (Nat.sub i 1)) (slSD (Nat.add 5 i)) (slSD (Nat.add 8 i)) c

theorem ch36409_ord : ordOK 8192 (wm slSM slAC) (slSD 0) = true := by decide +kernel
theorem ch36409_lab : labOK 8192 (wm slSM slAC) wGS (slSD 16) (slSD 1) (slSD 2) 92 = true := by
  decide +kernel
theorem ch36409_cz0 : czOK 8192 (slSD 1) (slSD 3) 0 46 = true := by decide +kernel
theorem ch36409_cz1 : czOK 8192 (slSD 1) (slSD 3) 46 46 = true := by decide +kernel
theorem ch36409_h : hOK 8192 (wm slSM slAC) 64 (slSD 4) = true := by decide +kernel
theorem ch36409_cm1 : slCM 1 96 = true := by decide +kernel
theorem ch36409_cm2 : slCM 2 576 = true := by decide +kernel
theorem ch36409_cm3 : slCM 3 208 = true := by decide +kernel
theorem ch36409_pv : pvOK (wm slSM slAC) 64 (slSD 0) wGS (slSD 17) = true := by decide +kernel
theorem ch36409_lvl1 : lvl1B (wm slSM slAC) (slSD 4) (slSD 6) 96 (slSD 12) (slSD 13) 6 = true := by
  decide +kernel
theorem ch36409_lvl2 : allB 6 slL2 = true := by decide +kernel
theorem ch36409_lvl3_0 : allFrom 0 336 slL3 = true := by decide +kernel
theorem ch36409_lvl3_1 : allFrom 336 336 slL3 = true := by decide +kernel
theorem ch36409_r3_0 : allFrom 0 4032 slR3 = true := by decide +kernel
theorem ch36409_r3_1 : allFrom 4032 4032 slR3 = true := by decide +kernel
theorem ch36409_r3_2 : allFrom 8064 4032 slR3 = true := by decide +kernel
theorem ch36409_r3_3 : allFrom 12096 4032 slR3 = true := by decide +kernel

end Certificates.KernelTower
