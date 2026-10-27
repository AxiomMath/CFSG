module

public import Certificates.Data.Kernel.Tower.T2Sq
public import Certificates.Data.Kernel.Tower.Cnt
public import Certificates.Kernel.Tower.WData
public import Certificates.Kernel.Tower.AData
public import Certificates.Kernel.Tower.WrSData

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

@[expose] noncomputable def wrL2 (r1 : Nat) : Bool :=
  lvl2At (wm wrSM wrAC) 64 (wrSD 0) (wrSD 4) (wrSD 7) 48 (wrSD 12) (wrSD 14) (wrSD 17) 24
    (wrSD (Nat.add 18 r1)) r1

@[expose] noncomputable def wrSL3 (r2 : Nat) : Bool :=
  lvl3At (wm wrSM wrAC) 64 (wrSD 0) (wrSD 4) (wrSD 8) 104 (wrSD 12) (wrSD 14) (wrSD 15) (wrSD 17)
    192 (wrSD (Nat.add 33 r2)) r2

@[expose] noncomputable def wrR3 (r3 : Nat) : Bool :=
  Nat.blt (Nat.land (r3L (wrSD 15) r3) 4095) 24 &&
    outC 8192 (wm wrSM wrAC) wGS wrPT wrIM 96 (r3IM 64 (wrSD 12) (wrSD 14) (wrSD 15) r3)
      (Nat.shiftRight (r3L (wrSD 15) r3) 25)

@[expose] noncomputable def wrT2At (a : Nat) : Bool :=
  t2At (wm wrSM wrAC) wGS (wrSD 4) wrT2.b0 wrT2.b1 (wrA (Nat.add a 2)) a

theorem ch36408_ord : ordOK 8192 (wm wrSM wrAC) (wrSD 0) = true := by decide +kernel
theorem ch36408_lab : labOK 8192 (wm wrSM wrAC) wGS (wrSD 16) (wrSD 1) (wrSD 2) 152 = true := by
  decide +kernel
theorem ch36408_czH : czHB (histB 8192 (wrSD 1)) (wrSD 3) 152 = true := by decide +kernel
theorem ch36408_h : hOK 8192 (wm wrSM wrAC) 64 (wrSD 4) = true := by decide +kernel
theorem ch36408_cm1 : cmOK 8192 (wm wrSM wrAC) 64 (wrSD 0) (wrSD 1) (wrSD 3) (wrSD 4) (l16 wGS 1)
    (lane (wrSD 5) 8 255 0) (wrSD 6) (wrSD 9) 120 = true := by decide +kernel
theorem ch36408_cm2 : cmOK 8192 (wm wrSM wrAC) 64 (wrSD 0) (wrSD 1) (wrSD 3) (wrSD 4) (l16 wGS 2)
    (lane (wrSD 5) 8 255 1) (wrSD 7) (wrSD 10) 48 = true := by decide +kernel
theorem ch36408_cm3 : cmOK 8192 (wm wrSM wrAC) 64 (wrSD 0) (wrSD 1) (wrSD 3) (wrSD 4) (l16 wGS 3)
    (lane (wrSD 5) 8 255 2) (wrSD 8) (wrSD 11) 104 = true := by decide +kernel
theorem ch36408_pv : pvOK (wm wrSM wrAC) 64 (wrSD 0) wGS (wrSD 17) = true := by decide +kernel
theorem ch36408_lvl1 : lvl1B (wm wrSM wrAC) (wrSD 4) (wrSD 6) 120 (wrSD 12) (wrSD 13) 15 = true := by
  decide +kernel
theorem ch36408_lvl2 : allB 15 wrL2 = true := by decide +kernel
theorem ch36408_lvl3 : allFrom 0 24 wrSL3 = true := by decide +kernel
theorem ch36408_r3 : allFrom 0 192 wrR3 = true := by decide +kernel
theorem ch36408_t2_0 : allFrom 0 48 wrT2At = true := by decide +kernel
theorem ch36408_t2_1 : allFrom 48 48 wrT2At = true := by decide +kernel

end Certificates.KernelTower
