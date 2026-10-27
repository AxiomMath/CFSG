module

public import Certificates.Kernel.ThBfs.OrbData
public import Certificates.Data.Kernel.ThBfs.Defs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

public section

namespace CertificateChecks.KernelThBfs

open CFSG.KC.Misc.Clos CFSG.KC.ThBfs

@[expose] noncomputable def orbAt (i : Nat) : Bool :=
  bfsAt orbAct (nat_lit 16777216) (nat_lit 2) (nat_lit 22680) OR OC OS i

theorem ch24201_root : keyAt OR 0 = 6566401 := by decide +kernel
theorem ch24201_r0 : allR 0 1260 orbAt = true := by quickRfl
theorem ch24201_r1 : allR 1260 1260 orbAt = true := by quickRfl
theorem ch24201_r2 : allR 2520 1260 orbAt = true := by quickRfl
theorem ch24201_r3 : allR 3780 1260 orbAt = true := by quickRfl
theorem ch24201_r4 : allR 5040 1260 orbAt = true := by quickRfl
theorem ch24201_r5 : allR 6300 1260 orbAt = true := by quickRfl
theorem ch24201_r6 : allR 7560 1260 orbAt = true := by quickRfl
theorem ch24201_r7 : allR 8820 1260 orbAt = true := by quickRfl
theorem ch24201_r8 : allR 10080 1260 orbAt = true := by quickRfl
theorem ch24201_r9 : allR 11340 1260 orbAt = true := by quickRfl
theorem ch24201_r10 : allR 12600 1260 orbAt = true := by quickRfl
theorem ch24201_r11 : allR 13860 1260 orbAt = true := by quickRfl
theorem ch24201_r12 : allR 15120 1260 orbAt = true := by quickRfl
theorem ch24201_r13 : allR 16380 1260 orbAt = true := by quickRfl
theorem ch24201_r14 : allR 17640 1260 orbAt = true := by quickRfl
theorem ch24201_r15 : allR 18900 1260 orbAt = true := by quickRfl
theorem ch24201_r16 : allR 20160 1260 orbAt = true := by quickRfl
theorem ch24201_r17 : allR 21420 1260 orbAt = true := by quickRfl

end CertificateChecks.KernelThBfs

end
