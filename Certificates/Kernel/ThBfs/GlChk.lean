module

public import Certificates.Kernel.ThBfs.GlData
public import Certificates.Data.Kernel.ThBfs.GlDefs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000
set_option Elab.async false
set_option profiler true
set_option profiler.threshold 500

public section

namespace CertificateChecks.KernelThBfs

open CFSG.KC.Misc.Clos CFSG.KC.ThBfs

@[expose] noncomputable def glAt (i : Nat) : Bool :=
  bfsAt glAct (nat_lit 65536) (nat_lit 2) (nat_lit 20160) GR GC GS i

theorem ch24203_root : keyAt GR 0 = 33825 := by decide +kernel
theorem ch24203_r0 : allR 0 1260 glAt = true := by quickRfl
theorem ch24203_r1 : allR 1260 1260 glAt = true := by quickRfl
theorem ch24203_r2 : allR 2520 1260 glAt = true := by quickRfl
theorem ch24203_r3 : allR 3780 1260 glAt = true := by quickRfl
theorem ch24203_r4 : allR 5040 1260 glAt = true := by quickRfl
theorem ch24203_r5 : allR 6300 1260 glAt = true := by quickRfl
theorem ch24203_r6 : allR 7560 1260 glAt = true := by quickRfl
theorem ch24203_r7 : allR 8820 1260 glAt = true := by quickRfl
theorem ch24203_r8 : allR 10080 1260 glAt = true := by quickRfl
theorem ch24203_r9 : allR 11340 1260 glAt = true := by quickRfl
theorem ch24203_r10 : allR 12600 1260 glAt = true := by quickRfl
theorem ch24203_r11 : allR 13860 1260 glAt = true := by quickRfl
theorem ch24203_r12 : allR 15120 1260 glAt = true := by quickRfl
theorem ch24203_r13 : allR 16380 1260 glAt = true := by quickRfl
theorem ch24203_r14 : allR 17640 1260 glAt = true := by quickRfl
theorem ch24203_r15 : allR 18900 1260 glAt = true := by quickRfl

end CertificateChecks.KernelThBfs

end
