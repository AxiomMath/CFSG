module

public import CFSG.Certificates.Kernel.Trace6091.Assemble
public import Certificates.Kernel.Trace6091.OddA
public import Certificates.Kernel.Trace6091.OctA
public import Certificates.Kernel.Trace6091.RestA
public import Certificates.Kernel.Trace6091.OctC
public import Certificates.Kernel.Trace6091.RestC

public section

namespace Certificates.Kernel.Trace6091

open CFSG.KC CFSG.KC.Trace6091 CFSG.Monster.B CFSG.Monster.AxisCount CFSG.Monster.Existence

theorem trK_A : trK permMonoA = 2 * 783 := by
  rw [trK, xBlk, latTrA, latTr2A, wTrA, pairA_sum, oddA_sum, octA_sum]
  norm_num

theorem trK_C : trK permMonoC = 2 * 0 := by
  rw [trK, xBlk, latTrC, latTr2C, wTrC, pairC_sum, oddC_sum, octC_sum]
  norm_num

theorem trK_A_ne : trK permMonoA ≠ 2 * 782 := by
  rw [trK_A]
  norm_num


theorem traceA (hv : Native.permValid permMonoA = true) : permTraceCheck permMonoA 783 = true :=
  permTraceCheck_of_K permMonoA hv trK_A

theorem traceC (hv : Native.permValid permMonoC = true) : permTraceCheck permMonoC 0 = true :=
  permTraceCheck_of_K permMonoC hv trK_C

end Certificates.Kernel.Trace6091

end
