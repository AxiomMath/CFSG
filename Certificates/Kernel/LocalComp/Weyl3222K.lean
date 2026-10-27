module

public import Certificates.Kernel.LocalComp.Weyl3186K
public import Certificates.Data.Kernel.WeylE8.U
public import Certificates.Kernel.LocalComp.E8Tables
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.W3186

open CFSG.KC.Enum CFSG.KLC.E8

@[expose] noncomputable def CGC : Nat := nat_lit 23977607783800121752830425511692626958976736721993647745

@[expose] noncomputable def W5 : Nat := nat_lit 252445440

@[expose] noncomputable def W80 : Nat := nat_lit 4039127040

@[expose] noncomputable def W85 : Nat := nat_lit 340266545438107957240229935594278224640

theorem kFr : framesOK DPK E8.FR = true := by quickRfl
theorem kCS5 : commSetK DPK E8.FR (signC 5) W5 4 = true := by quickRfl
theorem kCS80 : commSetK DPK E8.FR (signC 80) W80 4 = true := by quickRfl
theorem kCS85 : commSetK DPK E8.FR (signC 85) W85 16 = true := by quickRfl
theorem kCG : allN 6 (fun k => okC (e32 CGC k)) = true := by quickRfl

theorem kU0 : rangeK (uAt PP GC CGC) 0 512 = true := by quickRfl
theorem kU1 : rangeK (uAt PP GC CGC) 512 512 = true := by quickRfl
theorem kU2 : rangeK (uAt PP GC CGC) 1024 512 = true := by quickRfl
theorem kU3 : rangeK (uAt PP GC CGC) 1536 512 = true := by quickRfl
theorem kU4 : rangeK (uAt PP GC CGC) 2048 512 = true := by quickRfl
theorem kU5 : rangeK (uAt PP GC CGC) 2560 512 = true := by quickRfl
theorem kU6 : rangeK (uAt PP GC CGC) 3072 512 = true := by quickRfl
theorem kU7 : rangeK (uAt PP GC CGC) 3584 512 = true := by quickRfl
theorem kU8 : rangeK (uAt PP GC CGC) 4096 512 = true := by quickRfl
theorem kU9 : rangeK (uAt PP GC CGC) 4608 512 = true := by quickRfl
theorem kU10 : rangeK (uAt PP GC CGC) 5120 512 = true := by quickRfl
theorem kU11 : rangeK (uAt PP GC CGC) 5632 512 = true := by quickRfl
theorem kU12 : rangeK (uAt PP GC CGC) 6144 512 = true := by quickRfl
theorem kU13 : rangeK (uAt PP GC CGC) 6656 512 = true := by quickRfl
theorem kU14 : rangeK (uAt PP GC CGC) 7168 512 = true := by quickRfl
theorem kU15 : rangeK (uAt PP GC CGC) 7680 512 = true := by quickRfl

theorem kU : ∀ q < 16, rangeK (uAt PP GC CGC) (512 * q) 512 = true := by
  intro q hq
  interval_cases q
  exacts [kU0, kU1, kU2, kU3, kU4, kU5, kU6, kU7, kU8, kU9, kU10, kU11, kU12, kU13, kU14, kU15]

end CertificateChecks.KernelLC.W3186

end
