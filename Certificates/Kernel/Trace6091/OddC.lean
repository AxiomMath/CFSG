module

public import CFSG.Certificates.Kernel.Trace6091.ScanRest
public import CFSG.Monster.Existence.TwoPoint.ThreeRepsInputs

public section

namespace Certificates.Kernel.Trace6091

open CFSG.KC CFSG.KC.KDense CFSG.KC.Trace6091 CFSG.Monster.B CFSG.Monster.Existence Finset

@[expose] noncomputable def PC : Nat := nat_lit 49868768104246463569932747720473076

theorem pe_PC : ∀ i < 24, pe PC i = permMonoC[i]! := by decide +kernel

theorem oddC_0 : oddScanT PC (betaTabT PC) 0 256 = 0 := by decide +kernel

theorem oddC_1 : oddScanT PC (betaTabT PC) 256 256 = 0 := by decide +kernel

theorem oddC_2 : oddScanT PC (betaTabT PC) 512 256 = 0 := by decide +kernel

theorem oddC_3 : oddScanT PC (betaTabT PC) 768 256 = 0 := by decide +kernel

theorem oddC_4 : oddScanT PC (betaTabT PC) 1024 256 = 0 := by decide +kernel

theorem oddC_5 : oddScanT PC (betaTabT PC) 1280 256 = 0 := by decide +kernel

theorem oddC_6 : oddScanT PC (betaTabT PC) 1536 256 = 0 := by decide +kernel

theorem oddC_7 : oddScanT PC (betaTabT PC) 1792 256 = 0 := by decide +kernel

theorem oddC_sum : ∑ t ∈ range 2048, ∑ i ∈ range 24,
    xTerm permMonoC (Model.oddCode (2 * t) i) (Model.dualN (2 ^ i)) = 0 := by
  refine (odd_block pe_PC [0, 0, 0, 0, 0, 0, 0, 0] fun k hk => ?_).trans (by decide +kernel)
  interval_cases k
  exacts [oddC_0, oddC_1, oddC_2, oddC_3, oddC_4, oddC_5, oddC_6, oddC_7]

@[expose] noncomputable def PBadC : Nat := nat_lit 49868768104246464290508688099752416

theorem oddBadC_0 : oddScanT PBadC (betaTabT PBadC) 0 256 ≠ 0 := by decide +kernel

end Certificates.Kernel.Trace6091

end
