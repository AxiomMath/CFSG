module

public import CFSG.Certificates.Kernel.Trace6091.ScanOdd
public import CFSG.Monster.Existence.TwoPoint.ThreeRepsInputs

public section

namespace Certificates.Kernel.Trace6091

open CFSG.KC CFSG.KC.KDense CFSG.KC.Trace6091 CFSG.Monster.B CFSG.Monster.Existence Finset

@[expose] noncomputable def PA : Nat := nat_lit 111812619503779981116236019230164000

theorem pe_PA : ∀ i < 24, pe PA i = permMonoA[i]! := by decide +kernel

theorem oddA_0 : oddScanT PA (betaTabT PA) 0 256 = 24 := by decide +kernel

theorem oddA_0_sum : ∑ j ∈ range 256, ∑ i ∈ range 24,
    xTerm permMonoA (Model.oddCode (2 * (0 + j)) i) (Model.dualN (2 ^ i)) = 24 :=
  (oddScanT_eq pe_PA 0 256).symm.trans oddA_0

theorem oddA_0_ne : oddScanT PA (betaTabT PA) 0 256 ≠ 25 := by decide +kernel

@[expose] noncomputable def PBad : Nat := nat_lit 111812619503779981116236019230163969

theorem oddBad_0 : oddScanT PBad (betaTabT PBad) 0 256 ≠ 24 := by decide +kernel

end Certificates.Kernel.Trace6091

end
