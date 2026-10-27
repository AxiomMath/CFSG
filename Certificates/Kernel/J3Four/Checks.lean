module

public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import Certificates.Kernel.J3Four.Data
public import Certificates.Data.Kernel.J3Four
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.J3Four

open CertificateChecks.KernelSpor CFSG.KC.YoshQ

@[expose] noncomputable def g1 : List Nat :=
  [J3CentP 10, J3CentP 11, J3CentP 12, J3CentP 13, J3CentP 14]

@[expose] noncomputable def g1i : List Nat :=
  [J3CentI 10, J3CentI 11, J3CentI 12, J3CentI 13, J3CentI 14]

@[expose] noncomputable def g2 : List Nat := [J3CentP 22, J3CentP 23, J3CentP 24]

@[expose] noncomputable def g2i : List Nat := [J3CentI 22, J3CentI 23, J3CentI 24]

theorem row1_ok : rowK g1 g1i [1, 3, 4] 5 [1] r1R 192 = true := by
  quickRfl

theorem cent1_ok : centralOK g1 (J3CentP 9) = true := by
  quickRfl

theorem rep1_ok : eqN 6156 13 (J3CentP 9) (J3CentP 10) = true := by
  quickRfl

theorem row2_ok : rowK g2 g2i [0, 1, 2, 1, 2] 17 [0, 1] r2R 144 = true := by
  quickRfl

end CFSG.KD.J3Four

end
