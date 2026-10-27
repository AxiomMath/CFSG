module

public import Certificates.Kernel.Sporadic.OddCore.J3Cent
public import Certificates.Data.Kernel.Ivk8CentralN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelIvk8J3

open CFSG.KC.Ivk8N CFSG.KC.YoshQ CertificateChecks.KernelSpor

@[expose] noncomputable def gs : List Nat :=
  [J3CentP 1, J3CentP 2, J3CentP 3, J3CentP 4, J3CentP 5, J3CentP 6, J3CentP 7, J3CentP 8]

theorem j3TwoN_ok : twoOKN 6156 13 gs [1] [2] [1, 6, 8] [6, 3, 8] [4] [-8, -8] = true := by
  quickRfl

theorem j3CenN_ok : centralOKN 6156 13 gs [1] = true := by
  quickRfl

theorem j3EqN_ok : eqN 6156 13 (J3CentP 1) (J3CentP 9) = true := by
  quickRfl

end CertificateChecks.KernelIvk8J3

end
