
module

public import Certificates.Kernel.Fi23M.FinalBase
import all Certificates.Kernel.Fi23M.FinalBase

public import Certificates.Kernel.Fi23M.Conj
public import Certificates.Kernel.Fi23M.Action

public section

namespace CFSG.KD.Fi23K

open CertificateChecks.KernelFi23M CFSG.Sporadic.Fi23.Native

theorem fi23_cert :
    fi23Certificate 3 = true := by
  unfold fi23Certificate
  rw [matrixChecks_true]
  dsimp only
  rw [orbitData_eq', conj_okW, action_ok hcard 3, productChecks_true]
  rfl

end CFSG.KD.Fi23K

end
