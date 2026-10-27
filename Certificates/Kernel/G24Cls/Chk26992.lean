module

public import Certificates.Kernel.G24Tri.Chain27206
public import Certificates.Data.Kernel.G24Word
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option profiler true
set_option profiler.threshold 100

namespace CertificateChecks.KernelG24.Dih26992

open CFSG.KC.Enum CFSG.KC.G24Key CFSG.KC.G24Word CertificateChecks.KernelG24.Tri27206

@[expose] def u26 : List Nat := [2]

@[expose] def v26 : List Nat := [5, 5, 2, 4, 4, 2, 5, 5, 3, 4, 4]

@[expose] noncomputable def L26 : Nat → Nat := letC (LC.S 0) (LC.SI 0) (LC.S 1) (LC.SI 1)

theorem kD8 : (lettersK u26 && lettersK v26 && fixB L26 (u26 ++ u26) && fixB L26 (v26 ++ v26) &&
    fixB L26 (u26 ++ v26 ++ (u26 ++ v26) ++ (u26 ++ v26) ++ (u26 ++ v26)) &&
    diffB L26 (u26 ++ v26) (v26 ++ u26) 0) = true := by
  quickRfl

end CertificateChecks.KernelG24.Dih26992

end
