module

public import Certificates.Kernel.He4049.T
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.He4049

open CFSG.KC.Kc3K

theorem one : B.all (fun p => exK 14 16383 TF (eu 0) (ev 0) p == p) = true := by quickRfl

end CFSG.KD.He4049

end
