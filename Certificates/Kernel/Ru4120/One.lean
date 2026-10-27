module

public import Certificates.Kernel.Ru4120.T
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Ru4120

open CFSG.KC.Kc3K

theorem one : B.all (fun p => exK 12 4095 TF (eu 16) (ev 16) p == p) = true := by quickRfl

end CFSG.KD.Ru4120

end
