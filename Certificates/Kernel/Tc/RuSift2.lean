module

public import Certificates.Kernel.Tc.RuSift
public import Certificates.Kernel.SporSch.Ru.JOrb
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTc.Ru

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CertificateChecks.KernelSporSch

theorem kOk3b : allN 28 (fun k => ok3 (Nat.add 3 k)) = true := by quickRfl

theorem kSift3b : allN 28 (fun k => siftJ (R3.F (Nat.add 3 k))) = true := by quickRfl

theorem kRangeS : allN 18 (fun j => allN 4060 fun i => Nat.blt (pg 12 (mask 12) (RuJO.S j) i) 4060) =
    true := by quickRfl

theorem kSiftS : allN 18 (fun j => siftJ (RuJO.S j)) = true := by quickRfl

end CertificateChecks.KernelTc.Ru

end
