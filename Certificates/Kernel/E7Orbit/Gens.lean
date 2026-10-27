module

public import Certificates.Data.Kernel.E7Orbit.Check
public import Certificates.Data.OmegaSevenMax.RootCodes
public import Certificates.Kernel.E7Orbit.Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelE7Orbit

open CFSG.KC.E7Orbit CFSG.KC.Enum

@[expose] noncomputable def rootM (b : Nat) : Nat := msk (recAt T (MS b))

theorem bindH0 : bindOK NT (hP 0) 0 = true := by quickRfl
theorem bindH1 : bindOK NT (hP 1) 1 = true := by quickRfl
theorem bindH2 : bindOK NT (hP 2) 2 = true := by quickRfl
theorem bindH3 : bindOK NT (hP 3) 3 = true := by quickRfl
theorem bindH4 : bindOK NT (hP 4) 4 = true := by quickRfl
theorem bindH5 : bindOK NT (hP 5) 5 = true := by quickRfl
theorem u0 : Nat.beq (rootM 0) (wordMask 0 Certificates.OmegaSevenMax.rootCodes) = true := by
  quickRfl
theorem roots : allN 3 (fun c => Nat.beq (rootM (Nat.succ c))
    (wordMask (MS (Nat.add 4 c)) Certificates.OmegaSevenMax.rootCodes)) = true := by quickRfl
theorem hfix : allN 6 (fun j => Nat.beq (img (NT j) (rootM 0)) (rootM 0)) = true := by quickRfl
theorem cnt : cntOK T = true := by quickRfl

end CertificateChecks.KernelE7Orbit

end
