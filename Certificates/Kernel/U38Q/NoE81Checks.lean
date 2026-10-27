module

public import Certificates.Kernel.U38Q.NoE81Data
public import Certificates.Data.Kernel.U38NoE81K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU38Q

open CFSG.KC.Enum CFSG.KS CFSG.KC.U38QK CFSG.KC.U38NoE81K CFSG.KS.PEnum

theorem q211CU : selFrom (fun i => cubeK 513 10 (QE.T i)) 729 0 CU = true := by quickRfl

theorem q211CW : pairK (cenOK 513 10 [0, 167, 270] QE.T 729) CU CW = true := by quickRfl

theorem q211Big : Nat.ble (bigK CW) 80 = true := by quickRfl

theorem q211WLt : allL (fun j => Nat.blt j 729) WA = true ∧ allL (fun j => Nat.blt j 729) WB = true :=
  ⟨by quickRfl, by quickRfl⟩

end CertificateChecks.KernelU38Q

end
