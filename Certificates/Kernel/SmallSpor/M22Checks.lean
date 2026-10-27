module

public import Certificates.Kernel.SmallSpor.M22Data
public import Certificates.Kernel.SporSch.Mathieu.M22Data
public import Certificates.Data.Kernel.ListBridge
public import Certificates.Data.Kernel.ListBridgeTree
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSmallSpor.M22

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.ListBridge

@[expose] def uWords : List (List Int) := [[1, 1], [3, 3], [3, 2, 1]]

theorem nums : Nat.beq EK.ng 3 = true ∧ Nat.beq EU.ng 3 = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem bindK : allN 3 (fun j => Nat.beq (EK.G j) (CertificateChecks.KernelSporSch.M22C1.S j)) =
    true := by quickRfl

theorem posU : allN 3 (fun j => posW 3 (uWords.getD j [])) = true := by decide +kernel

theorem bindU : allN 3 (fun j => Nat.beq (EU.G j) (pwordK 22 5 EK.G (uWords.getD j []))) =
    true := by quickRfl

theorem depth : depthK 22 5 EU.ng EU.G EU.T EU.N 20 UD = true := by quickRfl

theorem pow : powK 22 5 6 EU.N EU.T = true := by quickRfl

theorem norm : allN EK.ng (fun j => normK 22 5 EU.N EU.T (EK.G j)) = true := by quickRfl

theorem self : selfK 22 5 EK.N EK.T EU.ng EU.G EU.N EU.T = true := by quickRfl

end CertificateChecks.KernelSmallSpor.M22

end
