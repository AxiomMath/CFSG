module

public import Certificates.Kernel.SmallSpor.M12Data
public import Certificates.Kernel.SporSch.Mathieu.M12Data
public import Certificates.Data.Kernel.ListBridge
public import Certificates.Data.Kernel.ListBridgeTree
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSmallSpor.M12

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.ListBridge
open CFSG.KLie.CT (notB)

@[expose] def u1Words : List (List Int) := [[1], [3, 3], [2, 4, 3], [4, 3, 2], [2, 2, 3, 4]]

@[expose] def n2Words : List (List Int) := [[1], [3]]

theorem nums : Nat.beq EK1.ng 4 = true ∧ Nat.beq EU1.ng 5 = true ∧ Nat.beq EK2.ng 3 = true ∧
    Nat.beq EN2.ng 2 = true := ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem bindK1 : allN 4 (fun j => Nat.beq (EK1.G j) (CertificateChecks.KernelSporSch.M12C1.S j)) =
    true := by quickRfl

theorem bindK2 : allN 3 (fun j => Nat.beq (EK2.G j) (CertificateChecks.KernelSporSch.M12C2.S j)) =
    true := by quickRfl

theorem posU1 : allN 5 (fun j => posW 4 (u1Words.getD j [])) = true := by decide +kernel

theorem posN2 : allN 2 (fun j => posW 3 (n2Words.getD j [])) = true := by decide +kernel

theorem bindU1 : allN 5 (fun j => Nat.beq (EU1.G j) (pwordK 12 4 EK1.G (u1Words.getD j []))) =
    true := by quickRfl

theorem bindN2 : allN 2 (fun j => Nat.beq (EN2.G j) (pwordK 12 4 EK2.G (n2Words.getD j []))) =
    true := by quickRfl

theorem depthU1 : depthK 12 4 EU1.ng EU1.G EU1.T EU1.N 20 UD1 = true := by quickRfl

theorem depthN2 : depthK 12 4 EN2.ng EN2.G EN2.T EN2.N 20 ND2 = true := by quickRfl

theorem powU1 : powK 12 4 5 EU1.N EU1.T = true := by quickRfl

theorem normU1 : allN EK1.ng (fun j => normK 12 4 EU1.N EU1.T (EK1.G j)) = true := by quickRfl

theorem selfU1 : selfK 12 4 EK1.N EK1.T EU1.ng EU1.G EU1.N EU1.T = true := by quickRfl

theorem card2 : Nat.beq EK2.N (2 * EN2.N) = true := by quickRfl

theorem canonR : canonK 12 4 (mask 4) (12 * 4) CertificateChecks.KernelSporSch.M12OC.R1 = true := by
  quickRfl

theorem outR : notB (inK EN2.N EN2.T CertificateChecks.KernelSporSch.M12OC.R1) = true := by
  quickRfl

end CertificateChecks.KernelSmallSpor.M12

end
