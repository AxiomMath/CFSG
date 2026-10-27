module

public import Certificates.Kernel.SmallSpor.M23Data
public import Certificates.Kernel.SporSch.Mathieu.M23Data
public import Certificates.Data.Kernel.ListBridge
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSmallSpor.M23

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.ListBridge

@[expose] def uWords : List (List Int) :=
  [[3, 3, 3], [2, 3, 2, 3], [1, 3, 3, 3, 1], [1, 3, 1, 3, 1, 3]]

theorem nums : Nat.beq EK.ng 4 = true ∧ Nat.beq EU.ng 4 = true ∧ Nat.beq EU.N 16 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem bindK : allN 4 (fun j => Nat.beq (EK.G j) (CertificateChecks.KernelSporSch.M23C1.S j)) =
    true := by quickRfl

theorem posU : allN 4 (fun j => posW 4 (uWords.getD j [])) = true := by decide +kernel

theorem bindU : allN 4 (fun j => Nat.beq (EU.G j) (pwordK 23 5 EK.G (uWords.getD j []))) =
    true := by quickRfl

theorem pow : powK 23 5 4 EU.N EU.T = true := by quickRfl

theorem norm : allN EK.ng (fun j => normK 23 5 EU.N EU.T (EK.G j)) = true := by quickRfl

theorem self : selfK 23 5 EK.N EK.T EU.ng EU.G EU.N EU.T = true := by quickRfl

end CertificateChecks.KernelSmallSpor.M23

end
