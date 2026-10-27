module

public import Certificates.Kernel.SmallSpor.M22E8Enum
public import Certificates.Kernel.SmallSpor.M22Data
public import Certificates.Data.Kernel.ListBridgeComm
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSmallSpor.M22

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.ListBridge

theorem numE : Nat.beq EU.N 64 = true ∧ Nat.beq EE.ng 3 = true ∧ Nat.beq EE.N 8 = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem bindE0 : Nat.beq (EE.G 0) (pcommutK 22 5 (EU.G 0) (EU.G 1)) = true := by quickRfl

theorem bindE1 : Nat.beq (EE.G 1) (pcommutK 22 5 (EU.G 0) (EU.G 2)) = true := by quickRfl

theorem bindE2 : Nat.beq (EE.G 2) (pcommutK 22 5 (EU.G 1) (EU.G 2)) = true := by quickRfl

theorem xyCanon : canonK 22 5 (mask 5) (22 * 5) (pcommutK 22 5 (EK.G 0) (EK.G 1)) = true := by
  quickRfl

theorem xyOut : CFSG.KLie.CT.notB (inK EU.N EU.T (pcommutK 22 5 (EK.G 0) (EK.G 1))) = true := by
  quickRfl

theorem powE : powK 22 5 1 EE.N EE.T = true := by quickRfl

theorem abelE : abelPtsK 22 5 EE.N EE.T = true := by quickRfl

theorem commU : commPtsK 22 5 EU.N EU.T EE.N EE.T = true := by quickRfl

theorem abelU_neg : CFSG.KLie.CT.notB (abelPtsK 22 5 EU.N EU.T) = true := by quickRfl

theorem commU_neg : CFSG.KLie.CT.notB (commPtsK 22 5 EU.N EU.T 4 EE.T) = true := by quickRfl

end CertificateChecks.KernelSmallSpor.M22

end
