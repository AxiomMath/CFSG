module

public import Certificates.Kernel.O8Sq.WitData
public import Certificates.Data.Kernel.O8SqForest
public import Certificates.Kernel.OmegaEight.Arr3009K
public import Certificates.Data.O8p2NoDatum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8Sq

open CFSG.KC.Enum CFSG.KS CFSG.KC.PCent CFSG.KC.O8Sq CertificateChecks.KernelO8
  CFSG.ClassicalInvolution.O8Data

@[expose] noncomputable def sGK (k : Nat) : Nat := AP.S (Nat.mul 2 k)

@[expose] noncomputable def repW (j : Nat) : Nat := wordK 360 9 sGK (RW.getD j [])

@[expose] noncomputable def witJ (j : Nat) : Bool :=
  strictB (repW j) (fun r => strictB (wordK 360 9 AP.S (HW.getD j []).reverse) (fun h =>
    Nat.beq (pc9 r r) (pc9 h (pc9 (mainK (IW.getD j (0, 0)).1) (pi9 h))) &&
    witOneK r h (wO ((witWords.getD (IW.getD j (0, 0)).1 []).getD (IW.getD j (0, 0)).2 []))))

theorem ch272020w : (Nat.beq RW.length 57 && allN 57 witJ) = true := by quickRfl

theorem ch272020fw : (forestK 360 9 sGK sGK 4 repW 57 FW && Nat.beq FW.length 3344) = true := by
  quickRfl

end CertificateChecks.KernelO8Sq

end
