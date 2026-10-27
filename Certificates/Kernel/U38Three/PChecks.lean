module

public import Certificates.Kernel.U38Three.PData
public import Certificates.Data.Kernel.U38ThreeK
public import Certificates.Data.Kernel.U38QK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU38Three

open CFSG.KC.Enum CFSG.KS CFSG.KC.U38QK CFSG.KC.U38ThreeK

@[expose] noncomputable def rI (k : Nat) : Nat := RI.getD k 0

theorem ch810201PNums : (Nat.beq PE.N 504 && Nat.beq PE.ng 2 && Nat.beq RI.length 8) = true := by
  quickRfl

theorem ch810201Q0 : repOK 9 4 12 504 PE.T (rI 0) Q0.N Q0.ng Q0.G = true := by quickRfl
theorem ch810201Q1 : repOK 9 4 12 504 PE.T (rI 1) Q1.N Q1.ng Q1.G = true := by quickRfl
theorem ch810201Q2 : repOK 9 4 12 504 PE.T (rI 2) Q2.N Q2.ng Q2.G = true := by quickRfl
theorem ch810201Q3 : repOK 9 4 12 504 PE.T (rI 3) Q3.N Q3.ng Q3.G = true := by quickRfl
theorem ch810201Q4 : repOK 9 4 12 504 PE.T (rI 4) Q4.N Q4.ng Q4.G = true := by quickRfl
theorem ch810201Q5 : repOK 9 4 12 504 PE.T (rI 5) Q5.N Q5.ng Q5.G = true := by quickRfl
theorem ch810201Q6 : repOK 9 4 12 504 PE.T (rI 6) Q6.N Q6.ng Q6.G = true := by quickRfl
theorem ch810201Q7 : repOK 9 4 12 504 PE.T (rI 7) Q7.N Q7.ng Q7.G = true := by quickRfl

theorem ch810201Cover : pairK (coverK 9 4 504 8 PE.T rI) (List.range 504) CH = true := by
  quickRfl

end CertificateChecks.KernelU38Three

end
