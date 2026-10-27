module

public import Certificates.Kernel.Om2K.Enum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm2

open CFSG.KC.Enum
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om2Data

@[expose] noncomputable def genOK (ws : List (List Nat)) (G : Nat → Nat) (k : Nat) : Bool :=
  bAnd(Nat.beq (G k) (wYK (ws.getD k [])), okK (G k))

theorem kEG0 : allN 5 (genOK wS0 E0.G) = true := by quickRfl
theorem kEG1 : allN 3 (genOK wP3 E1.G) = true := by quickRfl
theorem kEG2 : allN 4 (genOK wSc E2.G) = true := by quickRfl
theorem kEG3 : allN 1 (genOK wPc E3.G) = true := by quickRfl
theorem kEG4 : allN 2 (genOK wCR E4.G) = true := by quickRfl

theorem kSz : CFSG.KS.Raw.szOK 480 9 = true := by quickRfl

end CertificateChecks.KernelOm2

end
