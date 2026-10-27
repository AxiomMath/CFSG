module

public import Certificates.Kernel.Om1K.Enum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelOm1.A

open CFSG.KC.Enum
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711.Om1Data

theorem kEG0 : allN 4 (genOK wS0 E0.G) = true := by quickRfl
theorem kEG1 : allN 3 (genOK wP3 E1.G) = true := by quickRfl
theorem kEGa : allN 5 (genOK wSa Ea.G) = true := by quickRfl
theorem kEGa3 : allN wPa3.length (genOK wPa3 Ea3.G) = true := by quickRfl
theorem kEGa5 : allN wPa5.length (genOK wPa5 Ea5.G) = true := by quickRfl
theorem kEGc : allN 4 (genOK wSc Ec.G) = true := by quickRfl
theorem kEGpc : allN wPc.length (genOK wPc Epc.G) = true := by quickRfl
theorem kEGK : allN 4 (genOK k0W EK.G) = true := by quickRfl

theorem kLen : wS0.length = E0.ng ∧ wP3.length = E1.ng ∧ wSa.length = Ea.ng ∧
    wPa3.length = Ea3.ng ∧ wPa5.length = Ea5.ng ∧ wSc.length = Ec.ng ∧ wPc.length = Epc.ng ∧
    k0W.length = EK.ng := by decide +kernel

theorem kN : E0.N = 4096 ∧ E1.N = 27 ∧ Ea.N = 2048 ∧ Ea3.N = 9 ∧ Ea5.N = 5 ∧ Ec.N = 1024 ∧
    Epc.N = 3 ∧ EK.N = 32 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem kSz : CFSG.KS.Raw.szOK 240 8 = true := by quickRfl

end CertificateChecks.KernelOm1.A

end
