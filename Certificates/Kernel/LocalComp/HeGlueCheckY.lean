module

public import Certificates.Kernel.LocalComp.HeGlueDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeGlue

open CFSG.KC.HeGlueK CFSG.KC.HeModelK CFSG.KC.HeAutK CFSG.KC.HexaK CFSG.KC.Enum CFSG.KS
open CFSG.ComponentClassification.AS81.HeTri

@[expose] noncomputable def kerY (j : Nat) : Bool := kerYAt hd heRelsY (HeGlueD.KY j) j

theorem kY0 : allR kerY 0 768 = true := by quickRfl

theorem kY1 : allR kerY 768 768 = true := by quickRfl

theorem kY2 : allR kerY 1536 768 = true := by quickRfl

theorem kY3 : allR kerY 2304 768 = true := by quickRfl

theorem kY4 : allR kerY 3072 768 = true := by quickRfl

theorem kY5 : allR kerY 3840 768 = true := by quickRfl

theorem kY6 : allR kerY 4608 768 = true := by quickRfl

theorem kY7 : allR kerY 5376 768 = true := by quickRfl

theorem kY8 : allR kerY 6144 768 = true := by quickRfl

theorem kY9 : allR kerY 6912 768 = true := by quickRfl

theorem kY10 : allR kerY 7680 768 = true := by quickRfl

theorem kY11 : allR kerY 8448 768 = true := by quickRfl

end CertificateChecks.KernelLC.HeGlue

end
