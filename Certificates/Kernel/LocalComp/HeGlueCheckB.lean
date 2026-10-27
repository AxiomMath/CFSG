module

public import Certificates.Kernel.LocalComp.HeGlueDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeGlue

open CFSG.KC.HeGlueK CFSG.KC.HeModelK CFSG.KC.HeAutK CFSG.KC.HexaK CFSG.KC.Enum CFSG.KS
open CFSG.ComponentClassification.AS81.HeTri

theorem kB0 : allR (classBAt hd HeGlueD.WB) 0 768 = true := by quickRfl

theorem kB1 : allR (classBAt hd HeGlueD.WB) 768 768 = true := by quickRfl

theorem kB2 : allR (classBAt hd HeGlueD.WB) 1536 768 = true := by quickRfl

theorem kB3 : allR (classBAt hd HeGlueD.WB) 2304 768 = true := by quickRfl

end CertificateChecks.KernelLC.HeGlue

end
