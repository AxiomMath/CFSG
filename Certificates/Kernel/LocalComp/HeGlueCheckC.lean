module

public import Certificates.Kernel.LocalComp.HeGlueDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeGlue

open CFSG.KC.HeGlueK CFSG.KC.HeModelK CFSG.KC.HeAutK CFSG.KC.HexaK CFSG.KC.Enum CFSG.KS
open CFSG.ComponentClassification.AS81.HeTri

theorem kC0_0 : allR (classCAt hd heRelsP HeGlueD.WR HeGlueD.WC 0) 0 768 = true := by
  quickRfl

theorem kC0_1 : allR (classCAt hd heRelsP HeGlueD.WR HeGlueD.WC 0) 768 768 = true := by
  quickRfl

theorem kC0_2 : allR (classCAt hd heRelsP HeGlueD.WR HeGlueD.WC 0) 1536 768 = true := by
  quickRfl

theorem kC0_3 : allR (classCAt hd heRelsP HeGlueD.WR HeGlueD.WC 0) 2304 768 = true := by
  quickRfl

theorem kC1_0 : allR (classCAt hd heRelsP HeGlueD.WR HeGlueD.WC 1) 0 768 = true := by
  quickRfl

theorem kC1_1 : allR (classCAt hd heRelsP HeGlueD.WR HeGlueD.WC 1) 768 768 = true := by
  quickRfl

theorem kC1_2 : allR (classCAt hd heRelsP HeGlueD.WR HeGlueD.WC 1) 1536 768 = true := by
  quickRfl

theorem kC1_3 : allR (classCAt hd heRelsP HeGlueD.WR HeGlueD.WC 1) 2304 768 = true := by
  quickRfl

theorem kC2_0 : allR (classCAt hd heRelsP HeGlueD.WR HeGlueD.WC 2) 0 768 = true := by
  quickRfl

theorem kC2_1 : allR (classCAt hd heRelsP HeGlueD.WR HeGlueD.WC 2) 768 768 = true := by
  quickRfl

theorem kC2_2 : allR (classCAt hd heRelsP HeGlueD.WR HeGlueD.WC 2) 1536 768 = true := by
  quickRfl

theorem kC2_3 : allR (classCAt hd heRelsP HeGlueD.WR HeGlueD.WC 2) 2304 768 = true := by
  quickRfl

theorem kC3_0 : allR (classCAt hd heRelsP HeGlueD.WR HeGlueD.WC 3) 0 768 = true := by
  quickRfl

theorem kC3_1 : allR (classCAt hd heRelsP HeGlueD.WR HeGlueD.WC 3) 768 768 = true := by
  quickRfl

theorem kC3_2 : allR (classCAt hd heRelsP HeGlueD.WR HeGlueD.WC 3) 1536 768 = true := by
  quickRfl

theorem kC3_3 : allR (classCAt hd heRelsP HeGlueD.WR HeGlueD.WC 3) 2304 768 = true := by
  quickRfl

end CertificateChecks.KernelLC.HeGlue

end
