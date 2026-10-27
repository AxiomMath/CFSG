module

public import Certificates.Kernel.LocalComp.HeGlueDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.HeGlue

open CFSG.KC.HeGlueK CFSG.KC.HeModelK CFSG.KC.HeAutK CFSG.KC.HexaK CFSG.KC.Enum CFSG.KS
open CFSG.ComponentClassification.AS81.HeTri

@[expose] noncomputable def kerX (j : Nat) : Bool :=
  kerXAt hd heRelsX heRels23 (Nat.land (HeGlueD.KX j) 7)
    (Nat.land (Nat.shiftRight (HeGlueD.KX j) 3) 7) (Nat.shiftRight (HeGlueD.KX j) 6) j

theorem kX0 : allR kerX 0 768 = true := by quickRfl

theorem kX1 : allR kerX 768 768 = true := by quickRfl

theorem kX2 : allR kerX 1536 768 = true := by quickRfl

theorem kX3 : allR kerX 2304 768 = true := by quickRfl

theorem kX4 : allR kerX 3072 768 = true := by quickRfl

theorem kX5 : allR kerX 3840 768 = true := by quickRfl

theorem kX6 : allR kerX 4608 768 = true := by quickRfl

theorem kX7 : allR kerX 5376 768 = true := by quickRfl

theorem kX8 : allR kerX 6144 768 = true := by quickRfl

theorem kX9 : allR kerX 6912 768 = true := by quickRfl

theorem kX10 : allR kerX 7680 768 = true := by quickRfl

theorem kX11 : allR kerX 8448 768 = true := by quickRfl

end CertificateChecks.KernelLC.HeGlue

end
