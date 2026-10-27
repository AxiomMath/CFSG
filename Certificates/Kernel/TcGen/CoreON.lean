module

public import Certificates.Kernel.TcGen.ON
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreONSevenData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelTc.ON

open CFSG.KC.OpsLayK CFSG.AGLEmbedding.R3

theorem core_K : seedsL lay A B ⟨CoreON7.nregs, CoreON7.prog, CoreON7.spec.facts⟩ CoreON7.spec.rA
    CoreON7.spec.rB = true := by
  quickRfl

end CertificateChecks.KernelTc.ON

end
