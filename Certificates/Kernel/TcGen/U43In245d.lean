module

public import Certificates.Data.Inputs245dU43
public import Certificates.Kernel.TcGen.Small3
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelTc.In245d

open CFSG.KC.OpsLayK CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs245d

theorem cp_K : seedsL U43.lay U43.A U43.B ⟨nregs, cpProg, cpSpec.facts⟩ cpSpec.rA cpSpec.rB =
    true := by
  quickRfl

end CertificateChecks.KernelTc.In245d

end
