module

public import Certificates.Kernel.TcGen.ON
public import Certificates.Data.Inputs2711eON
public import Certificates.Data.Kernel.GenWf
public import Certificates.Data.Kernel.OpsLayT
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelTc.ON

open CFSG.KC.OpsLayK CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e

theorem gen271102T_K :
    seedsLT lay A B ⟨onGenData.nregs, onGenData.prog, onGenData.facts⟩ 0 1 = true := by
  quickRfl

theorem gen271102T_D : genWf 3 onGenData = true := by
  decide +kernel

end CertificateChecks.KernelTc.ON

end
