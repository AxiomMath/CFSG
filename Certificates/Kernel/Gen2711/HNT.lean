module

public import Certificates.Kernel.FusLay.HN
public import Certificates.Data.Kernel.OpsLayT
public import Certificates.Data.Inputs2711eHN
public import Certificates.Data.Kernel.GenWf
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelFusLay.HN

open CFSG.KC.OpsLayK CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e CFSG.AGLEmbedding.R3
  CFSG.AGLEmbedding.R3.AlphaHN

theorem gen271104T_K :
    seedsLT lay A B ⟨hnGenData.nregs, hnGenData.prog, hnGenData.facts⟩ 0 1 = true := by
  quickRfl

theorem gen271104T_D :
    (genWf 3 hnGenData && hnMod.wf 3 && pcWf (hnTops ++ hnMod.basisPc 3)) = true := by
  decide +kernel

end CertificateChecks.KernelFusLay.HN

end
