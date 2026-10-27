module

public import Certificates.Kernel.Heis.C9707
public import Certificates.Data.Kernel.OuterN
public import CFSG.LieType.SeitzGeneration.OuterSmallData11

public section

set_option maxRecDepth 1000000

namespace CertificateChecks.KernelHeis

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisWords CFSG.KC.HeisN

theorem outer11_k :
    (fkP 11).outerN 11 11 rawGens11 words1_11 (decodeL W11.chars) outerRaw11 = true := by
  decide +kernel

end CertificateChecks.KernelHeis
