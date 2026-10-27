module

public import Certificates.Kernel.Heis.C9707
public import Certificates.Data.Kernel.OuterN
public import CFSG.LieType.SeitzGeneration.OuterSmallData5

public section

set_option maxRecDepth 1000000

namespace CertificateChecks.KernelHeis

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisWords CFSG.KC.HeisN

theorem outer5_k :
    (fkP 5).outerN 5 5 rawGens5 words1_5 (decodeL W5.chars) outerRaw5 = true := by
  decide +kernel

end CertificateChecks.KernelHeis
