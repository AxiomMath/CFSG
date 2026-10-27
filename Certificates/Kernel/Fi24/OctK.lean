module

public import Certificates.Data.Kernel.Fi24Oct
public import CFSG.Sporadic.Fi24.OctadData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Fi24.ExtCert

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi24.Oct

open CFSG.KC.Fi24Oct CFSG.Sporadic.Fi24.Native

theorem kA : cardK octMasks.toList = true := by quickRfl

theorem kB : pairK octMasks.toList = true := by quickRfl

theorem kC : treeK octMasks.toList octPar.toList octLab.toList (octPerms[0]!).toList
    (octPerms[1]!).toList = true := by
  quickRfl

end CertificateChecks.KernelFi24.Oct

end
