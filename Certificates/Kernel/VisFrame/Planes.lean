module

public import Certificates.Kernel.AxisPlane.Cmd
public import Certificates.Data.Kernel.VisFrame.Gens

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelAP.VisFrame

#kc_planes CertificateChecks.KernelAP.VisFrame R CFSG.KC.VisFrame.reps CFSG.KC.VisFrame.sizes
  CFSG.KC.VisFrame.gen0 CFSG.KC.VisFrame.gen1

end CertificateChecks.KernelAP.VisFrame

end
