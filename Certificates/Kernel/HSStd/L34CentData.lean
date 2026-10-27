module

public import Certificates.Kernel.HSStd.L34CentGen
public import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Kernel.HSStd.L34CentGen
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

public section

set_option maxRecDepth 400000

#kc_items CertificateChecks.KernelHSStd.L34C.X include_bytes "data/L34CentData.X.items" 1550 1286956489558617852
#kc_items CertificateChecks.KernelHSStd.L34C.P include_bytes "data/L34CentData.P.items" 8616 10233573296777842347
#kmisc_packarrs CertificateChecks.KernelHSStd.L34C.CC
  CertificateChecks.KernelHSStd.L34CentGen.c3Cnt 8

end
