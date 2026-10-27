module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.GL52.ChainData
meta import Certificates.Kernel.Misc.GL52.ChainData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelMisc.GL52C 31 6 31 CertificateChecks.KernelMisc.GL52K.glStrong
  CertificateChecks.KernelMisc.GL52K.glBase 2 CertificateChecks.KernelMisc.GL52K.glDer

end
