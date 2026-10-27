module

public import Certificates.Kernel.Sporadic.OddCore.ON2122W
public meta import Certificates.Kernel.Sporadic.OddCore.ON2122W
public meta import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Sporadic.ONOddCore.LiftHomCheckInputs
public import CFSG.Sporadic.ONOddCore.LiftHomCheckInputs
public meta import Certificates.Kernel.Sporadic.RawGenSch3G
public import Certificates.Kernel.Sporadic.RawGenSch3G

public section

set_option maxRecDepth 400000

#ks_rawchain_sl3g CertificateChecks.KernelSpor.PP3_0 960 10 64 960 0
  CertificateChecks.KernelSpor.ON2122.pS3_0
  CertificateChecks.KernelSpor.ON2122.resBA 3 CertificateChecks.KernelSpor.ON2122.resD (1 2)
  CertificateChecks.KernelSpor.ON2122.resWS
#ks_rawchain_sl3g CertificateChecks.KernelSpor.PP3_1 960 10 64 960 0
  CertificateChecks.KernelSpor.ON2122.pS3_1
  CertificateChecks.KernelSpor.ON2122.resBA 3 CertificateChecks.KernelSpor.ON2122.resD (1 2)
  CertificateChecks.KernelSpor.ON2122.resWS
#ks_rawchain_sl3g CertificateChecks.KernelSpor.PP3_2 960 10 64 960 0
  CertificateChecks.KernelSpor.ON2122.pS3_2
  CertificateChecks.KernelSpor.ON2122.resBA 3 CertificateChecks.KernelSpor.ON2122.resD (1 2)
  CertificateChecks.KernelSpor.ON2122.resWS
#ks_rawchain_sl3g CertificateChecks.KernelSpor.PP3_3 960 10 64 960 0
  CertificateChecks.KernelSpor.ON2122.pS3_3
  CertificateChecks.KernelSpor.ON2122.resBA 3 CertificateChecks.KernelSpor.ON2122.resD (1 2)
  CertificateChecks.KernelSpor.ON2122.resWS

end
