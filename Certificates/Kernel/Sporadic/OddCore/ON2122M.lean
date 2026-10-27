module

public import Certificates.Kernel.Sporadic.OddCore.ON2122W
public meta import Certificates.Kernel.Sporadic.OddCore.ON2122W
public meta import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.RawGen
public meta import CFSG.Sporadic.ONOddCore.LiftHomCheckInputs
public import CFSG.Sporadic.ONOddCore.LiftHomCheckInputs

public section

set_option maxRecDepth 400000

#ks_rawchain CertificateChecks.KernelSpor.PM2122 480 9 64 CertificateChecks.KernelSpor.ON2122.mS
  CertificateChecks.KernelSpor.ON2122.resBA 3 CertificateChecks.KernelSpor.ON2122.resD

end
