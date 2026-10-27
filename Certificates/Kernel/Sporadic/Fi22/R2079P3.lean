module

public import Certificates.Kernel.Sporadic.RawTreeGen
public import Certificates.Kernel.Sporadic.Fi22.W2079
public meta import CFSG.Sporadic.FischerOddCore.FischerOuterFi22CheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22CheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fo22R

meta def p3M : Array Nat := #[0, 1, 2, 4, 3]

end CertificateChecks.KernelSpor.Fo22R

#ks_rawtree CertificateChecks.KernelSpor.Fo22P3 1575 11 64 64 0
  CFSG.Sporadic.FischerOddCore.fo22P3Strong CertificateChecks.KernelSpor.Fo22R.p3M 2
  CertificateChecks.KernelSpor.Fo22W.p3D

end
