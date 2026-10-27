module

public import Certificates.Kernel.Sporadic.RawTreeGen
public import Certificates.Kernel.Sporadic.Fi22.W2079
public meta import CFSG.Sporadic.FischerOddCore.FischerOuterFi22CheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22CheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fo22R

meta def n4xM : Array Nat := #[0, 1, 2, 3, 6, 4]

end CertificateChecks.KernelSpor.Fo22R

#ks_rawtree CertificateChecks.KernelSpor.Fo22N4x 3510 12 64 64 0
  CFSG.Sporadic.FischerOddCore.fo22N4Strong CertificateChecks.KernelSpor.Fo22R.n4xM 2
  CertificateChecks.KernelSpor.Fo22W.n4D

end
