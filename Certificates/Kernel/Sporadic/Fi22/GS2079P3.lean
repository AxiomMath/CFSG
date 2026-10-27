module

public import Certificates.Kernel.Sporadic.GraphSepGen
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22CheckInputs
public meta import CFSG.Sporadic.FischerOddCore.FischerOuterFi22CheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fo22R

meta def p3G : Array Nat := #[0, 1, 2, 4, 3]

end CertificateChecks.KernelSpor.Fo22R

#ks_graphsep CertificateChecks.KernelSpor.Fo22GP3 1575 11 64
  CFSG.Sporadic.FischerOddCore.fo22P3Strong CertificateChecks.KernelSpor.Fo22R.p3G 27

end
