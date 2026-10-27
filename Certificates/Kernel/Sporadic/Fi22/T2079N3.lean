module

public import Certificates.Kernel.Sporadic.ConjTreeGen
public import Certificates.Kernel.Sporadic.Fi22.R2079N3
public import Certificates.Kernel.Sporadic.Fi22.R2079P3
public import Certificates.Kernel.Sporadic.Fi22.D2079
public meta import CFSG.Sporadic.FischerOddCore.FischerOuterFi22CheckInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fo22R

meta def g3M : Array (Array Nat) :=
  #[CFSG.Sporadic.FischerOddCore.fo22N3Strong[0]!, CFSG.Sporadic.FischerOddCore.fo22N3Strong[1]!]

end CertificateChecks.KernelSpor.Fo22R

#ks_conjtree CertificateChecks.KernelSpor.Fo22T3 3510 12 2 64 CertificateChecks.KernelSpor.Fo22R.g3M
  CFSG.Sporadic.FischerOddCore.fo22S03 CFSG.Sporadic.FischerOddCore.fo22Tree3
  CertificateChecks.KernelSpor.Fo22N3.S CertificateChecks.KernelSpor.Fo22N3.SI
  CertificateChecks.KernelSpor.Fo22T.Tree3.F 12 CertificateChecks.KernelSpor.Fo22P3.S 11

end
