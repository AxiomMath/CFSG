module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Sporadic.Fi22.W2079
public meta import CFSG.Sporadic.FischerOddCore.FischerOuterFi22CheckInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.FischerOddCore.FischerOuterFi22CheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fo22R

meta def p4M : Array Nat := #[0, 1, 2, 4, 3, 5]

meta def p2M : Array Nat := #[0, 1, 2, 3, 5, 7]

end CertificateChecks.KernelSpor.Fo22R

#ks_rawchain CertificateChecks.KernelSpor.Fo22P4 63 7 8
  CFSG.Sporadic.FischerOddCore.fo22P4Strong CertificateChecks.KernelSpor.Fo22R.p4M 2
  CertificateChecks.KernelSpor.Fo22W.p4D

#ks_rawchain CertificateChecks.KernelSpor.Fo22P2 27 5 8
  CFSG.Sporadic.FischerOddCore.fo22P2Strong CertificateChecks.KernelSpor.Fo22R.p2M 3
  CertificateChecks.KernelSpor.Fo22W.p2D

end
