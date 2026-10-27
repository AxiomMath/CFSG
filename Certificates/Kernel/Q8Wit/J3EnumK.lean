module

public import Certificates.Kernel.Q8Wit.J3Keys
public import Certificates.Kernel.B3S3.GenKey
public meta import Certificates.Kernel.Q8Wit.J3Keys
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#kb3_enum_key CertificateChecks.KernelQ8W.J3Q CertificateChecks.KernelQ8W.J3.j3Gens
  CertificateChecks.KernelQ8W.J3.j3KeysArr 6156 13 32

public section

namespace CertificateChecks.KernelQ8W.J3

theorem ryNeg : (!CFSG.KC.BfsPin.runSlY 6156 13 J3Q.ng J3Q.N j3KeysArr.toList J3Q.G J3Q.T
    (fun i => J3Q.E (i + 1)) 32 J3Q.C 0) = true := by
  quickRfl

end CertificateChecks.KernelQ8W.J3

end
