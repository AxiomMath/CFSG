module

public import Certificates.Kernel.B3S3.GenL
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22E8Data
public meta import CFSG.Monster.B.Mathieu.Order
public import Certificates.Kernel.SmallSpor.Base012
public meta import Certificates.Kernel.SmallSpor.Base012
public import CFSG.Assembly.Defs
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CertificateChecks.KernelSmallSpor.M22

meta def eG : Array (Array Nat) :=
  (CFSG.ClassicalInvolution.m22E8CommGens.map fun g =>
    (CFSG.Monster.B.Mathieu.imageList g).toArray).toArray

end CertificateChecks.KernelSmallSpor.M22

end

set_option maxRecDepth 400000

#kb3_enum_l CertificateChecks.KernelSmallSpor.M22.EE CertificateChecks.KernelSmallSpor.M22.eG
  CertificateChecks.KernelSmallSpor.base012 22 5
