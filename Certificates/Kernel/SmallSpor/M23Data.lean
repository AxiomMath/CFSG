module

public import Certificates.Kernel.B3S3.GenL
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.M23Inputs
public meta import CFSG.Monster.B.Mathieu.Order
public import Certificates.Kernel.SmallSpor.Bases
public meta import Certificates.Kernel.SmallSpor.Bases
public import CFSG.Assembly.Defs
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CertificateChecks.KernelSmallSpor.M23

meta def kG : Array (Array Nat) :=
  (CFSG.ClassicalInvolution.m23KGens1.map fun g =>
    (CFSG.Monster.B.Mathieu.imageList g).toArray).toArray

meta def uG : Array (Array Nat) :=
  (CFSG.ClassicalInvolution.m23UGens1.map fun g =>
    (CFSG.Monster.B.Mathieu.imageList g).toArray).toArray

end CertificateChecks.KernelSmallSpor.M23

end

set_option maxRecDepth 400000

#kb3_enum_l CertificateChecks.KernelSmallSpor.M23.EK CertificateChecks.KernelSmallSpor.M23.kG
  CertificateChecks.KernelSmallSpor.m23Base 23 5
#kb3_enum_l CertificateChecks.KernelSmallSpor.M23.EU CertificateChecks.KernelSmallSpor.M23.uG
  CertificateChecks.KernelSmallSpor.m23Base 23 5
