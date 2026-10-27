module

public import Certificates.Kernel.B3S3.GenL
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.M22Inputs
public meta import CFSG.Monster.B.Mathieu.Order
public import Certificates.Kernel.SmallSpor.Base012
public meta import Certificates.Kernel.SmallSpor.Base012
public meta import Certificates.Kernel.SmallSpor.TreeGen
public import Certificates.Kernel.SporSch.Th.GenV4
public import CFSG.Assembly.Defs
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import Certificates.Kernel.SmallSpor.TreeGen

public section

namespace CertificateChecks.KernelSmallSpor.M22

meta def kG : Array (Array Nat) :=
  (CFSG.ClassicalInvolution.m22KGens1.map fun g =>
    (CFSG.Monster.B.Mathieu.imageList g).toArray).toArray

meta def uG : Array (Array Nat) :=
  (CFSG.ClassicalInvolution.m22UGens1.map fun g =>
    (CFSG.Monster.B.Mathieu.imageList g).toArray).toArray

meta def uD : List Nat := CFSG.KC.ListBridgeGen.treeRecs 22 5 uG

end CertificateChecks.KernelSmallSpor.M22

end

set_option maxRecDepth 400000

#kb3_enum_l CertificateChecks.KernelSmallSpor.M22.EK CertificateChecks.KernelSmallSpor.M22.kG
  CertificateChecks.KernelSmallSpor.base012 22 5
#kb3_enum_l CertificateChecks.KernelSmallSpor.M22.EU CertificateChecks.KernelSmallSpor.M22.uG
  CertificateChecks.KernelSmallSpor.base012 22 5
#kss_natlist CertificateChecks.KernelSmallSpor.M22.UD CertificateChecks.KernelSmallSpor.M22.uD
