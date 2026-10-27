module

public import Certificates.Kernel.B3S3.GenL
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.M12Inputs
public meta import CFSG.Monster.B.Mathieu.Order
public import Certificates.Kernel.SmallSpor.Base012
public meta import Certificates.Kernel.SmallSpor.Base012
public meta import Certificates.Kernel.SmallSpor.TreeGen
public import Certificates.Kernel.SporSch.Th.GenV4
public import CFSG.Assembly.Defs
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.Basic
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreM12
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreModel
public import Certificates.Kernel.SmallSpor.TreeGen

public section

namespace CertificateChecks.KernelSmallSpor.M12

meta def imgs (L : List (Equiv.Perm (Fin 12))) : Array (Array Nat) :=
  (L.map fun g => (CFSG.Monster.B.Mathieu.imageList g).toArray).toArray

meta def k1G : Array (Array Nat) := imgs CFSG.ClassicalInvolution.m12KGens1

meta def u1G : Array (Array Nat) := imgs CFSG.ClassicalInvolution.m12UGens1

meta def k2G : Array (Array Nat) := imgs CFSG.ClassicalInvolution.m12KGens2

meta def n2G : Array (Array Nat) := imgs CFSG.ClassicalInvolution.m12NGens2

meta def u1D : List Nat := CFSG.KC.ListBridgeGen.treeRecs 12 4 u1G

meta def n2D : List Nat := CFSG.KC.ListBridgeGen.treeRecs 12 4 n2G

end CertificateChecks.KernelSmallSpor.M12

end

set_option maxRecDepth 400000

#kb3_enum_l CertificateChecks.KernelSmallSpor.M12.EK1 CertificateChecks.KernelSmallSpor.M12.k1G
  CertificateChecks.KernelSmallSpor.base012 12 4
#kb3_enum_l CertificateChecks.KernelSmallSpor.M12.EU1 CertificateChecks.KernelSmallSpor.M12.u1G
  CertificateChecks.KernelSmallSpor.base012 12 4
#kb3_enum_l CertificateChecks.KernelSmallSpor.M12.EK2 CertificateChecks.KernelSmallSpor.M12.k2G
  CertificateChecks.KernelSmallSpor.base012 12 4
#kb3_enum_l CertificateChecks.KernelSmallSpor.M12.EN2 CertificateChecks.KernelSmallSpor.M12.n2G
  CertificateChecks.KernelSmallSpor.base012 12 4
#kss_natlist CertificateChecks.KernelSmallSpor.M12.UD1 CertificateChecks.KernelSmallSpor.M12.u1D
#kss_natlist CertificateChecks.KernelSmallSpor.M12.ND2 CertificateChecks.KernelSmallSpor.M12.n2D
