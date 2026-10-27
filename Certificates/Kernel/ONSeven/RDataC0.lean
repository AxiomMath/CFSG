module

public import Certificates.Kernel.Sporadic.OrbRecGen
public import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.B3S3.GenSl
public import Certificates.Kernel.ONSeven.RDefs
public meta import Certificates.Kernel.Sporadic.OrbRecGen
public meta import Certificates.Kernel.B3S3.Gen
public meta import Certificates.Kernel.B3S3.GenSl
public meta import Certificates.Kernel.ONSeven.RGen
public meta import Certificates.Kernel.ONSeven.RDefs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0

#kc_orbrec CertificateChecks.KernelSpor.ONR.C0 CertificateChecks.KernelSpor.ONR.Gen.c0R
  CertificateChecks.KernelSpor.ONR.Gen.c0A 4 12
#kc_nattree CertificateChecks.KernelSpor.ONR.X0 CertificateChecks.KernelSpor.ONR.Gen.x0P
#kb3_enum_sl CertificateChecks.KernelSpor.ONR.EC0 CertificateChecks.KernelSpor.ONR.Gen.c0T
  CertificateChecks.KernelSpor.ONR.kbA 2746 12 49
#kb3_enum_sl CertificateChecks.KernelSpor.ONR.EF0 CertificateChecks.KernelSpor.ONR.Gen.f0T
  CertificateChecks.KernelSpor.ONR.kbA 2746 12 49

end
