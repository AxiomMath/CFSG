module

public import Certificates.Kernel.Sporadic.OrbRecGen
public import Certificates.Kernel.B3S3.Gen
public import Certificates.Kernel.ONSeven.RDefs
public meta import Certificates.Kernel.Sporadic.OrbRecGen
public meta import Certificates.Kernel.B3S3.Gen
public meta import Certificates.Kernel.ONSeven.RGen
public meta import Certificates.Kernel.ONSeven.RDefs
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

set_option maxRecDepth 400000

#kc_orbrec CertificateChecks.KernelSpor.ONR.C3 CertificateChecks.KernelSpor.ONR.Gen.c3R
  CertificateChecks.KernelSpor.ONR.Gen.c3A 2 7
#kb3_enum CertificateChecks.KernelSpor.ONR.EC3 CertificateChecks.KernelSpor.ONR.Gen.c3T
  CertificateChecks.KernelSpor.ONR.kbA 99 7
#kc_orbrec CertificateChecks.KernelSpor.ONR.C4 CertificateChecks.KernelSpor.ONR.Gen.c4R
  CertificateChecks.KernelSpor.ONR.Gen.c4A 2 7
#kb3_enum CertificateChecks.KernelSpor.ONR.EC4 CertificateChecks.KernelSpor.ONR.Gen.c4T
  CertificateChecks.KernelSpor.ONR.kbA 99 7

end
