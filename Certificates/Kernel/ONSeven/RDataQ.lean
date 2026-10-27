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

#kc_orbrec CertificateChecks.KernelSpor.ONR.Q CertificateChecks.KernelSpor.ONR.Gen.qR
  CertificateChecks.KernelSpor.ONR.Gen.qA 2 10
#kc_nattree CertificateChecks.KernelSpor.ONR.QL CertificateChecks.KernelSpor.ONR.Gen.qL
#kb3_enum CertificateChecks.KernelSpor.ONR.EQ CertificateChecks.KernelSpor.ONR.Gen.qT
  CertificateChecks.KernelSpor.ONR.kbA 687 10

end
