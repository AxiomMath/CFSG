module

public import Certificates.Kernel.KGC31M24.Defs7217
public import Certificates.Data.Insp443M24

public section

namespace CertificateChecks.KernelInsp443M24

open CFSG.KC.KGC31P CFSG.Quasithin.KGC31.M24 CFSG.SectionRank.QTK.Insp443.M24
open CertificateChecks.KernelKGC31M24

@[expose] noncomputable def gP : Nat := pw gW
@[expose] noncomputable def zP : Nat := pc 24 5 gP (pinv 24 5 d6P)
@[expose] noncomputable def lP : Nat := pw lW
@[expose] noncomputable def xP : Nat := pw xW
@[expose] noncomputable def nP : Nat := pw nW
@[expose] noncomputable def cjP : List Nat := cjW.map pw

@[expose] noncomputable def sixP : List Nat := cAll zP u6P ++ cAll lP (cAll zP u6P)

@[expose] noncomputable def lqP : List Nat := mjW.map fun w => wcj w y7W

end CertificateChecks.KernelInsp443M24
