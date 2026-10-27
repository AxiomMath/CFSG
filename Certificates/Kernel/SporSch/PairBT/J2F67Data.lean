module

public import Certificates.Kernel.SporSch.Pair.J2Chain
public import Certificates.Kernel.SporSch.PairBT.GenSyl
public import Certificates.Kernel.SporSch.PairBT.GenSylElts
public import Certificates.Data.Kernel.SporSch.MathieuBT
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.J2F67

meta def r5Hint : String := include_str "J2F67R5.txt"

meta def r7Hint : String := include_str "J2F67R7.txt"

meta def syl5Hint : String := include_str "J2F67S5.txt"

end CertificateChecks.KernelSporSch.J2F67

#kss_reps CertificateChecks.KernelSporSch.J2F67R 315 9 CertificateChecks.KernelSporSch.J2F67.r5Hint

#kss_reps CertificateChecks.KernelSporSch.J2F67Z 315 9 CertificateChecks.KernelSporSch.J2F67.r7Hint

namespace CertificateChecks.KernelSporSch.J2F67

@[expose] noncomputable def R1 : Nat := CertificateChecks.KernelSporSch.J2F67R.XL.getD 0 0

@[expose] noncomputable def R2 : Nat := CertificateChecks.KernelSporSch.J2F67R.XL.getD 1 0

@[expose] noncomputable def R3 : Nat := CertificateChecks.KernelSporSch.J2F67R.XL.getD 2 0

@[expose] noncomputable def R4 : Nat := CertificateChecks.KernelSporSch.J2F67R.XL.getD 3 0

@[expose] noncomputable def RL5 : List Nat := [R1, R2, R3, R4]

@[expose] noncomputable def Z7 : Nat := CertificateChecks.KernelSporSch.J2F67Z.XL.getD 0 0

@[expose] noncomputable def V : Nat := CertificateChecks.KernelSporSch.J2F67Z.XL.getD 1 0

end CertificateChecks.KernelSporSch.J2F67

end
