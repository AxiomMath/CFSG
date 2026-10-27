module

public import Certificates.Kernel.Ivk8J3.Checks
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import CFSG.Certificates.Kernel.Ivk8CentralNSound
public import Certificates.Data.GH74.Ivk8J3

public section

namespace CertificateChecks.KernelIvk8J3

open CFSG.KC.Enum CFSG.KC.YoshQ CFSG.KC.Ivk8N Certificates.Ivk8Two.J3 CertificateChecks.KernelSpor
  CFSG.Sporadic.SmallOddCore CFSG.KS.MulH

theorem dims : Dims 6156 13 := ⟨by decide, by decide, by decide, by decide⟩

theorem cent_eq {k : Nat} (hk : k < 31) : j3CentTbl k = tabN 6156 13 (J3CentP k) := by
  rw [← tabT_unpack (n := 6156) (w := 13), ← OddCore.j3CentTbl_eq hk, tabT_natArr]

theorem gensT_eq : gensT = gs.map (tabN 6156 13) := by
  unfold gensT gs
  rw [cent_eq (k := 1) (by norm_num), cent_eq (k := 2) (by norm_num),
    cent_eq (k := 3) (by norm_num), cent_eq (k := 4) (by norm_num),
    cent_eq (k := 5) (by norm_num), cent_eq (k := 6) (by norm_num),
    cent_eq (k := 7) (by norm_num), cent_eq (k := 8) (by norm_num)]
  rfl

theorem j3TwoOK_true : j3TwoOK = true := by
  unfold j3TwoOK
  rw [gensT_eq, twoOKT_tabN dims, centralOKT_tabN dims, cent_eq (k := 1) (by norm_num),
    cent_eq (k := 9) (by norm_num), tblEq_tabN' dims, j3TwoN_ok, j3CenN_ok, j3EqN_ok]
  rfl

end CertificateChecks.KernelIvk8J3

end
