module

public import Certificates.Kernel.SmithEK.SpanChk
public import Certificates.Kernel.SmithEK.TvEq
public import CFSG.Certificates.Kernel.SmithEK.SpanSound

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

theorem pts_length : pts.L.length = 693 := by
  decide +kernel

theorem tvW_length (p : Nat) : (tvW cT.L p).length = 20 := by
  rw [cT_eq]
  simp [tvW, hQ, cTabQ]

theorem chkSpan_eq_true : chkSpan = true := by
  apply chkSpan_of
  intro k hk
  rw [tvCols_eq, ← tvW_cTabQ, ← cT_eq]
  apply spanOKA_of (tvW_length _)
  have hk' : k < pts.L.length := by rw [pts_length]; exact hk
  rw [List.getD_eq_getElem _ _ hk']
  exact List.all_eq_true.1 spanW_ok _ (List.getElem_mem hk')

end CertificateChecks.KernelSmithEK
