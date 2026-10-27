module

public import Certificates.Kernel.SmithEK.PChk
public import Certificates.Kernel.SmithEK.Span
public import CFSG.Certificates.Kernel.SmithEK.PSound

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

theorem chkP_eq : chkP = true := by
  refine chkP_of uPts_eq pts_length (fun k hk => ?_) pchk_ok
  have hk' : k < pts.L.length := by rw [pts_length]; exact hk
  rw [tvCols_eq, ← tvW_cTabQ, ← cT_eq, ← cs_ok]
  simp [List.getD_eq_getElem?_getD, hk']

end CertificateChecks.KernelSmithEK
