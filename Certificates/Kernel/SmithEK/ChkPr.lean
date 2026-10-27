module

public import Certificates.Kernel.SmithEK.PrRowsA
public import Certificates.Kernel.SmithEK.PrRowsB
public import Certificates.Kernel.SmithEK.Span
public import Certificates.Kernel.SmithEK.TvEq
public import CFSG.Certificates.Kernel.SmithEK.PrSound
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

#kc_forall_tree c21115rows_all (fun c => pqChk tp.C pts.L (87 * c) 87 = true) 8
  CertificateChecks.KernelSmithEK.c21115row_

theorem chkProd_eq : CFSG.LargeExtraspecial.S14.SMI.chkProd = true := by
  refine chkProd_of uPts_eq pts_length tp_len (fun k hk => ?_) c21115rows_all
  have hk' : k < pts.L.length := by rw [pts_length]; exact hk
  rw [packOK_sound _ _ _ tp_ok k hk', tvCols_eq, cT_eq, tvW_cTabQ]

end CertificateChecks.KernelSmithEK
