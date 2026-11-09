module

public import Certificates.Data.Kernel.SmithEKS
public import Certificates.Kernel.SmithEK.Pts
public import Certificates.Kernel.SmithEK.Tab
import CFSG.Certificates.Kernel.Common.AllChunks
import CFSG.Certificates.Kernel.Common.Cover

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

theorem spanW_q : ∀ k < 8, ((pts.L.drop (k * 87)).take 87).all (fun p => spanOKL (tvW cT.L p)) =
    true := by
  kc_cover 1

theorem spanW_len : pts.L.length ≤ 8 * 87 := by decide +kernel

theorem spanW_ok : pts.L.all (fun p => spanOKL (tvW cT.L p)) = true :=
  CFSG.KC.AllChunks.all_of_chunks pts.L _ 87 8 spanW_len spanW_q

theorem spanW_neg_id : spanOKL ((List.range 20).map (2 ^ ·)) = false := by
  decide +kernel

theorem spanW_neg_col : spanOKL ((tvW cT.L (pts.L.getD 0 0)).set 3 0) = false := by
  decide +kernel

end CertificateChecks.KernelSmithEK
