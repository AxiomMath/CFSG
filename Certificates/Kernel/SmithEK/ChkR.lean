module

public import Certificates.Kernel.SmithEK.DRowsA
public import Certificates.Kernel.SmithEK.DRowsB
public import Certificates.Kernel.SmithEK.DRowsC
public import Certificates.Kernel.SmithEK.RChk
public import Certificates.Kernel.SmithEK.ChkD2
public import Certificates.Kernel.SmithEK.ChkT
public import CFSG.Certificates.Kernel.SmithEK.RSound
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

#kc_forall_tree drows_all (fun c => dChunkK pb.P wd.M (27 * c) 27 = true) 33
  CertificateChecks.KernelSmithEK.c21261row_

theorem chkDist_eq : chkDist = true := by
  refine chkDist_of uPts_eq pts_length pb_len (fun _ hi => pb_get hi)
    (fun _ hi => (wMask_eq_wd hi).symm) (fun i hi => ?_)
  have hc : i / 27 < 33 := by omega
  have h1 : 27 * (i / 27) ≤ i := by omega
  have h2 : i < 27 * (i / 27) + 27 := by omega
  exact dChunkK_sound (drows_all (i / 27) hc) h1 h2

theorem chkRank_eq : chkRank = true :=
  chkRank_of uPts_eq pts_length (fun _ hi => pb_get hi) c21261rank

theorem chkSpanW_eq : chkSpanW = true :=
  chkSpanW_of (fun _ hi => wtArr_wd hi) c21261span

end CertificateChecks.KernelSmithEK
