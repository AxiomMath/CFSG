module

public import Certificates.Kernel.SmithEK.WPins
public import Certificates.Kernel.SmithEK.WRowsA
public import Certificates.Kernel.SmithEK.WRowsB
public import CFSG.Certificates.Kernel.SmithEK.WSound
import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

#kc_forall_tree pins_all (fun c => pinChunkK wData.toList wd.W wd.M (64 * c) 64 = true) 14
  CertificateChecks.KernelSmithEK.c21104pin_

#kc_forall_tree rows_all (fun c => chunkK wd.W wd.M (16 * c) 16 = true) 56
  CertificateChecks.KernelSmithEK.c21104row_

theorem chkW_eq : chkW = true := by
  refine chkW_of (M := wd.M) wd_len wd_ok (fun i hi => ?_) (fun i hi => ?_)
  · have hc : i / 64 < 14 := by omega
    have e := pinChunkK_sound (pins_all (i / 64) hc) (Nat.mod_lt i (by omega : 64 > 0))
      (by rw [wData_len, Nat.div_add_mod]; exact hi)
    rwa [Nat.div_add_mod] at e
  · have hc : i / 16 < 56 := by omega
    have e := chunkK_sound (rows_all (i / 16) hc) (Nat.mod_lt i (by omega : 16 > 0))
      (by rw [wd_len, Nat.div_add_mod]; exact hi)
    rwa [Nat.div_add_mod] at e

end CertificateChecks.KernelSmithEK
