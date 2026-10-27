module

public import Certificates.Kernel.SmithEK.ChkW
public import Certificates.Kernel.SmithEK.UChecks
public import CFSG.Certificates.Kernel.SmithEK.USound

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE CFSG.SmithE.K

theorem wdM_len : wd.M.length = 891 := by
  decide +kernel

theorem wMask_eq_wd {i : ℕ} (hi : i < 891) : wMask i = wd.M.getD i 0 := by
  have hc : i / 64 < 14 := by omega
  have e := pinChunkK_sound (pins_all (i / 64) hc) (Nat.mod_lt i (by omega : 64 > 0))
    (by rw [wData_len, Nat.div_add_mod]; exact hi)
  rw [Nat.div_add_mod] at e
  exact CFSG.SmithE.KU.wMask_of_pin (by rw [wB_eq, CFSG.SmithL6.Kernel.get0]) e

theorem chkUA_eq : chkUA () = true := by
  refine CFSG.SmithE.KU.chkUA_of (fun i => ua.Y.getD i 0) (fun i hi => ?_) (fun i hi => ?_)
    (fun i hi j hj he => ?_)
  · have h := chkW_eq
    unfold chkW at h
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
    exact h.1.2 i hi
  · have e := CFSG.SmithE.KU.dualK_sound _ _ c21263dual i (by rw [wData_len]; exact hi)
    rwa [wB_eq, CFSG.SmithL6.Kernel.get0]
  · rw [wMask_eq_wd hi, wMask_eq_wd hj] at he
    exact CFSG.SmithE.KU.keyK_sound c21263key (by rw [wdM_len]; exact hi)
      (by rw [wdM_len]; exact hj) (by rw [he])

end CertificateChecks.KernelSmithEK
