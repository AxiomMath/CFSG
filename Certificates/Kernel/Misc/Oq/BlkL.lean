module

public import Certificates.Data.Kernel.Misc.OqBlk

public section

namespace CertificateChecks.KernelMisc.Oq

open CFSG.KC.Misc.Oq CFSG.KC.LQT.P

private theorem allN_of_forall {m : ℕ} {f : ℕ → Bool} (h : ∀ i, i < m → f i = true) :
    allN m f = true := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change CFSG.KC.Ord.andB (f m) (allN m f) = true
    rw [h m (Nat.lt_succ_self m), ih fun i hi => h i (by omega)]
    all_goals rfl

theorem blkL_0 : okL 0 = true := by decide +kernel

theorem blkL_1 : okL 1 = true := by decide +kernel

theorem blkL_2 : okL 2 = true := by decide +kernel

theorem blkL_3 : okL 3 = true := by decide +kernel

theorem blkL_4 : okL 4 = true := by decide +kernel

theorem blkL_5 : okL 5 = true := by decide +kernel

theorem blkL_6 : okL 6 = true := by decide +kernel

theorem blkL_7 : okL 7 = true := by decide +kernel

theorem blkL_8 : okL 8 = true := by decide +kernel

theorem blkL : allN 9 okL = true :=
  allN_of_forall fun i hi => match i, hi with
    | 0, _ => blkL_0
    | 1, _ => blkL_1
    | 2, _ => blkL_2
    | 3, _ => blkL_3
    | 4, _ => blkL_4
    | 5, _ => blkL_5
    | 6, _ => blkL_6
    | 7, _ => blkL_7
    | 8, _ => blkL_8
    | _ + 9, h => absurd h (by omega)

end CertificateChecks.KernelMisc.Oq

end
