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

theorem blkU0_0 : okUs 0 0 = true := by decide +kernel

theorem blkU0_1 : okUs 0 1 = true := by decide +kernel

theorem blkU0_2 : okUs 0 2 = true := by decide +kernel

theorem blkU0_3 : okUs 0 3 = true := by decide +kernel

theorem blkU0_4 : okUs 0 4 = true := by decide +kernel

theorem blkU0_5 : okUs 0 5 = true := by decide +kernel

theorem blkU0_6 : okUs 0 6 = true := by decide +kernel

theorem blkU0_7 : okUs 0 7 = true := by decide +kernel

theorem blkU0_8 : okUs 0 8 = true := by decide +kernel

theorem blkU0_9 : okUs 0 9 = true := by decide +kernel

theorem blkU0 : allN 10 (okUs 0) = true :=
  allN_of_forall fun i hi => match i, hi with
    | 0, _ => blkU0_0
    | 1, _ => blkU0_1
    | 2, _ => blkU0_2
    | 3, _ => blkU0_3
    | 4, _ => blkU0_4
    | 5, _ => blkU0_5
    | 6, _ => blkU0_6
    | 7, _ => blkU0_7
    | 8, _ => blkU0_8
    | 9, _ => blkU0_9
    | _ + 10, h => absurd h (by omega)

end CertificateChecks.KernelMisc.Oq

end
