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

theorem blkU1_0 : okUs 1 0 = true := by decide +kernel

theorem blkU1_1 : okUs 1 1 = true := by decide +kernel

theorem blkU1_2 : okUs 1 2 = true := by decide +kernel

theorem blkU1_3 : okUs 1 3 = true := by decide +kernel

theorem blkU1_4 : okUs 1 4 = true := by decide +kernel

theorem blkU1_5 : okUs 1 5 = true := by decide +kernel

theorem blkU1_6 : okUs 1 6 = true := by decide +kernel

theorem blkU1_7 : okUs 1 7 = true := by decide +kernel

theorem blkU1_8 : okUs 1 8 = true := by decide +kernel

theorem blkU1_9 : okUs 1 9 = true := by decide +kernel

theorem blkU1 : allN 10 (okUs 1) = true :=
  allN_of_forall fun i hi => match i, hi with
    | 0, _ => blkU1_0
    | 1, _ => blkU1_1
    | 2, _ => blkU1_2
    | 3, _ => blkU1_3
    | 4, _ => blkU1_4
    | 5, _ => blkU1_5
    | 6, _ => blkU1_6
    | 7, _ => blkU1_7
    | 8, _ => blkU1_8
    | 9, _ => blkU1_9
    | _ + 10, h => absurd h (by omega)

end CertificateChecks.KernelMisc.Oq

end
