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

theorem blkU2_0 : okUs 2 0 = true := by decide +kernel

theorem blkU2_1 : okUs 2 1 = true := by decide +kernel

theorem blkU2_2 : okUs 2 2 = true := by decide +kernel

theorem blkU2_3 : okUs 2 3 = true := by decide +kernel

theorem blkU2_4 : okUs 2 4 = true := by decide +kernel

theorem blkU2_5 : okUs 2 5 = true := by decide +kernel

theorem blkU2_6 : okUs 2 6 = true := by decide +kernel

theorem blkU2_7 : okUs 2 7 = true := by decide +kernel

theorem blkU2_8 : okUs 2 8 = true := by decide +kernel

theorem blkU2_9 : okUs 2 9 = true := by decide +kernel

theorem blkU2 : allN 10 (okUs 2) = true :=
  allN_of_forall fun i hi => match i, hi with
    | 0, _ => blkU2_0
    | 1, _ => blkU2_1
    | 2, _ => blkU2_2
    | 3, _ => blkU2_3
    | 4, _ => blkU2_4
    | 5, _ => blkU2_5
    | 6, _ => blkU2_6
    | 7, _ => blkU2_7
    | 8, _ => blkU2_8
    | 9, _ => blkU2_9
    | _ + 10, h => absurd h (by omega)

end CertificateChecks.KernelMisc.Oq

end
