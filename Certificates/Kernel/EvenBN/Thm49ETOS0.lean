module

public import Certificates.Kernel.EvenBN.Thm49ETOData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

namespace CertificateChecks.KernelT49

open CFSG.KC.Enum CFSG.KS CFSG.KD.T49

theorem allBlk_succ_true0 {b n : Nat} {f : Nat → Bool} (h1 : f (Nat.add b n) = true)
    (h2 : allBlk b f n = true) : allBlk b f (n + 1) = true := by
  change Bool.rec (motive := fun _ => Bool) false (allBlk b f n) (f (Nat.add b n)) = true
  rw [h1]
  exact h2

theorem allBlk_add_true0 {b n : Nat} {f : Nat → Bool} (h1 : allBlk b f n = true) :
    ∀ m, allBlk (Nat.add b n) f m = true → allBlk b f (n + m) = true
  | 0, _ => h1
  | m + 1, h => by
    change Bool.rec (motive := fun _ => Bool) false (allBlk (Nat.add b n) f m)
      (f (Nat.add (Nat.add b n) m)) = true at h
    change Bool.rec (motive := fun _ => Bool) false (allBlk b f (n + m)) (f (Nat.add b (n + m))) = true
    rw [show Nat.add b (n + m) = Nat.add (Nat.add b n) m from (Nat.add_assoc b n m).symm]
    cases hf : f (Nat.add (Nat.add b n) m)
    · rw [hf] at h
      exact absurd h Bool.false_ne_true
    · rw [hf] at h
      exact allBlk_add_true0 h1 m h

theorem allN92_true0 {f : Nat → Bool} (h1 : allBlk 64 f 28 = true) (h2 : allBlk 0 f 64 = true) :
    allN 92 f = true := by
  change Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false true (allBlk 0 f 64)) (allBlk 64 f 28) = true
  rw [h1, h2]

theorem search43i_0 : searchK w43 0 = true := by quickRfl

theorem search43i_1 : searchK w43 1 = true := by quickRfl

theorem search43i_2 : searchK w43 2 = true := by quickRfl

theorem search43i_3 : searchK w43 3 = true := by quickRfl

theorem search43i_4 : searchK w43 4 = true := by quickRfl

theorem search43i_5 : searchK w43 5 = true := by quickRfl

theorem search43i_6 : searchK w43 6 = true := by quickRfl

theorem search43i_7 : searchK w43 7 = true := by quickRfl

theorem search43i_8 : searchK w43 8 = true := by quickRfl

theorem search43i_9 : searchK w43 9 = true := by quickRfl

theorem search43i_10 : searchK w43 10 = true := by quickRfl

theorem search43i_11 : searchK w43 11 = true := by quickRfl

theorem pair43b_12_0 : allBlk 0 (fun i4 => pairK w43 12 i4) 8 = true := by quickRfl

theorem pair43b_12_1 : allBlk 8 (fun i4 => pairK w43 12 i4) 8 = true := by quickRfl

theorem pair43b_12_2 : allBlk 16 (fun i4 => pairK w43 12 i4) 8 = true := by quickRfl

theorem pair43b_12_3 : allBlk 24 (fun i4 => pairK w43 12 i4) 8 = true := by quickRfl

theorem pair43b_12_4 : allBlk 32 (fun i4 => pairK w43 12 i4) 8 = true := by quickRfl

theorem pair43b_12_5 : allBlk 40 (fun i4 => pairK w43 12 i4) 8 = true := by quickRfl

theorem pair43b_12_6 : allBlk 48 (fun i4 => pairK w43 12 i4) 8 = true := by quickRfl

theorem pair43b_12_7 : allBlk 56 (fun i4 => pairK w43 12 i4) 8 = true := by quickRfl

theorem pair43b_12_8 : allBlk 64 (fun i4 => pairK w43 12 i4) 8 = true := by quickRfl

theorem pair43b_12_9 : allBlk 72 (fun i4 => pairK w43 12 i4) 8 = true := by quickRfl

theorem pair43b_12_10 : allBlk 80 (fun i4 => pairK w43 12 i4) 8 = true := by quickRfl

theorem pair43b_12_11 : allBlk 88 (fun i4 => pairK w43 12 i4) 4 = true := by quickRfl

theorem search43i_12 : searchK w43 12 = true :=
  allN92_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (pair43b_12_8) 8 pair43b_12_9) 8 pair43b_12_10) 4 pair43b_12_11)
    (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (pair43b_12_0) 8 pair43b_12_1) 8 pair43b_12_2) 8 pair43b_12_3) 8 pair43b_12_4) 8 pair43b_12_5) 8 pair43b_12_6) 8 pair43b_12_7)

theorem search43i_13 : searchK w43 13 = true := by quickRfl

theorem search43i_14 : searchK w43 14 = true := by quickRfl

theorem search43i_15 : searchK w43 15 = true := by quickRfl

theorem pair43b_16_0 : allBlk 0 (fun i4 => pairK w43 16 i4) 8 = true := by quickRfl

theorem pair43b_16_1 : allBlk 8 (fun i4 => pairK w43 16 i4) 8 = true := by quickRfl

theorem pair43b_16_2 : allBlk 16 (fun i4 => pairK w43 16 i4) 8 = true := by quickRfl

theorem pair43b_16_3 : allBlk 24 (fun i4 => pairK w43 16 i4) 8 = true := by quickRfl

theorem pair43b_16_4 : allBlk 32 (fun i4 => pairK w43 16 i4) 8 = true := by quickRfl

theorem pair43b_16_5 : allBlk 40 (fun i4 => pairK w43 16 i4) 8 = true := by quickRfl

theorem pair43b_16_6 : allBlk 48 (fun i4 => pairK w43 16 i4) 8 = true := by quickRfl

theorem pair43b_16_7 : allBlk 56 (fun i4 => pairK w43 16 i4) 8 = true := by quickRfl

theorem pair43b_16_8 : allBlk 64 (fun i4 => pairK w43 16 i4) 8 = true := by quickRfl

theorem pair43b_16_9 : allBlk 72 (fun i4 => pairK w43 16 i4) 8 = true := by quickRfl

theorem pair43b_16_10 : allBlk 80 (fun i4 => pairK w43 16 i4) 8 = true := by quickRfl

theorem pair43b_16_11 : allBlk 88 (fun i4 => pairK w43 16 i4) 4 = true := by quickRfl

theorem search43i_16 : searchK w43 16 = true :=
  allN92_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (pair43b_16_8) 8 pair43b_16_9) 8 pair43b_16_10) 4 pair43b_16_11)
    (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (pair43b_16_0) 8 pair43b_16_1) 8 pair43b_16_2) 8 pair43b_16_3) 8 pair43b_16_4) 8 pair43b_16_5) 8 pair43b_16_6) 8 pair43b_16_7)

theorem search43i_17 : searchK w43 17 = true := by quickRfl

theorem search43i_18 : searchK w43 18 = true := by quickRfl

theorem search43i_19 : searchK w43 19 = true := by quickRfl

theorem pair43b_20_0 : allBlk 0 (fun i4 => pairK w43 20 i4) 8 = true := by quickRfl

theorem pair43b_20_1 : allBlk 8 (fun i4 => pairK w43 20 i4) 8 = true := by quickRfl

theorem pair43b_20_2 : allBlk 16 (fun i4 => pairK w43 20 i4) 8 = true := by quickRfl

theorem pair43b_20_3 : allBlk 24 (fun i4 => pairK w43 20 i4) 8 = true := by quickRfl

theorem pair43b_20_4 : allBlk 32 (fun i4 => pairK w43 20 i4) 8 = true := by quickRfl

theorem pair43b_20_5 : allBlk 40 (fun i4 => pairK w43 20 i4) 8 = true := by quickRfl

theorem pair43b_20_6 : allBlk 48 (fun i4 => pairK w43 20 i4) 8 = true := by quickRfl

theorem pair43b_20_7 : allBlk 56 (fun i4 => pairK w43 20 i4) 8 = true := by quickRfl

theorem pair43b_20_8 : allBlk 64 (fun i4 => pairK w43 20 i4) 8 = true := by quickRfl

theorem pair43b_20_9 : allBlk 72 (fun i4 => pairK w43 20 i4) 8 = true := by quickRfl

theorem pair43b_20_10 : allBlk 80 (fun i4 => pairK w43 20 i4) 8 = true := by quickRfl

theorem pair43b_20_11 : allBlk 88 (fun i4 => pairK w43 20 i4) 4 = true := by quickRfl

theorem search43i_20 : searchK w43 20 = true :=
  allN92_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (pair43b_20_8) 8 pair43b_20_9) 8 pair43b_20_10) 4 pair43b_20_11)
    (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (pair43b_20_0) 8 pair43b_20_1) 8 pair43b_20_2) 8 pair43b_20_3) 8 pair43b_20_4) 8 pair43b_20_5) 8 pair43b_20_6) 8 pair43b_20_7)

theorem search43i_21 : searchK w43 21 = true := by quickRfl

theorem pair43b_22_0 : allBlk 0 (fun i4 => pairK w43 22 i4) 8 = true := by quickRfl

theorem pair43b_22_1 : allBlk 8 (fun i4 => pairK w43 22 i4) 8 = true := by quickRfl

theorem pair43b_22_2 : allBlk 16 (fun i4 => pairK w43 22 i4) 8 = true := by quickRfl

theorem pair43b_22_3 : allBlk 24 (fun i4 => pairK w43 22 i4) 8 = true := by quickRfl

theorem pair43b_22_4 : allBlk 32 (fun i4 => pairK w43 22 i4) 8 = true := by quickRfl

theorem pair43b_22_5 : allBlk 40 (fun i4 => pairK w43 22 i4) 8 = true := by quickRfl

theorem pair43b_22_6 : allBlk 48 (fun i4 => pairK w43 22 i4) 8 = true := by quickRfl

theorem pair43b_22_7 : allBlk 56 (fun i4 => pairK w43 22 i4) 8 = true := by quickRfl

theorem pair43b_22_8 : allBlk 64 (fun i4 => pairK w43 22 i4) 8 = true := by quickRfl

theorem pair43b_22_9 : allBlk 72 (fun i4 => pairK w43 22 i4) 8 = true := by quickRfl

theorem pair43b_22_10 : allBlk 80 (fun i4 => pairK w43 22 i4) 8 = true := by quickRfl

theorem pair43b_22_11 : allBlk 88 (fun i4 => pairK w43 22 i4) 4 = true := by quickRfl

theorem search43i_22 : searchK w43 22 = true :=
  allN92_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (pair43b_22_8) 8 pair43b_22_9) 8 pair43b_22_10) 4 pair43b_22_11)
    (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (allBlk_add_true0 (pair43b_22_0) 8 pair43b_22_1) 8 pair43b_22_2) 8 pair43b_22_3) 8 pair43b_22_4) 8 pair43b_22_5) 8 pair43b_22_6) 8 pair43b_22_7)

public section

theorem search43_0 : allBlk 0 (fun i3 => searchK w43 i3) 23 = true :=
  allBlk_succ_true0 search43i_22 (allBlk_succ_true0 search43i_21 (allBlk_succ_true0 search43i_20 (allBlk_succ_true0 search43i_19 (allBlk_succ_true0 search43i_18 (allBlk_succ_true0 search43i_17 (allBlk_succ_true0 search43i_16 (allBlk_succ_true0 search43i_15 (allBlk_succ_true0 search43i_14 (allBlk_succ_true0 search43i_13 (allBlk_succ_true0 search43i_12 (allBlk_succ_true0 search43i_11 (allBlk_succ_true0 search43i_10 (allBlk_succ_true0 search43i_9 (allBlk_succ_true0 search43i_8 (allBlk_succ_true0 search43i_7 (allBlk_succ_true0 search43i_6 (allBlk_succ_true0 search43i_5 (allBlk_succ_true0 search43i_4 (allBlk_succ_true0 search43i_3 (allBlk_succ_true0 search43i_2 (allBlk_succ_true0 search43i_1 (allBlk_succ_true0 search43i_0 (rfl)))))))))))))))))))))))

end

end CertificateChecks.KernelT49
