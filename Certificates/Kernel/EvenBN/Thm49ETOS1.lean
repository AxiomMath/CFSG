module

public import Certificates.Kernel.EvenBN.Thm49ETOData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

namespace CertificateChecks.KernelT49

open CFSG.KC.Enum CFSG.KS CFSG.KD.T49

theorem allBlk_succ_true1 {b n : Nat} {f : Nat → Bool} (h1 : f (Nat.add b n) = true)
    (h2 : allBlk b f n = true) : allBlk b f (n + 1) = true := by
  change Bool.rec (motive := fun _ => Bool) false (allBlk b f n) (f (Nat.add b n)) = true
  rw [h1]
  exact h2

theorem allBlk_add_true1 {b n : Nat} {f : Nat → Bool} (h1 : allBlk b f n = true) :
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
      exact allBlk_add_true1 h1 m h

theorem allN92_true1 {f : Nat → Bool} (h1 : allBlk 64 f 28 = true) (h2 : allBlk 0 f 64 = true) :
    allN 92 f = true := by
  change Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false true (allBlk 0 f 64)) (allBlk 64 f 28) = true
  rw [h1, h2]

theorem search43i_23 : searchK w43 23 = true := by quickRfl

theorem search43i_24 : searchK w43 24 = true := by quickRfl

theorem search43i_25 : searchK w43 25 = true := by quickRfl

theorem search43i_26 : searchK w43 26 = true := by quickRfl

theorem search43i_27 : searchK w43 27 = true := by quickRfl

theorem search43i_28 : searchK w43 28 = true := by quickRfl

theorem search43i_29 : searchK w43 29 = true := by quickRfl

theorem search43i_30 : searchK w43 30 = true := by quickRfl

theorem pair43b_31_0 : allBlk 0 (fun i4 => pairK w43 31 i4) 8 = true := by quickRfl

theorem pair43b_31_1 : allBlk 8 (fun i4 => pairK w43 31 i4) 8 = true := by quickRfl

theorem pair43b_31_2 : allBlk 16 (fun i4 => pairK w43 31 i4) 8 = true := by quickRfl

theorem pair43b_31_3 : allBlk 24 (fun i4 => pairK w43 31 i4) 8 = true := by quickRfl

theorem pair43b_31_4 : allBlk 32 (fun i4 => pairK w43 31 i4) 8 = true := by quickRfl

theorem pair43b_31_5 : allBlk 40 (fun i4 => pairK w43 31 i4) 8 = true := by quickRfl

theorem pair43b_31_6 : allBlk 48 (fun i4 => pairK w43 31 i4) 8 = true := by quickRfl

theorem pair43b_31_7 : allBlk 56 (fun i4 => pairK w43 31 i4) 8 = true := by quickRfl

theorem pair43b_31_8 : allBlk 64 (fun i4 => pairK w43 31 i4) 8 = true := by quickRfl

theorem pair43b_31_9 : allBlk 72 (fun i4 => pairK w43 31 i4) 8 = true := by quickRfl

theorem pair43b_31_10 : allBlk 80 (fun i4 => pairK w43 31 i4) 8 = true := by quickRfl

theorem pair43b_31_11 : allBlk 88 (fun i4 => pairK w43 31 i4) 4 = true := by quickRfl

theorem search43i_31 : searchK w43 31 = true :=
  allN92_true1 (allBlk_add_true1 (allBlk_add_true1 (allBlk_add_true1 (pair43b_31_8) 8 pair43b_31_9) 8 pair43b_31_10) 4 pair43b_31_11)
    (allBlk_add_true1 (allBlk_add_true1 (allBlk_add_true1 (allBlk_add_true1 (allBlk_add_true1 (allBlk_add_true1 (allBlk_add_true1 (pair43b_31_0) 8 pair43b_31_1) 8 pair43b_31_2) 8 pair43b_31_3) 8 pair43b_31_4) 8 pair43b_31_5) 8 pair43b_31_6) 8 pair43b_31_7)

theorem search43i_32 : searchK w43 32 = true := by quickRfl

theorem search43i_33 : searchK w43 33 = true := by quickRfl

theorem search43i_34 : searchK w43 34 = true := by quickRfl

theorem pair43b_35_0 : allBlk 0 (fun i4 => pairK w43 35 i4) 8 = true := by quickRfl

theorem pair43b_35_1 : allBlk 8 (fun i4 => pairK w43 35 i4) 8 = true := by quickRfl

theorem pair43b_35_2 : allBlk 16 (fun i4 => pairK w43 35 i4) 8 = true := by quickRfl

theorem pair43b_35_3 : allBlk 24 (fun i4 => pairK w43 35 i4) 8 = true := by quickRfl

theorem pair43b_35_4 : allBlk 32 (fun i4 => pairK w43 35 i4) 8 = true := by quickRfl

theorem pair43b_35_5 : allBlk 40 (fun i4 => pairK w43 35 i4) 8 = true := by quickRfl

theorem pair43b_35_6 : allBlk 48 (fun i4 => pairK w43 35 i4) 8 = true := by quickRfl

theorem pair43b_35_7 : allBlk 56 (fun i4 => pairK w43 35 i4) 8 = true := by quickRfl

theorem pair43b_35_8 : allBlk 64 (fun i4 => pairK w43 35 i4) 8 = true := by quickRfl

theorem pair43b_35_9 : allBlk 72 (fun i4 => pairK w43 35 i4) 8 = true := by quickRfl

theorem pair43b_35_10 : allBlk 80 (fun i4 => pairK w43 35 i4) 8 = true := by quickRfl

theorem pair43b_35_11 : allBlk 88 (fun i4 => pairK w43 35 i4) 4 = true := by quickRfl

theorem search43i_35 : searchK w43 35 = true :=
  allN92_true1 (allBlk_add_true1 (allBlk_add_true1 (allBlk_add_true1 (pair43b_35_8) 8 pair43b_35_9) 8 pair43b_35_10) 4 pair43b_35_11)
    (allBlk_add_true1 (allBlk_add_true1 (allBlk_add_true1 (allBlk_add_true1 (allBlk_add_true1 (allBlk_add_true1 (allBlk_add_true1 (pair43b_35_0) 8 pair43b_35_1) 8 pair43b_35_2) 8 pair43b_35_3) 8 pair43b_35_4) 8 pair43b_35_5) 8 pair43b_35_6) 8 pair43b_35_7)

theorem search43i_36 : searchK w43 36 = true := by quickRfl

theorem search43i_37 : searchK w43 37 = true := by quickRfl

theorem search43i_38 : searchK w43 38 = true := by quickRfl

theorem search43i_39 : searchK w43 39 = true := by quickRfl

theorem search43i_40 : searchK w43 40 = true := by quickRfl

theorem search43i_41 : searchK w43 41 = true := by quickRfl

theorem search43i_42 : searchK w43 42 = true := by quickRfl

theorem search43i_43 : searchK w43 43 = true := by quickRfl

theorem search43i_44 : searchK w43 44 = true := by quickRfl

theorem search43i_45 : searchK w43 45 = true := by quickRfl

public section

theorem search43_1 : allBlk 23 (fun i3 => searchK w43 i3) 23 = true :=
  allBlk_succ_true1 search43i_45 (allBlk_succ_true1 search43i_44 (allBlk_succ_true1 search43i_43 (allBlk_succ_true1 search43i_42 (allBlk_succ_true1 search43i_41 (allBlk_succ_true1 search43i_40 (allBlk_succ_true1 search43i_39 (allBlk_succ_true1 search43i_38 (allBlk_succ_true1 search43i_37 (allBlk_succ_true1 search43i_36 (allBlk_succ_true1 search43i_35 (allBlk_succ_true1 search43i_34 (allBlk_succ_true1 search43i_33 (allBlk_succ_true1 search43i_32 (allBlk_succ_true1 search43i_31 (allBlk_succ_true1 search43i_30 (allBlk_succ_true1 search43i_29 (allBlk_succ_true1 search43i_28 (allBlk_succ_true1 search43i_27 (allBlk_succ_true1 search43i_26 (allBlk_succ_true1 search43i_25 (allBlk_succ_true1 search43i_24 (allBlk_succ_true1 search43i_23 (rfl)))))))))))))))))))))))

end

end CertificateChecks.KernelT49
