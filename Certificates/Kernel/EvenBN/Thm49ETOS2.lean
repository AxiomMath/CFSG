module

public import Certificates.Kernel.EvenBN.Thm49ETOData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

namespace CertificateChecks.KernelT49

open CFSG.KC.Enum CFSG.KS CFSG.KD.T49

theorem allBlk_succ_true2 {b n : Nat} {f : Nat → Bool} (h1 : f (Nat.add b n) = true)
    (h2 : allBlk b f n = true) : allBlk b f (n + 1) = true := by
  change Bool.rec (motive := fun _ => Bool) false (allBlk b f n) (f (Nat.add b n)) = true
  rw [h1]
  exact h2

theorem allBlk_add_true2 {b n : Nat} {f : Nat → Bool} (h1 : allBlk b f n = true) :
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
      exact allBlk_add_true2 h1 m h

theorem allN92_true2 {f : Nat → Bool} (h1 : allBlk 64 f 28 = true) (h2 : allBlk 0 f 64 = true) :
    allN 92 f = true := by
  change Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false true (allBlk 0 f 64)) (allBlk 64 f 28) = true
  rw [h1, h2]

theorem pair43b_46_0 : allBlk 0 (fun i4 => pairK w43 46 i4) 8 = true := by quickRfl

theorem pair43b_46_1 : allBlk 8 (fun i4 => pairK w43 46 i4) 8 = true := by quickRfl

theorem pair43b_46_2 : allBlk 16 (fun i4 => pairK w43 46 i4) 8 = true := by quickRfl

theorem pair43b_46_3 : allBlk 24 (fun i4 => pairK w43 46 i4) 8 = true := by quickRfl

theorem pair43b_46_4 : allBlk 32 (fun i4 => pairK w43 46 i4) 8 = true := by quickRfl

theorem pair43b_46_5 : allBlk 40 (fun i4 => pairK w43 46 i4) 8 = true := by quickRfl

theorem pair43b_46_6 : allBlk 48 (fun i4 => pairK w43 46 i4) 8 = true := by quickRfl

theorem pair43b_46_7 : allBlk 56 (fun i4 => pairK w43 46 i4) 8 = true := by quickRfl

theorem pair43b_46_8 : allBlk 64 (fun i4 => pairK w43 46 i4) 8 = true := by quickRfl

theorem pair43b_46_9 : allBlk 72 (fun i4 => pairK w43 46 i4) 8 = true := by quickRfl

theorem pair43b_46_10 : allBlk 80 (fun i4 => pairK w43 46 i4) 8 = true := by quickRfl

theorem pair43b_46_11 : allBlk 88 (fun i4 => pairK w43 46 i4) 4 = true := by quickRfl

theorem search43i_46 : searchK w43 46 = true :=
  allN92_true2 (allBlk_add_true2 (allBlk_add_true2 (allBlk_add_true2 (pair43b_46_8) 8 pair43b_46_9) 8 pair43b_46_10) 4 pair43b_46_11)
    (allBlk_add_true2 (allBlk_add_true2 (allBlk_add_true2 (allBlk_add_true2 (allBlk_add_true2 (allBlk_add_true2 (allBlk_add_true2 (pair43b_46_0) 8 pair43b_46_1) 8 pair43b_46_2) 8 pair43b_46_3) 8 pair43b_46_4) 8 pair43b_46_5) 8 pair43b_46_6) 8 pair43b_46_7)

theorem search43i_47 : searchK w43 47 = true := by quickRfl

theorem search43i_48 : searchK w43 48 = true := by quickRfl

theorem search43i_49 : searchK w43 49 = true := by quickRfl

theorem search43i_50 : searchK w43 50 = true := by quickRfl

theorem search43i_51 : searchK w43 51 = true := by quickRfl

theorem pair43b_52_0 : allBlk 0 (fun i4 => pairK w43 52 i4) 8 = true := by quickRfl

theorem pair43b_52_1 : allBlk 8 (fun i4 => pairK w43 52 i4) 8 = true := by quickRfl

theorem pair43b_52_2 : allBlk 16 (fun i4 => pairK w43 52 i4) 8 = true := by quickRfl

theorem pair43b_52_3 : allBlk 24 (fun i4 => pairK w43 52 i4) 8 = true := by quickRfl

theorem pair43b_52_4 : allBlk 32 (fun i4 => pairK w43 52 i4) 8 = true := by quickRfl

theorem pair43b_52_5 : allBlk 40 (fun i4 => pairK w43 52 i4) 8 = true := by quickRfl

theorem pair43b_52_6 : allBlk 48 (fun i4 => pairK w43 52 i4) 8 = true := by quickRfl

theorem pair43b_52_7 : allBlk 56 (fun i4 => pairK w43 52 i4) 8 = true := by quickRfl

theorem pair43b_52_8 : allBlk 64 (fun i4 => pairK w43 52 i4) 8 = true := by quickRfl

theorem pair43b_52_9 : allBlk 72 (fun i4 => pairK w43 52 i4) 8 = true := by quickRfl

theorem pair43b_52_10 : allBlk 80 (fun i4 => pairK w43 52 i4) 8 = true := by quickRfl

theorem pair43b_52_11 : allBlk 88 (fun i4 => pairK w43 52 i4) 4 = true := by quickRfl

theorem search43i_52 : searchK w43 52 = true :=
  allN92_true2 (allBlk_add_true2 (allBlk_add_true2 (allBlk_add_true2 (pair43b_52_8) 8 pair43b_52_9) 8 pair43b_52_10) 4 pair43b_52_11)
    (allBlk_add_true2 (allBlk_add_true2 (allBlk_add_true2 (allBlk_add_true2 (allBlk_add_true2 (allBlk_add_true2 (allBlk_add_true2 (pair43b_52_0) 8 pair43b_52_1) 8 pair43b_52_2) 8 pair43b_52_3) 8 pair43b_52_4) 8 pair43b_52_5) 8 pair43b_52_6) 8 pair43b_52_7)

theorem search43i_53 : searchK w43 53 = true := by quickRfl

theorem search43i_54 : searchK w43 54 = true := by quickRfl

theorem search43i_55 : searchK w43 55 = true := by quickRfl

theorem search43i_56 : searchK w43 56 = true := by quickRfl

theorem search43i_57 : searchK w43 57 = true := by quickRfl

theorem search43i_58 : searchK w43 58 = true := by quickRfl

theorem search43i_59 : searchK w43 59 = true := by quickRfl

theorem search43i_60 : searchK w43 60 = true := by quickRfl

theorem search43i_61 : searchK w43 61 = true := by quickRfl

theorem search43i_62 : searchK w43 62 = true := by quickRfl

theorem search43i_63 : searchK w43 63 = true := by quickRfl

theorem search43i_64 : searchK w43 64 = true := by quickRfl

theorem search43i_65 : searchK w43 65 = true := by quickRfl

theorem search43i_66 : searchK w43 66 = true := by quickRfl

theorem search43i_67 : searchK w43 67 = true := by quickRfl

theorem search43i_68 : searchK w43 68 = true := by quickRfl

public section

theorem search43_2 : allBlk 46 (fun i3 => searchK w43 i3) 23 = true :=
  allBlk_succ_true2 search43i_68 (allBlk_succ_true2 search43i_67 (allBlk_succ_true2 search43i_66 (allBlk_succ_true2 search43i_65 (allBlk_succ_true2 search43i_64 (allBlk_succ_true2 search43i_63 (allBlk_succ_true2 search43i_62 (allBlk_succ_true2 search43i_61 (allBlk_succ_true2 search43i_60 (allBlk_succ_true2 search43i_59 (allBlk_succ_true2 search43i_58 (allBlk_succ_true2 search43i_57 (allBlk_succ_true2 search43i_56 (allBlk_succ_true2 search43i_55 (allBlk_succ_true2 search43i_54 (allBlk_succ_true2 search43i_53 (allBlk_succ_true2 search43i_52 (allBlk_succ_true2 search43i_51 (allBlk_succ_true2 search43i_50 (allBlk_succ_true2 search43i_49 (allBlk_succ_true2 search43i_48 (allBlk_succ_true2 search43i_47 (allBlk_succ_true2 search43i_46 (rfl)))))))))))))))))))))))

end

end CertificateChecks.KernelT49
