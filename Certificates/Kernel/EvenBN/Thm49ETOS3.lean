module

public import Certificates.Kernel.EvenBN.Thm49ETOData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

namespace CertificateChecks.KernelT49

open CFSG.KC.Enum CFSG.KS CFSG.KD.T49

theorem allBlk_succ_true3 {b n : Nat} {f : Nat → Bool} (h1 : f (Nat.add b n) = true)
    (h2 : allBlk b f n = true) : allBlk b f (n + 1) = true := by
  change Bool.rec (motive := fun _ => Bool) false (allBlk b f n) (f (Nat.add b n)) = true
  rw [h1]
  exact h2

theorem search43i_69 : searchK w43 69 = true := by quickRfl

theorem search43i_70 : searchK w43 70 = true := by quickRfl

theorem search43i_71 : searchK w43 71 = true := by quickRfl

theorem search43i_72 : searchK w43 72 = true := by quickRfl

theorem search43i_73 : searchK w43 73 = true := by quickRfl

theorem search43i_74 : searchK w43 74 = true := by quickRfl

theorem search43i_75 : searchK w43 75 = true := by quickRfl

theorem search43i_76 : searchK w43 76 = true := by quickRfl

theorem search43i_77 : searchK w43 77 = true := by quickRfl

theorem search43i_78 : searchK w43 78 = true := by quickRfl

theorem search43i_79 : searchK w43 79 = true := by quickRfl

theorem search43i_80 : searchK w43 80 = true := by quickRfl

theorem search43i_81 : searchK w43 81 = true := by quickRfl

theorem search43i_82 : searchK w43 82 = true := by quickRfl

theorem search43i_83 : searchK w43 83 = true := by quickRfl

theorem search43i_84 : searchK w43 84 = true := by quickRfl

theorem search43i_85 : searchK w43 85 = true := by quickRfl

theorem search43i_86 : searchK w43 86 = true := by quickRfl

theorem search43i_87 : searchK w43 87 = true := by quickRfl

theorem search43i_88 : searchK w43 88 = true := by quickRfl

theorem search43i_89 : searchK w43 89 = true := by quickRfl

theorem search43i_90 : searchK w43 90 = true := by quickRfl

theorem search43i_91 : searchK w43 91 = true := by quickRfl

public section

theorem search43_3 : allBlk 69 (fun i3 => searchK w43 i3) 23 = true :=
  allBlk_succ_true3 search43i_91 (allBlk_succ_true3 search43i_90 (allBlk_succ_true3 search43i_89 (allBlk_succ_true3 search43i_88 (allBlk_succ_true3 search43i_87 (allBlk_succ_true3 search43i_86 (allBlk_succ_true3 search43i_85 (allBlk_succ_true3 search43i_84 (allBlk_succ_true3 search43i_83 (allBlk_succ_true3 search43i_82 (allBlk_succ_true3 search43i_81 (allBlk_succ_true3 search43i_80 (allBlk_succ_true3 search43i_79 (allBlk_succ_true3 search43i_78 (allBlk_succ_true3 search43i_77 (allBlk_succ_true3 search43i_76 (allBlk_succ_true3 search43i_75 (allBlk_succ_true3 search43i_74 (allBlk_succ_true3 search43i_73 (allBlk_succ_true3 search43i_72 (allBlk_succ_true3 search43i_71 (allBlk_succ_true3 search43i_70 (allBlk_succ_true3 search43i_69 (rfl)))))))))))))))))))))))

end

end CertificateChecks.KernelT49
