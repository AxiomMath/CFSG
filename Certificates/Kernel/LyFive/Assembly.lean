module

public import Certificates.Kernel.LyFive.Classes
public import Certificates.Kernel.SporSch.Ly.FiveClass

public section

namespace CertificateChecks.KernelLyFive

open CFSG.KS.LyFive.G2 CFSG.KS.LyFive.Bfs CertificateChecks.KernelSporSch.LyFC
open CFSG.RankThree.PartOne.LyFive CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native


theorem classHp_eq : classHp = hGenPairs asArr := rfl

theorem classTree_eq (w : Mat) (τ : List ℤ) (N : ℕ) :
    classTree w τ N = CFSG.Sporadic.LySchreier.Native.conjBFS (classR w τ) (hGenPairs asArr) N := rfl

theorem lyXClass : lyXClassOK = true := by
  have hr := roots_ok.1.1
  unfold lyXClassOK classOK
  rw [classT_check tx, classTree_eq, classR_x, classHp_eq]
  simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, Bool.not_false, Bool.true_or,
    and_true]
  refine ⟨⟨conjBFS_treeOK hr, by norm_num⟩, conjBFS_size_ge hr cls_x⟩

theorem lyY3Class : lyY3ClassOK = true := by
  have hr := roots_ok.2.1.1
  unfold lyY3ClassOK classOK
  rw [classT_check ty3, classTree_eq, classR_y3, classHp_eq]
  obtain ⟨hcl, hsz⟩ := conjBFS_closed_eq hr cls_y3
  simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, Bool.not_true, Bool.false_or,
    beq_iff_eq]
  exact ⟨⟨⟨conjBFS_treeOK hr, by norm_num⟩, hsz.ge⟩, hcl, hsz⟩

theorem lyY1Class : lyY1ClassOK = true := by
  have hr := roots_ok.2.2.1
  unfold lyY1ClassOK classOK
  rw [classT_check ty1, classTree_eq, classR_y1, classHp_eq]
  simp only [Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, Bool.not_false, Bool.true_or,
    and_true]
  refine ⟨⟨conjBFS_treeOK hr, by norm_num⟩, conjBFS_size_ge hr cls_y1⟩

end CertificateChecks.KernelLyFive

end
