module

public import Certificates.Kernel.Sp6Insp443.SixGlue
public import CFSG.Certificates.Kernel.L52Insp443.Scan
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.Sp6Model

public section

namespace CertificateChecks.KernelS6I

open CFSG.KC.L52I CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.SectionRank.QTK.Insp443.Sp6
  CFSG.SectionRank.QTK.Insp443.PermKit.Native CFSG.Quasithin.KGC31.Native CFSG.Certificates.Native
  CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Native

theorem count5 :
    countProducts 36 (anyTest (tests5 (spanTabs 36 (cands5.getD 1 []))
      (spanTabs 36 (cands5.getD 3 [])) (spanTabs 36 (cands5.getD 4 [])))) (lv ()) (idT 36) = 0 := by
  rw [← levelTables_eq_lv]
  refine countProducts_eq_zero_of (by norm_num) co3Sp36Chain valid fun x T hT => ?_
  have hg : (x : Equiv.Perm (Fin 36)) ∈ co3X36 := x.2
  have h6 := cands5_sixTest hg hT
  unfold anyTest
  rw [← Bool.not_eq_true, List.any_eq_true]
  rintro ⟨f, hf, h1⟩
  simp only [tests5, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bool.false_ne_true ((cands5_centTest (k := 0) (by norm_num) hg hT).symm.trans h1)
  · exact Bool.false_ne_true ((cands5_centTest (k := 1) (by norm_num) hg hT).symm.trans h1)
  · exact Bool.false_ne_true ((cands5_centTest (k := 2) (by norm_num) hg hT).symm.trans h1)
  · exact Bool.false_ne_true ((cands5_centTest (k := 3) (by norm_num) hg hT).symm.trans h1)
  · exact Bool.false_ne_true ((cands5_centTest (k := 4) (by norm_num) hg hT).symm.trans h1)
  · exact Bool.false_ne_true ((cands5_centTest (k := 5) (by norm_num) hg hT).symm.trans h1)
  · exact Bool.false_ne_true (h6.1.symm.trans h1)
  · exact Bool.false_ne_true (h6.2.1.symm.trans h1)
  · exact Bool.false_ne_true (h6.2.2.symm.trans h1)

end CertificateChecks.KernelS6I

end
