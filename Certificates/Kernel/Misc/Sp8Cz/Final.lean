module

public import CFSG.Certificates.Kernel.Misc.Sp8CzSound
public import Certificates.Kernel.Misc.Sp8Cz.Checks
public import Certificates.Certificate899103

public section

namespace CFSG.KD.Sp8Cz

open CFSG.KC.Sp8Cz CFSG.KC.Sp8Syl3 CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

theorem cz5_gens : ∀ s < 7, EncS (czGens.getD s []) (REC s) := by decide +kernel

theorem cz5_z3 : EncS z3S (REC 7) := by decide +kernel

theorem cz5_l1 : List.Forall₂ EncS l1S (l1N REC) := by
  have g0 : EncS z0S (REC 0) := cz5_gens 0 (by norm_num)
  have g1 : EncS z1S (REC 1) := cz5_gens 1 (by norm_num)
  have g2 : EncS z2S (REC 3) := cz5_gens 3 (by norm_num)
  exact .cons g0 (.cons (mulE g0 g0) (.cons g1 (.cons (mulE g1 g1) (.cons g2 (.cons (mulE g2 g2)
    (.cons cz5_z3 (.cons (mulE cz5_z3 cz5_z3) .nil)))))))

theorem cert899105_ok : czChk899105 = true ∧ colChk899105 = true ∧ e0cChk899105 = true ∧
    hypChk899105 = true ∧ f1Chk899105 = true ∧ e9Chk899105 = true := by
  have htab := tab_e0_of Certificates.certificate899103.2.1
  have g0 : EncS z0S (REC 0) := cz5_gens 0 (by norm_num)
  have g1 : EncS z1S (REC 1) := cz5_gens 1 (by norm_num)
  have g2 : EncS z2S (REC 3) := cz5_gens 3 (by norm_num)
  have g3 : EncS z3S (REC 7) := cz5_z3
  refine ⟨czChk_of cz5_gens (by decide +kernel) (by decide +kernel) cz5_tab_ok,
    colChk_of cz5_cntW cz5_cntW', e0cChk_of htab, hypChk_of htab, by decide +kernel, ?_⟩
  unfold e9Chk899105
  have h01 := e9_of (i := 0) (j := 1) g0 g1 cz5_l1 (w2_enc g0 (mulE g0 g0) g1 (mulE g1 g1))
    (by decide +kernel) cz5_e9tab_ok.1 cz5_e9mem_ok.1
  have h23 := e9_of (i := 2) (j := 3) g2 g3 cz5_l1 (w2_enc g2 (mulE g2 g2) g3 (mulE g3 g3))
    (by decide +kernel) cz5_e9tab_ok.2.1 cz5_e9mem_ok.2.1
  have h03 := e9_of (i := 0) (j := 3) g0 g3 cz5_l1 (w2_enc g0 (mulE g0 g0) g3 (mulE g3 g3))
    (by decide +kernel) cz5_e9tab_ok.2.2 cz5_e9mem_ok.2.2
  rw [Bool.and_eq_true] at h01 h23 h03
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨h01, h23, h03⟩

end CFSG.KD.Sp8Cz

end
