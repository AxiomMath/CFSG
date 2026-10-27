module

public import CFSG.Certificates.Kernel.Misc.Sp8U0Sound
public import Certificates.Kernel.Misc.Sp8U0.Tab
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.Sp8U0

open CFSG.KC.Sp8U0 CFSG.KC.Sp8Syl3 CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

theorem u06_gens : ∀ s < 5, EncS (u0Gens.getD s []) (REC s) := by decide +kernel

theorem u06_zuS : ∀ i < 4, EncS (zuS.getD i []) (REC (5 + i)) := by decide +kernel

theorem u06_zu_enc : List.Forall₂ EncS zuS [REC 5, REC 6, REC 7, REC 8] :=
  .cons (u06_zuS 0 (by norm_num)) (.cons (u06_zuS 1 (by norm_num)) (.cons (u06_zuS 2 (by norm_num))
    (.cons (u06_zuS 3 (by norm_num)) .nil)))

theorem u06_sp : u0Gens.all spS = true := by decide +kernel

theorem u06_fix : ((zuS.map fun z => (fixS z, aTypeS z)) ==
    [(256, true), (64, true), (128, false), (64, false)]) = true := by
  quickRfl

theorem u06_u0Chk : u0Chk899106 = true := u0Chk_of u06_gens u06_sp u06_tab_ok

theorem u06_zuChk : zuChk899106 = true :=
  zuChk_of u06_gens u06_zu_enc u06_tab_ok u06_zu_ok u06_fix

theorem u06_baseChk : baseChk899106 = true := by quickRfl

end CFSG.KD.Sp8U0

end
