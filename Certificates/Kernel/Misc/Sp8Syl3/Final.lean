module

public import CFSG.Certificates.Kernel.Misc.Sp8Syl3Sound
public import Certificates.Kernel.Misc.Sp8Syl3.Checks

public section

namespace CFSG.KD.Sp8Syl3

open CFSG.KC.Sp8Syl3 CFSG.RankThree.PartTwo.Sec21.FF81.Sp8

theorem sy3_gens : ∀ s < 5, EncS (pGens.getD s []) (REC s) := by decide +kernel

theorem sy3_conjs : ∀ c < 3, EncS (conjL.getD c []) (REC (Nat.add 5 c)) ∧
    EncS (invS (conjL.getD c [])) (REC (Nat.add 8 c)) := by decide +kernel

theorem cert899103_ok : pairsChk899103 = true ∧ e0Chk899103 = true ∧ pChk899103 = true ∧
    cpChk899103 = true ∧ conjChk899103 = true :=
  ⟨by decide +kernel, e0Chk_of sy3_gens (by decide +kernel) sy3_tabE_ok sy3_e0_ok,
    pChk_of sy3_gens (by decide +kernel) sy3_tabP_ok,
    cpChk_of sy3_gens sy3_tabE_ok sy3_tabP_ok sy3_cp_ok,
    conjChk_of sy3_gens sy3_conjs sy3_tabE_ok sy3_tabP_ok sy3_conj_ok⟩

end CFSG.KD.Sp8Syl3

end
