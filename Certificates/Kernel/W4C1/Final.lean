module

public import CFSG.Certificates.Kernel.W4C1.Sound
public import CFSG.Certificates.Kernel.Sp6Two.Sound
public import Certificates.Kernel.Sp6Two.ChecksC
public import Certificates.Kernel.W4C1.Checks

public section

namespace CFSG.KD.W4C1

open CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.KC.Sp6Two CFSG.KD.Sp6Two CFSG.KC.W4C1
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.GF2Type.Smith1979.W4C1

theorem gens330375 : ∀ s < 5, canon6 (syG.getD s []) = true ∧ pk (syG.getD s []) = at2 REC 16 s := by
  decide +kernel

set_option maxRecDepth 20000 in
theorem pairs330375 : syP.all pairT = true := by
  decide +kernel

theorem w2330375 : canon6 w2C = true ∧ pk w2C = recX REC 34728 158 := by
  decide +kernel

theorem syl330375 : closureOK syG syT 512 = true ∧
    ∀ t < 512, canon6 (syT.getD t []) = true ∧ pk (syT.getD t []) = recX REC 34728 t :=
  closureKG_ok rfl (by decide) (by decide) (by decide) gens330375 tabS_ok (by decide) (by decide)
    (by decide)

theorem size330375 : syT.size = 512 := by
  have h := syl330375.1
  simp only [closureOK, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.1

theorem chk330375_ok : chk = true := by
  unfold chk
  rw [all_pairs pairs330375, syl330375.1,
    contains_of size330375 syl330375.2 (by decide) w2330375,
    chainOK_of gens330375 size330375 syl330375.2 w2330375 (by decide) chain330375_ok]
  decide +kernel

end CFSG.KD.W4C1

end
