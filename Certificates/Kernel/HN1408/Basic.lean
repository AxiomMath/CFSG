module

public import Certificates.Kernel.HN1408.Glue
public import Certificates.Kernel.HN1408.BasicChecks
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.BasicCheck

public section

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem gens_all :
    h1408Gens.all (fun g => permOK 1408 g && invOK 1408 g (invT 1408 g)) = true := by
  rw [List.all_eq_true]
  intro g hg
  obtain ⟨j, hj, rfl⟩ := mem_gens hg
  exact gen_ok hj

theorem twoHSBasicOK_of : twoHSBasicOK = true := by
  have eA := tabW_eq (wd := wordA) (by decide)
  have eZ := tabW_eq (wd := wordZ) (by decide)
  have eB := tabW_eq (wd := wordB) (by decide)
  have eZ1 := tabW_eq (wd := wordZ₁) (by decide)
  have eAZ := tabW_eq (wd := wordAZ) (by decide)
  have hi := invol4
  simp only [bAnd_iff] at hi
  have hs := swaps
  simp only [bAnd_iff, Nat.ble_eq] at hs
  have hc : h1408Gens.all (fun g => commTT 1408 (tabW wordA) g) = true := by
    rw [List.all_eq_true]
    intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gens hg
    rw [eA.1, commTT_eq eA.2 (h8 hj).1]
    exact allN_spec centA j hj
  unfold twoHSBasicOK
  rw [gens_all, hc, eA.1, eZ.1, eB.1, eZ1.1, eAZ.1, involOK_eq eA.2, involOK_eq eZ.2,
    involOK_eq eB.2, involOK_eq eZ1.2, halves_eq eA.2 halvesA, halves_eq eZ.2 halvesZ,
    halves_eq eAZ.2 halvesAZ, swapsZero_eq eB.2, swapsZero_eq eZ1.2, hi.1, hi.2.1, hi.2.2.1,
    hi.2.2.2]
  simp [hs.1, hs.2]

theorem gensInvoOK_of : CFSG.EvenSporadicStandard.HNRecog.HaradaModel.gensInvoOK = true := by
  unfold CFSG.EvenSporadicStandard.HNRecog.HaradaModel.gensInvoOK
  rw [List.all_eq_true]
  intro j hj
  have hj' : j < 7 := List.mem_range.1 hj
  have e := tabW_eq (wd := [j + 1]) (by simp [lettersOK]; omega)
  rw [e.1, invoOK_eq e.2]
  exact allN_spec gensInvo j hj'

end CFSG.KD.HN1408

end
