module

public import Certificates.Kernel.Eight89K.Model
public import Certificates.Kernel.Eight89K.Cover3
public import Certificates.Kernel.Eight89K.Cover6
public import CFSG.Certificates.Kernel.Eight89KModelSound
public import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KCoverPG

public section

namespace CFSG.KC.Eight89K

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8 KInputs CFSG.KC.MiscCoset Subgroup

theorem cover3_facts : ∀ k l, k < 2 → l < 3 → Finite (CoverPG 3 0 0 k l) ∧
    Nat.card (CoverPG 3 0 0 k l) ≤ if l = 0 then 1080 else 360 := by
  intro k l hk hl
  interval_cases k <;> interval_cases l
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c3k0l0
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c3k0l1
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c3k0l2
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c3k1l0
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c3k1l1
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c3k1l2

theorem cover6_facts : ∀ i j k l, i < 2 → j < 2 → k < 2 → l < 3 →
    Finite (CoverPG 6 i j k l) ∧
      Nat.card (CoverPG 6 i j k l) ≤ (if i = j then 2160 else 1080) / (if l = 0 then 1 else 3) := by
  intro i j k l hi hj hk hl
  interval_cases i <;> interval_cases j <;> interval_cases k <;> interval_cases l
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i0j0k0l0
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i0j0k0l1
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i0j0k0l2
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i0j0k1l0
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i0j0k1l1
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i0j0k1l2
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i0j1k0l0
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i0j1k0l1
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i0j1k0l2
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i0j1k1l0
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i0j1k1l1
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i0j1k1l2
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i1j0k0l0
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i1j0k0l1
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i1j0k0l2
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i1j0k1l0
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i1j0k1l1
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i1j0k1l2
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i1j1k0l0
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i1j1k0l1
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i1j1k0l2
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i1j1k1l0
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i1j1k1l1
  · exact TableFact.card _ (by decide) CFSG.KBFact.F1491c6i1j1k1l2

theorem model3_facts :
    orderOf s3 = 15 ∧ a3 ^ 2 = 1 ∧ b3 ^ 4 = 1 ∧ (a3 * b3 * b3) ^ 5 = 1 ∧ c3 ∈ center model3 :=
  model3_facts_of_rel model3_rel

theorem model6_facts :
    orderOf s6 = 30 ∧ a6 ^ 2 = c6 ^ 3 ∧ b6 ^ 4 = c6 ^ 3 ∧ (a6 * b6 * b6) ^ 5 = 1 ∧
      c6 ∈ center model6 :=
  model6_facts_of_rel model6_rel

end CFSG.KC.Eight89K

end
