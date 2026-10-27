module

public import CFSG.Alternating.Multipliers.Carmichael
public import Certificates.Kernel.Misc.Coset.XCar3
public import Certificates.Kernel.Misc.Coset.XCar4
public import Certificates.Kernel.Misc.Coset.XCar5
public import Certificates.Kernel.Misc.Coset.XCar3A.All
public import Certificates.Kernel.Misc.Coset.XCar4A.All
public import Certificates.Kernel.Misc.Coset.XCar5A.All

public section

namespace CertificateChecks.KernelMiscCoset.C2326

open CFSG.CosetTable CFSG.KC.MiscCoset CFSG.Alternating.Multipliers CFSG.LieType.Multipliers
  CFSG.Certificates.CosetEnumeration

abbrev W (k : ℕ) : List (List (Fin k × Bool)) :=
  coverWords (carmichaelWords k) fun i => commWords (carmichaelPairs k i)

theorem t3 : (W 3).map encW = CFSG.KBRoute.XCar3.rels := by decide +kernel
theorem t4 : (W 4).map encW = CFSG.KBRoute.XCar4.rels := by decide +kernel
theorem t5 : (W 5).map encW = CFSG.KBRoute.XCar5.rels := by decide +kernel
theorem a3 : codes (W 3) = CFSG.KAct.XCar3.rels := by decide +kernel
theorem a4 : codes (W 4) = CFSG.KAct.XCar4.rels := by decide +kernel
theorem a5 : codes (W 5) = CFSG.KAct.XCar5.rels := by decide +kernel
theorem u3 : (carmichaelRel01 1).map letterCode = [0, 2, 0, 2] := by decide +kernel
theorem u4 : (carmichaelRel01 2).map letterCode = [0, 2, 0, 2] := by decide +kernel
theorem u5 : (carmichaelRel01 3).map letterCode = [0, 2, 0, 2] := by decide +kernel

theorem five : Finite (PG 3 (W 3)) ∧ Nat.card (PG 3 (W 3)) ≤ 120 ∧
    2 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 3) | r ∈ (W 3).map FreeGroup.mk}
      (FreeGroup.mk (carmichaelRel01 1))) := by
  have h := XCar3.t1
  unfold CFSG.KBRoute.XCar3.T1.ok at h
  obtain ⟨f, c⟩ := card_le_of_tableOk (W 3) t3 h (by norm_num) CFSG.KBRoute.XCar3.top rfl
  refine ⟨f, c, Act.cycleOK_sound (W 3) a3 (by norm_num) (Act.pointOK_of_allR CFSG.KAct.XCar3.all)
    _ ?_⟩
  rw [u3]
  exact CFSG.KAct.XCar3.cyc0

theorem six : Finite (PG 4 (W 4)) ∧ Nat.card (PG 4 (W 4)) ≤ 2160 ∧
    6 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ (W 4).map FreeGroup.mk}
      (FreeGroup.mk (carmichaelRel01 2))) := by
  have h := XCar4.t1
  unfold CFSG.KBRoute.XCar4.T1.ok at h
  obtain ⟨f, c⟩ := card_le_of_tableOk (W 4) t4 h (by norm_num) CFSG.KBRoute.XCar4.top rfl
  refine ⟨f, c, Act.cycleOK_sound (W 4) a4 (by norm_num) (Act.pointOK_of_allR CFSG.KAct.XCar4.all)
    _ ?_⟩
  rw [u4]
  exact CFSG.KAct.XCar4.cyc0

theorem seven : Finite (PG 5 (W 5)) ∧ Nat.card (PG 5 (W 5)) ≤ 15120 ∧
    6 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin 5) | r ∈ (W 5).map FreeGroup.mk}
      (FreeGroup.mk (carmichaelRel01 3))) := by
  have h := XCar5.t1
  unfold CFSG.KBRoute.XCar5.T1.ok at h
  obtain ⟨f, c⟩ := card_le_of_tableOk (W 5) t5 h (by norm_num) CFSG.KBRoute.XCar5.top rfl
  refine ⟨f, c, Act.cycleOK_sound (W 5) a5 (by norm_num) (Act.pointOK_of_allR CFSG.KAct.XCar5.all)
    _ ?_⟩
  rw [u5]
  exact CFSG.KAct.XCar5.cyc0

end CertificateChecks.KernelMiscCoset.C2326

end
