module

public import Certificates.Kernel.YChain.Chain
public import Certificates.Kernel.YChain.Tables.YCa01
public import Certificates.Kernel.YChain.Tables.YCa02
public import Certificates.Kernel.YChain.Tables.YCa03
public import Certificates.Kernel.YChain.Tables.YCa04
public import Certificates.Kernel.YChain.Tables.YCa05
public import Certificates.Kernel.YChain.Tables.YCa06

public section

namespace CertificateChecks.KernelYChain

open CFSG.YGroups CFSG.Certificates CFSG.Certificates.KB

theorem rels_y110_y210 : ∀ w ∈ yRels 1 1 0, w.map (shiftAt 1) ∈ yRels 2 1 0 := by decide

theorem y210 : Finite (YGroup 2 1 0) ∧ Nat.card (YGroup 2 1 0) ≤ 120 := by
  have := y110.1
  have t := YCa01.t1
  unfold CFSG.KBRoute.YCa01.T1.ok at t
  have h := card_le_of_table (shiftAt 1) rels_y110_y210 t (by decide +kernel) (by decide +kernel)
    (by decide) CFSG.KBRoute.YCa01.top
  exact ⟨h.1, h.2.trans (by have := Nat.mul_le_mul_left 5 y110.2; omega)⟩

theorem rels_y210_y220 : ∀ w ∈ yRels 2 1 0, w.map (shiftAt 3) ∈ yRels 2 2 0 := by decide

theorem y220 : Finite (YGroup 2 2 0) ∧ Nat.card (YGroup 2 2 0) ≤ 720 := by
  have := y210.1
  have t := YCa02.t1
  unfold CFSG.KBRoute.YCa02.T1.ok at t
  have h := card_le_of_table (shiftAt 3) rels_y210_y220 t (by decide +kernel) (by decide +kernel)
    (by decide) CFSG.KBRoute.YCa02.top
  exact ⟨h.1, h.2.trans (by have := Nat.mul_le_mul_left 6 y210.2; omega)⟩

theorem rels_y220_y320 : ∀ w ∈ yRels 2 2 0, w.map (shiftAt 2) ∈ yRels 3 2 0 := by decide

theorem y320 : Finite (YGroup 3 2 0) ∧ Nat.card (YGroup 3 2 0) ≤ 5040 := by
  have := y220.1
  have t := YCa03.t1
  unfold CFSG.KBRoute.YCa03.T1.ok at t
  have h := card_le_of_table (shiftAt 2) rels_y220_y320 t (by decide +kernel) (by decide +kernel)
    (by decide) CFSG.KBRoute.YCa03.top
  exact ⟨h.1, h.2.trans (by have := Nat.mul_le_mul_left 7 y220.2; omega)⟩

theorem rels_y320_y330 : ∀ w ∈ yRels 3 2 0, w.map (shiftAt 5) ∈ yRels 3 3 0 := by decide

theorem y330 : Finite (YGroup 3 3 0) ∧ Nat.card (YGroup 3 3 0) ≤ 40320 := by
  have := y320.1
  have t := YCa04.t1
  unfold CFSG.KBRoute.YCa04.T1.ok at t
  have h := card_le_of_table (shiftAt 5) rels_y320_y330 t (by decide +kernel) (by decide +kernel)
    (by decide) CFSG.KBRoute.YCa04.top
  exact ⟨h.1, h.2.trans (by have := Nat.mul_le_mul_left 8 y320.2; omega)⟩

theorem rels_y330_y430 : ∀ w ∈ yRels 3 3 0, w.map (shiftAt 3) ∈ yRels 4 3 0 := by decide

theorem y430 : Finite (YGroup 4 3 0) ∧ Nat.card (YGroup 4 3 0) ≤ 362880 := by
  have := y330.1
  have t := YCa05.t1
  unfold CFSG.KBRoute.YCa05.T1.ok at t
  have h := card_le_of_table (shiftAt 3) rels_y330_y430 t (by decide +kernel) (by decide +kernel)
    (by decide) CFSG.KBRoute.YCa05.top
  exact ⟨h.1, h.2.trans (by have := Nat.mul_le_mul_left 9 y330.2; omega)⟩

theorem rels_y430_y440 : ∀ w ∈ yRels 4 3 0, w.map (shiftAt 7) ∈ yRels 4 4 0 := by decide

theorem y440 : Finite (YGroup 4 4 0) ∧ Nat.card (YGroup 4 4 0) ≤ 3628800 := by
  have := y430.1
  have t := YCa06.t1
  unfold CFSG.KBRoute.YCa06.T1.ok at t
  have h := card_le_of_table (shiftAt 7) rels_y430_y440 t (by decide +kernel) (by decide +kernel)
    (by decide) CFSG.KBRoute.YCa06.top
  exact ⟨h.1, h.2.trans (by have := Nat.mul_le_mul_left 10 y430.2; omega)⟩

end CertificateChecks.KernelYChain

end
