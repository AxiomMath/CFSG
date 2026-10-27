module

public import Certificates.Kernel.YChain.Step
public import Certificates.Kernel.YChain.Tables.YCh01
public import Certificates.Kernel.YChain.Tables.YCh02
public import Certificates.Kernel.YChain.Tables.YCh03
public import Certificates.Kernel.YChain.Tables.YCh04
public import Certificates.Kernel.YChain.Tables.YCh05
public import Certificates.Kernel.YChain.Tables.YCh06
public import Certificates.Kernel.YChain.Tables.YCh07
public import Certificates.Kernel.YChain.Tables.YCh08
public import Certificates.Kernel.YChain.Tables.YCh09
public import Certificates.Kernel.YChain.Tables.YCh10

public section

namespace CertificateChecks.KernelYChain

open CFSG.YGroups CFSG.Certificates CFSG.Certificates.KB

theorem y000 : Finite (YGroup 0 0 0) ∧ Nat.card (YGroup 0 0 0) ≤ 2 := by
  have t := YCh01.t1
  unfold CFSG.KBRoute.YCh01.T1.ok at t
  exact card_le_of_table_bot t (by decide +kernel) (by decide) CFSG.KBRoute.YCh01.top

theorem rels_y000_y100 : ∀ w ∈ yRels 0 0 0, w.map (shiftAt 0) ∈ yRels 1 0 0 := by decide

theorem y100 : Finite (YGroup 1 0 0) ∧ Nat.card (YGroup 1 0 0) ≤ 3 * 2 := by
  have := y000.1
  have t := YCh02.t1
  unfold CFSG.KBRoute.YCh02.T1.ok at t
  have h := card_le_of_table (shiftAt 0) rels_y000_y100 t (by decide +kernel) (by decide +kernel)
    (by decide) CFSG.KBRoute.YCh02.top
  exact ⟨h.1, h.2.trans (Nat.mul_le_mul_left _ y000.2)⟩

theorem rels_y100_y110 : ∀ w ∈ yRels 1 0 0, w.map (shiftAt 1) ∈ yRels 1 1 0 := by decide

theorem y110 : Finite (YGroup 1 1 0) ∧ Nat.card (YGroup 1 1 0) ≤ 4 * (3 * 2) := by
  have := y100.1
  have t := YCh03.t1
  unfold CFSG.KBRoute.YCh03.T1.ok at t
  have h := card_le_of_table (shiftAt 1) rels_y100_y110 t (by decide +kernel) (by decide +kernel)
    (by decide) CFSG.KBRoute.YCh03.top
  exact ⟨h.1, h.2.trans (Nat.mul_le_mul_left _ y100.2)⟩

theorem rels_y110_y111 : ∀ w ∈ yRels 1 1 0, w.map (shiftAt 2) ∈ yRels 1 1 1 := by decide

theorem y111 : Finite (YGroup 1 1 1) ∧ Nat.card (YGroup 1 1 1) ≤ 8 * (4 * (3 * 2)) := by
  have := y110.1
  have t := YCh04.t1
  unfold CFSG.KBRoute.YCh04.T1.ok at t
  have h := card_le_of_table (shiftAt 2) rels_y110_y111 t (by decide +kernel) (by decide +kernel)
    (by decide) CFSG.KBRoute.YCh04.top
  exact ⟨h.1, h.2.trans (Nat.mul_le_mul_left _ y110.2)⟩

theorem rels_y111_y211 : ∀ w ∈ yRels 1 1 1, w.map (shiftAt 1) ∈ yRels 2 1 1 := by decide

theorem y211 : Finite (YGroup 2 1 1) ∧ Nat.card (YGroup 2 1 1) ≤ 10 * (8 * (4 * (3 * 2))) := by
  have := y111.1
  have t := YCh05.t1
  unfold CFSG.KBRoute.YCh05.T1.ok at t
  have h := card_le_of_table (shiftAt 1) rels_y111_y211 t (by decide +kernel) (by decide +kernel)
    (by decide) CFSG.KBRoute.YCh05.top
  exact ⟨h.1, h.2.trans (Nat.mul_le_mul_left _ y111.2)⟩

theorem rels_y211_y221 : ∀ w ∈ yRels 2 1 1, w.map (shiftAt 3) ∈ yRels 2 2 1 := by decide

theorem y221 : Finite (YGroup 2 2 1) ∧ Nat.card (YGroup 2 2 1) ≤ 51840 := by
  have := y211.1
  have t := YCh06.t1
  unfold CFSG.KBRoute.YCh06.T1.ok at t
  have h := card_le_of_table (shiftAt 3) rels_y211_y221 t (by decide +kernel) (by decide +kernel)
    (by decide) CFSG.KBRoute.YCh06.top
  exact ⟨h.1, h.2.trans (by have := Nat.mul_le_mul_left 27 y211.2; omega)⟩

theorem rels_y221_y222 : ∀ w ∈ yRels 2 2 1, w.map (shiftAt 5) ∈ yRels 2 2 2 := by decide

theorem y222 : Finite (YGroup 2 2 2) ∧ Nat.card (YGroup 2 2 2) ≤ 12597120 := by
  have := y221.1
  have t := YCh07.t1
  unfold CFSG.KBRoute.YCh07.T1.ok at t
  have h := card_le_of_table (shiftAt 5) rels_y221_y222 t (by decide +kernel) (by decide +kernel)
    (by decide) CFSG.KBRoute.YCh07.top
  exact ⟨h.1, h.2.trans (by have := Nat.mul_le_mul_left 243 y221.2; omega)⟩

theorem rels_y222_y322 : ∀ w ∈ yRels 2 2 2, w.map (shiftAt 2) ∈ yRels 3 2 2 := by decide

theorem y322 : Finite (YGroup 3 2 2) ∧ Nat.card (YGroup 3 2 2) ≤ 9170703360 := by
  have := y222.1
  have t := YCh08.t1
  unfold CFSG.KBRoute.YCh08.T1.ok at t
  have h := card_le_of_table (shiftAt 2) rels_y222_y322 t (by decide +kernel) (by decide +kernel)
    (by decide) CFSG.KBRoute.YCh08.top
  exact ⟨h.1, h.2.trans (by have := Nat.mul_le_mul_left 728 y222.2; omega)⟩

theorem rels_y322_y332 : ∀ w ∈ yRels 3 2 2, w.map (shiftAt 5) ∈ yRels 3 3 2 := by decide

theorem y332 : Finite (YGroup 3 3 2) ∧ Nat.card (YGroup 3 3 2) ≤ 258247006617600 := by
  have := y322.1
  have t := YCh09.t1
  unfold CFSG.KBRoute.YCh09.T1.ok at t
  have h := card_le_of_table (shiftAt 5) rels_y322_y332 t (by decide +kernel) (by decide +kernel)
    (by decide) CFSG.KBRoute.YCh09.top
  exact ⟨h.1, h.2.trans (by have := Nat.mul_le_mul_left 28160 y322.2; omega)⟩

theorem rels_y332_y432 : ∀ w ∈ yRels 3 3 2, w.map (shiftAt 3) ∈ yRels 4 3 2 := by decide

theorem y432 : Finite (YGroup 4 3 2) ∧ Nat.card (YGroup 4 3 2) ≤ 8178940946586009600 := by
  have := y332.1
  have t := YCh10.t1
  unfold CFSG.KBRoute.YCh10.T1.ok at t
  have h := card_le_of_table (shiftAt 3) rels_y332_y432 t (by decide +kernel) (by decide +kernel)
    (by decide) CFSG.KBRoute.YCh10.top
  exact ⟨h.1, h.2.trans (by have := Nat.mul_le_mul_left 31671 y332.2; omega)⟩

end CertificateChecks.KernelYChain

end
