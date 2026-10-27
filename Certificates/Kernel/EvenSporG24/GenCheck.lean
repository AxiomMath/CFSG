module

public import Certificates.Kernel.EvenSporG24.TblText
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.G24ModelHex
import all Init.Data.List.SplitOn.Basic

public section

namespace CertificateChecks.EvenSporG24

open CFSG.EvenSporadicStandard.G24Model CFSG.Fischer

@[expose] def xCodeN (i c a b : Nat) : Nat :=
  if h : i < 2 ∧ c < 4 ∧ a < 14 ∧ b < 14 then
    (xEnt ⟨i, h.1⟩ ⟨⟨c, h.2.1⟩⟩ ⟨a, h.2.2.1⟩ ⟨b, h.2.2.2⟩).code.val
  else 0

@[expose] def yCodeN (i c a b : Nat) : Nat :=
  if h : i < 2 ∧ c < 4 ∧ a < 14 ∧ b < 14 then
    (yEnt ⟨i, h.1⟩ ⟨⟨c, h.2.1⟩⟩ ⟨a, h.2.2.1⟩ ⟨b, h.2.2.2⟩).code.val
  else 0

@[expose] noncomputable def entL : List Nat := tblL.drop 2730

@[expose] noncomputable def genOKK : Bool :=
  (List.range 2).all fun i => (List.range 4).all fun c => (List.range 14).all fun a =>
    (List.range 14).all fun b =>
      xCodeN i c a b == entL.getD (196 * (4 * i + c) + 14 * a + b) 0 % 4 &&
        yCodeN i c a b == entL.getD (196 * (8 + 4 * i + c) + 14 * a + b) 0 % 4

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem genOKK_true : genOKK = true := by
  have hD : ∀ (L : List Nat) (x y : Nat), L.getD (x + y) 0 = (L.drop x).getD y 0 := by
    intro L x y
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  have hDD : ∀ (L : List Nat) (x y : Nat), L.drop (x + y) = (L.drop x).drop y := by
    intro L x y
    rw [List.drop_drop]
  unfold genOKK
  simp only [hD, hDD]
  decide +kernel

end CertificateChecks.EvenSporG24
