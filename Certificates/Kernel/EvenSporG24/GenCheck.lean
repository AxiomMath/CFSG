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

theorem getD_add_drop (L : List Nat) (x y : Nat) : L.getD (x + y) 0 = (L.drop x).getD y 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem drop_add_drop (L : List Nat) (x y : Nat) : L.drop (x + y) = (L.drop x).drop y := by
  rw [List.drop_drop]

theorem all_range_of {n : Nat} {p : Nat → Bool} (h : ∀ i < n, p i = true) :
    (List.range n).all p = true :=
  List.all_eq_true.2 fun i hi => h i (List.mem_range.1 hi)

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem genOK_0_0 : ((List.range 14).all fun a => (List.range 14).all fun b =>
    xCodeN 0 0 a b == entL.getD (196 * (4 * 0 + 0) + 14 * a + b) 0 % 4 &&
      yCodeN 0 0 a b == entL.getD (196 * (8 + 4 * 0 + 0) + 14 * a + b) 0 % 4) = true := by
  simp only [getD_add_drop, drop_add_drop]
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem genOK_0_1 : ((List.range 14).all fun a => (List.range 14).all fun b =>
    xCodeN 0 1 a b == entL.getD (196 * (4 * 0 + 1) + 14 * a + b) 0 % 4 &&
      yCodeN 0 1 a b == entL.getD (196 * (8 + 4 * 0 + 1) + 14 * a + b) 0 % 4) = true := by
  simp only [getD_add_drop, drop_add_drop]
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem genOK_0_2 : ((List.range 14).all fun a => (List.range 14).all fun b =>
    xCodeN 0 2 a b == entL.getD (196 * (4 * 0 + 2) + 14 * a + b) 0 % 4 &&
      yCodeN 0 2 a b == entL.getD (196 * (8 + 4 * 0 + 2) + 14 * a + b) 0 % 4) = true := by
  simp only [getD_add_drop, drop_add_drop]
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem genOK_0_3 : ((List.range 14).all fun a => (List.range 14).all fun b =>
    xCodeN 0 3 a b == entL.getD (196 * (4 * 0 + 3) + 14 * a + b) 0 % 4 &&
      yCodeN 0 3 a b == entL.getD (196 * (8 + 4 * 0 + 3) + 14 * a + b) 0 % 4) = true := by
  simp only [getD_add_drop, drop_add_drop]
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem genOK_1_0 : ((List.range 14).all fun a => (List.range 14).all fun b =>
    xCodeN 1 0 a b == entL.getD (196 * (4 * 1 + 0) + 14 * a + b) 0 % 4 &&
      yCodeN 1 0 a b == entL.getD (196 * (8 + 4 * 1 + 0) + 14 * a + b) 0 % 4) = true := by
  simp only [getD_add_drop, drop_add_drop]
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem genOK_1_1 : ((List.range 14).all fun a => (List.range 14).all fun b =>
    xCodeN 1 1 a b == entL.getD (196 * (4 * 1 + 1) + 14 * a + b) 0 % 4 &&
      yCodeN 1 1 a b == entL.getD (196 * (8 + 4 * 1 + 1) + 14 * a + b) 0 % 4) = true := by
  simp only [getD_add_drop, drop_add_drop]
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem genOK_1_2 : ((List.range 14).all fun a => (List.range 14).all fun b =>
    xCodeN 1 2 a b == entL.getD (196 * (4 * 1 + 2) + 14 * a + b) 0 % 4 &&
      yCodeN 1 2 a b == entL.getD (196 * (8 + 4 * 1 + 2) + 14 * a + b) 0 % 4) = true := by
  simp only [getD_add_drop, drop_add_drop]
  decide +kernel

set_option maxRecDepth 400000 in
set_option maxHeartbeats 0 in
theorem genOK_1_3 : ((List.range 14).all fun a => (List.range 14).all fun b =>
    xCodeN 1 3 a b == entL.getD (196 * (4 * 1 + 3) + 14 * a + b) 0 % 4 &&
      yCodeN 1 3 a b == entL.getD (196 * (8 + 4 * 1 + 3) + 14 * a + b) 0 % 4) = true := by
  simp only [getD_add_drop, drop_add_drop]
  decide +kernel

theorem genOKK_true : genOKK = true :=
  all_range_of fun i hi => all_range_of fun c hc => by
    interval_cases i <;> interval_cases c
    exacts [genOK_0_0, genOK_0_1, genOK_0_2, genOK_0_3, genOK_1_0, genOK_1_1, genOK_1_2, genOK_1_3]

end CertificateChecks.EvenSporG24
