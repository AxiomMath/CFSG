module

public import Certificates.Data.Kernel.M24G.TrioOne

set_option maxRecDepth 400000

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

theorem range64_of_8 {F : Nat → Bool} (h0 : ∀ j < 8, F j = true) (h1 : ∀ j < 8, F (8 + j) = true)
    (h2 : ∀ j < 8, F (16 + j) = true) (h3 : ∀ j < 8, F (24 + j) = true)
    (h4 : ∀ j < 8, F (32 + j) = true) (h5 : ∀ j < 8, F (40 + j) = true)
    (h6 : ∀ j < 8, F (48 + j) = true) (h7 : ∀ j < 8, F (56 + j) = true) :
    (List.range 64).all F = true := by
  rw [List.all_eq_true]
  intro s hs
  rw [List.mem_range] at hs
  have key : ∀ b, (∀ j < 8, F (b + j) = true) → b ≤ s → s < b + 8 → F s = true := by
    intro b hb h1 h2
    have h := hb (s - b) (by omega)
    rwa [show b + (s - b) = s by omega] at h
  by_cases c0 : s < 8
  · exact h0 s c0
  by_cases c1 : s < 16
  · exact key 8 h1 (by omega) (by omega)
  by_cases c2 : s < 24
  · exact key 16 h2 (by omega) (by omega)
  by_cases c3 : s < 32
  · exact key 24 h3 (by omega) (by omega)
  by_cases c4 : s < 40
  · exact key 32 h4 (by omega) (by omega)
  by_cases c5 : s < 48
  · exact key 40 h5 (by omega) (by omega)
  by_cases c6 : s < 56
  · exact key 48 h6 (by omega) (by omega)
  · exact key 56 h7 (by omega) (by omega)

theorem gA : ((List.range 6).all (fun j => prodL (1 <<< j) == (Native.tTabs.getD j #[]).toList) &&
    prodL 0 == Native.r121IdTab.toList) = true := by
  decide +kernel

theorem gB0 : ∀ j < 8, ((List.range 64).all fun s' =>
    composeL (prodL j) (prodL s') == prodL (j ^^^ s')) = true := by
  decide +kernel

theorem gB1 : ∀ j < 8, ((List.range 64).all fun s' =>
    composeL (prodL (8 + j)) (prodL s') == prodL ((8 + j) ^^^ s')) = true := by
  decide +kernel

theorem gB2 : ∀ j < 8, ((List.range 64).all fun s' =>
    composeL (prodL (16 + j)) (prodL s') == prodL ((16 + j) ^^^ s')) = true := by
  decide +kernel

theorem gB3 : ∀ j < 8, ((List.range 64).all fun s' =>
    composeL (prodL (24 + j)) (prodL s') == prodL ((24 + j) ^^^ s')) = true := by
  decide +kernel

theorem gB4 : ∀ j < 8, ((List.range 64).all fun s' =>
    composeL (prodL (32 + j)) (prodL s') == prodL ((32 + j) ^^^ s')) = true := by
  decide +kernel

theorem gB5 : ∀ j < 8, ((List.range 64).all fun s' =>
    composeL (prodL (40 + j)) (prodL s') == prodL ((40 + j) ^^^ s')) = true := by
  decide +kernel

theorem gB6 : ∀ j < 8, ((List.range 64).all fun s' =>
    composeL (prodL (48 + j)) (prodL s') == prodL ((48 + j) ^^^ s')) = true := by
  decide +kernel

theorem gB7 : ∀ j < 8, ((List.range 64).all fun s' =>
    composeL (prodL (56 + j)) (prodL s') == prodL ((56 + j) ^^^ s')) = true := by
  decide +kernel

theorem gB : ((List.range 64).all fun s => (List.range 64).all fun s' =>
    composeL (prodL s) (prodL s') == prodL (s ^^^ s')) = true :=
  range64_of_8 (F := fun s => (List.range 64).all fun s' =>
    composeL (prodL s) (prodL s') == prodL (s ^^^ s')) gB0 gB1 gB2 gB3 gB4 gB5 gB6 gB7

theorem gC : ((List.range 64).all fun s => (List.range s).all fun s' =>
    (List.range 24).any fun i => (prodL s).getD i 0 != (prodL s').getD i 0) = true := by
  decide +kernel

theorem gD : ((List.range 64).all fun s => (prodL s).length == 24 && (prodL s).all (· < 24)) =
    true := by
  decide +kernel

theorem groupL_ok : groupL = true := by
  unfold groupL
  rw [gA, gB, gC, gD] <;> rfl

end CFSG.KC.M24G
