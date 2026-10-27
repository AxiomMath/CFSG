module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.DSFactsNonsplitDataInputs
public import CFSG.Certificates.Kernel.Misc.Coset.T46WordsSound
public import Certificates.Kernel.Misc.T46
public import Certificates.Kernel.Misc.Coset.XT46W.Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
public import Certificates.Kernel.Misc.Coset.C10017
public import Certificates.Kernel.UnitarySix.Struct3010
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.LieType.Multipliers.U62BridgeInputs
import CFSG.LieType.Multipliers.U62Data
import CFSG.LieType.Multipliers.CoverWords
import CFSG.Certificates.PresentationLetters
import CFSG.Certificates.CosetTablePresented

public section

namespace CertificateChecks.KernelMiscCoset.C3144

open CFSG.KC.MiscCoset CFSG.CosetTable CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62
  CFSG.EvenSmallLie.UnitarySix CFSG.Certificates.CosetEnumeration CFSG.F4.Native CFSG.KC.U6
  CertificateChecks.KernelU6

set_option maxRecDepth 100000

@[expose] noncomputable def nsEN : List Nat :=
  [1, 7, 91, 35, 26, 90, 28, 7, 91, 35, 26, 90, 28, 42, 43, 3, 0, 6, 14, 51, 42, 7, 91, 35, 26, 90,
    28, 1, 28, 90, 26, 35, 91, 7, 42, 51, 14, 6, 0, 3, 43, 42, 28, 90, 26, 35, 91, 7, 28, 90, 26,
    35, 91, 7, 68]

@[expose] noncomputable def nsN1N : List Nat :=
  [7, 91, 35, 26, 90, 28, 42, 51, 14, 6, 0, 3, 43, 7, 91, 35, 26, 90, 28, 1, 7, 91, 35, 26, 90, 28,
    7, 91, 35, 26, 90, 28, 42, 1, 7, 91, 35, 26, 90, 28, 42, 68, 42, 7, 91, 35, 26, 90, 28, 42]

@[expose] noncomputable def nsN2N : List Nat :=
  [42, 28, 90, 26, 35, 91, 7, 28, 90, 26, 35, 91, 7, 1, 28, 90, 26, 35, 91, 7, 42, 7, 91, 35, 26,
    90, 28, 42, 7, 91, 35, 26, 90, 28, 68, 42, 28, 90, 26, 35, 91, 7, 42, 28, 90, 26, 35, 91, 7, 51,
    14, 6, 0, 3, 43]

@[expose] noncomputable def MA : Nat := nat_lit 3417360655900012744524710438636167847359307910347583640659341401022203592618440293572727200307832553568217612577232634602632193701256698739568508731895582238916007968296506470787734073437063202424477023772590984525569867821262648171668620444673

@[expose] noncomputable def MB : Nat := nat_lit 100777263590198943715092122492575795477480397822

theorem nsEN_eq : expand nsE = nsEN.map decZ := by decide +kernel
theorem nsN1N_eq : expand nsN₁ = nsN1N.map decZ := by decide +kernel
theorem nsN2N_eq : expand nsN₂ = nsN2N.map decZ := by decide +kernel

theorem kA : check3010S U.LT aWN aWN [nsEN] MA [[0, 2, 8]] = true := by quickRfl
theorem kB : check3010S U.LT aWN [nsN1N, nsN2N] [] MB [] = true := by quickRfl

theorem nsE_mem :
    u62W (expand nsE) ∈ Subgroup.closure {g | g ∈ aGens} := by
  have h := (sound3010S letters_eq aWN_eq aWN_eq (tw := [expand nsE])
    (by simp only [nsEN_eq, List.map_cons, List.map_nil]) kA).2.2
  exact h _ List.mem_cons_self

theorem nsN_conj :
    ∀ k ∈ [u62W (expand nsN₁), u62W (expand nsN₂)], ∀ a ∈ aGens,
      k * a * k⁻¹ ∈ Subgroup.closure {g | g ∈ aGens} := by
  have h := (sound3010S letters_eq aWN_eq (kw := [expand nsN₁, expand nsN₂]) (tw := [])
    (by simp only [nsN1N_eq, nsN2N_eq, List.map_cons, List.map_nil]) rfl kB).2.1
  intro k hk
  exact h k (List.mem_append_left _ hk)

@[expose] def RC : List (List Int) :=
  [[-4, -46, -18, 14, 46, 15, 22, -26, 8, 4, 1, -2, -22, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, 22, -1, -4, -46, -18, 14, 46, 15, 22, 35, 22, -4, -46, -18, 14, 46, 15, 22, -1, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, 22, -22, -2, 1, 4, 8, -26, 22, -4, -46, -18, 14, 46, 15, -1, 15, 46, 14, -18, -46, -4, 22, -26, 8, 4, 1, -2, -22, 22, 15, 46, 14, -18, -46, -4, 15, 46, 14, -18, -46, -4, 35, 22, 15, 46, 14, -18, -46, -4, 22, 35, 22, 15, 46, 14, -18, -46, -4, -1, 22, 15, 46, 14, -18, -46, -4, 15, 46, 14, -18, -46, -4, -1, 15, 46, 14, -18, -46, -4, -22, -2, 1, 4, 8, -26, 22, 15, 46, 14, -18, -46, -4, 35, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, 22, -22, -2, 1, 4, 8, -26, 22, -4, -46, -18, 14, 46, 15, -1, 15, 46, 14, -18, -46, -4, 22, -26, 8, 4, 1, -2, -22, 22, 15, 46, 14, -18, -46, -4, 15, 46, 14, -18, -46, -4, -1],
    [22, 15, 46, 14, -18, -46, -4, 15, 46, 14, -18, -46, -4, -1, 15, 46, 14, -18, -46, -4, 22, -4, -46, -18, 14, 46, 15, 22, -4, -46, -18, 14, 46, 15, 35, 22, 15, 46, 14, -18, -46, -4, 22, 15, 46, 14, -18, -46, -4, -26, 8, 4, 1, -2, -22, -1, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, 22, -22, -2, 1, 4, 8, -26, 22, -4, -46, -18, 14, 46, 15, -1, 15, 46, 14, -18, -46, -4, 22, -26, 8, 4, 1, -2, -22, 22, 15, 46, 14, -18, -46, -4, 15, 46, 14, -18, -46, -4, 35, -22, -2, 1, 4, 8, -26, -4, -46, -18, 14, 46, 15, 22, -4, -46, -18, 14, 46, 15, 22, 35, 15, 46, 14, -18, -46, -4, 22, 15, 46, 14, -18, -46, -4, 22, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, 22, 35, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, 22, -22, -2, 1, 4, 8, -26, 22, -4, -46, -18, 14, 46, 15, -1, 15, 46, 14, -18, -46, -4, 22, -26, 8, 4, 1, -2, -22, 22, 15, 46, 14, -18, -46, -4, 15, 46, 14, -18, -46, -4, -1]]

theorem hC : [expand nsC₁, expand nsC₂] = RC := by decide +kernel

theorem letters : T46W.lettersK RC [] [] [] [] = true := by quickRfl

theorem points : Act.allR (nat_lit 0) (nat_lit 693)
    (T46W.pointK CFSG.KAct.XT46W.A CFSG.KD.Misc.T46.GP RC [] [] [] []) = true := by
  allR_blocks 16

theorem comm_fix : t46FixAll (CFSG.Sporadic.Th.Native.wordT 693 CFSG.Sporadic.Fi22.Native.t46Gen
      (expand nsC₁)) = true ∧
    t46FixAll (CFSG.Sporadic.Th.Native.wordT 693 CFSG.Sporadic.Fi22.Native.t46Gen
      (expand nsC₂)) = true := by
  have h := T46W.pointK_sound CFSG.KD.Misc.Unitary.hU CFSG.KD.Misc.T46.pts
    CFSG.KD.Misc.T46.genAll letters fun x hx => Act.allR_spec points x (Nat.zero_le x) (by omega)
  have e : [expand nsC₁, expand nsC₂].all (fun r => t46FixAll
      (CFSG.Sporadic.Th.Native.wordT 693 CFSG.Sporadic.Fi22.Native.t46Gen r)) =
      RC.all (fun r => t46FixAll
        (CFSG.Sporadic.Th.Native.wordT 693 (CFSG.KC.Misc.T46.genG uPts) r)) := by
    rw [← hC]
    rfl
  simp only [T46W.wordsG, Bool.and_eq_true] at h
  have h1 := h.1.1.1
  rw [← e] at h1
  simpa only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] using h1

theorem moves : Act.movesOK CFSG.KAct.XU62K.A (Nat.add 5 5)
    (codes (exclWords nsC₁ (0, 1, 0) ++ exclWords nsC₂ (0, 0, 1))) = true := by
  quickRfl

theorem cover : ∃ (E : Type) (_ : Group E) (ψ : PG 5 coverWs →* E),
    ∀ u ∈ exclWords nsC₁ (0, 1, 0) ++ exclWords nsC₂ (0, 0, 1),
      ψ (PresentedGroup.mk _ (FreeGroup.mk u)) ≠ 1 := by
  have hpt := Act.coverPointOK_sound rels (fun i => commWords (coverPairs i)) fixWords C10017.hR
    C10017.hW (Act.coverPointOK_of_allR CFSG.KAct.XU62K.all)
  obtain ⟨E, _, ψ, -, h⟩ := Act.movesOK_sound coverWs fixWords
    (by simp only [codes, List.map_append]) (by norm_num) hpt _ moves
  exact ⟨E, _, ψ, h⟩

end CertificateChecks.KernelMiscCoset.C3144

end
