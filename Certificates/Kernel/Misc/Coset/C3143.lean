module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.CoverActionDataInputs
public import CFSG.Certificates.Kernel.Misc.Coset.T46WordsSound
public import Certificates.Kernel.Misc.T46
public import Certificates.Kernel.Misc.Coset.XT46W.Data
public import Certificates.Kernel.Misc.Coset.ActBlocks
public import Certificates.Kernel.Misc.Coset.C10017
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.LieType.Multipliers.U62BridgeInputs
import CFSG.LieType.Multipliers.U62Data
import CFSG.LieType.Multipliers.CoverWords
import CFSG.Certificates.PresentationLetters
import CFSG.Certificates.CosetTablePresented

public section

namespace CertificateChecks.KernelMiscCoset.C3143

open CFSG.KC.MiscCoset CFSG.CosetTable CFSG.LieType.Multipliers CFSG.LieType.Multipliers.U62
  CFSG.EvenSmallLie.UnitarySix CFSG.Certificates.CosetEnumeration CFSG.F4.Native

set_option maxRecDepth 100000

@[expose] def DR : List (List Int) :=
  [[-1, -1],
    [-4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15],
    [-1, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15],
    [-1, -4, -46, -18, 14, 46, 15, -1, 15, 46, 14, -18, -46, -4, -1, -4, -46, -18, 14, 46, 15, -1, 15, 46, 14, -18, -46, -4, -1, -4, -46, -18, 14, 46, 15, -1, 15, 46, 14, -18, -46, -4],
    [-1, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -1, 15, 46, 14, -18, -46, -4, -1, 15, 46, 14, -18, -46, -4, -1, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -1, 15, 46, 14, -18, -46, -4, -1, 15, 46, 14, -18, -46, -4],
    [-22, -2, 1, 4, 8, -26, -22, -2, 1, 4, 8, -26, -22, -2, 1, 4, 8, -26],
    [-22, -2, 1, 4, 8, -26, -1, -26, 8, 4, 1, -2, -22, -1],
    [-22, -2, 1, 4, 8, -26, -4, -46, -18, 14, 46, 15, -26, 8, 4, 1, -2, -22, 15, 46, 14, -18, -46, -4],
    [22, 22],
    [22, -1, 22, -1],
    [22, 15, 46, 14, -18, -46, -4, -1, -4, -46, -18, 14, 46, 15, 22, 15, 46, 14, -18, -46, -4, -1, -4, -46, -18, 14, 46, 15],
    [22, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, -1, 15, 46, 14, -18, -46, -4, 15, 46, 14, -18, -46, -4, 22, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, -1, 15, 46, 14, -18, -46, -4, 15, 46, 14, -18, -46, -4],
    [22, 15, 46, 14, -18, -46, -4, 15, 46, 14, -18, -46, -4, -1, -4, -46, -18, 14, 46, 15, -1, 15, 46, 14, -18, -46, -4, -26, 8, 4, 1, -2, -22, 22, -22, -2, 1, 4, 8, -26, -4, -46, -18, 14, 46, 15, -1, 15, 46, 14, -18, -46, -4, -1, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15],
    [22, -1, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -1, -26, 8, 4, 1, -2, -22, 22, -26, 8, 4, 1, -2, -22, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15],
    [22, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -1, -4, -46, -18, 14, 46, 15, -4, -46, -18, 14, 46, 15, 22, 15, 46, 14, -18, -46, -4, 15, 46, 14, -18, -46, -4, -1, 15, 46, 14, -18, -46, -4, -1, 15, 46, 14, -18, -46, -4, 15, 46, 14, -18, -46, -4, -1, 15, 46, 14, -18, -46, -4, -1, 15, 46, 14, -18, -46, -4],
    [22, -4, -46, -18, 14, 46, 15, -1, 15, 46, 14, -18, -46, -4, 22, -4, -46, -18, 14, 46, 15, -1, 15, 46, 14, -18, -46, -4, 22, -4, -46, -18, 14, 46, 15, -1, 15, 46, 14, -18, -46, -4],
    [-22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22],
    [-22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, -1, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, -1],
    [-22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, -4, -46, -18, 14, 46, 15, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 15, 46, 14, -18, -46, -4],
    [-22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, -22, -2, 1, 4, 8, -26, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, -22, -2, 1, 4, 8, -26],
    [-22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22],
    [-22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22, 15, 46, 14, -18, -46, -4, -1, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22, 15, 46, 14, -18, -46, -4, -1, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22, 15, 46, 14, -18, -46, -4, -1, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22, 15, 46, 14, -18, -46, -4, -1, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22, 15, 46, 14, -18, -46, -4, -1, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22, 15, 46, 14, -18, -46, -4, -1, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22, 15, 46, 14, -18, -46, -4, -1],
    [-22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22, -22, -2, 1, 4, 8, -26, -1, 15, 46, 14, -18, -46, -4, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22, -22, -2, 1, 4, 8, -26, -1, 15, 46, 14, -18, -46, -4, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22, -22, -2, 1, 4, 8, -26, -1, 15, 46, 14, -18, -46, -4, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22, -22, -2, 1, 4, 8, -26, -1, 15, 46, 14, -18, -46, -4, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22, -22, -2, 1, 4, 8, -26, -1, 15, 46, 14, -18, -46, -4, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22, -22, -2, 1, 4, 8, -26, -1, 15, 46, 14, -18, -46, -4, -22, -2, 1, 4, 8, -26, 35, -26, 8, 4, 1, -2, -22, 22, -22, -2, 1, 4, 8, -26, -1, 15, 46, 14, -18, -46, -4]]

theorem hD : rels.map (fun r => expand (substWord deltaWords r)) = DR := by decide +kernel

theorem letters : T46W.lettersK DR [] [] [] [] = true := by quickRfl

theorem points : Act.allR (nat_lit 0) (nat_lit 693)
    (T46W.pointK CFSG.KAct.XT46W.A CFSG.KD.Misc.T46.GP DR [] [] [] []) = true := by
  allR_blocks 16

theorem deltaRel : deltaRelCheck = true := by
  have h := T46W.pointK_sound CFSG.KD.Misc.Unitary.hU CFSG.KD.Misc.T46.pts
    CFSG.KD.Misc.T46.genAll letters fun x hx => Act.allR_spec points x (Nat.zero_le x) (by omega)
  have e : deltaRelCheck = (rels.map fun r => expand (substWord deltaWords r)).all
      (fun r => t46FixAll (CFSG.Sporadic.Th.Native.wordT 693 (CFSG.KC.Misc.T46.genG uPts) r)) := by
    rw [deltaRelCheck, List.all_map]
    rfl
  rw [e, hD]
  simp only [T46W.wordsG, Bool.and_eq_true] at h
  exact h.1.1.1

theorem moves : Act.movesOK CFSG.KAct.XU62K.A (Nat.add 5 5) (codes obsMoveWords) = true := by
  quickRfl

theorem obs : ∃ (E : Type) (_ : Group E) (ψ : PG 5 coverWs →* E),
    ∀ u ∈ obsMoveWords, ψ (PresentedGroup.mk _ (FreeGroup.mk u)) ≠ 1 := by
  have hpt := Act.coverPointOK_sound rels (fun i => commWords (coverPairs i)) fixWords C10017.hR
    C10017.hW (Act.coverPointOK_of_allR CFSG.KAct.XU62K.all)
  obtain ⟨E, _, ψ, -, h⟩ := Act.movesOK_sound coverWs fixWords
    (by simp only [codes, List.map_append]) (by norm_num) hpt obsMoveWords moves
  exact ⟨E, _, ψ, h⟩

end CertificateChecks.KernelMiscCoset.C3143

end
