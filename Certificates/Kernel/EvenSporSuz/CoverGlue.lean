module

public import CFSG.Certificates.Kernel.EvenSporSuz.CoverSound
public import Certificates.Kernel.EvenSporSuz.Cover25001
import Certificates.Kernel.EvenSporSuz.Bridge
import Certificates.Kernel.CosetJ.Suz
import CFSG.Certificates.Kernel.CosetJ.WordsTSound
import all Certificates.Kernel.EvenSporSuz.Data
import all Certificates.Kernel.EvenSporSuz.Cover25001

public section

namespace CertificateChecks.KernelSuz

open CFSG.KC.EvenSporSuz CFSG.EvenSporadicStandard.TwoSuz CFSG.Sporadic.Recognition.SuzMultiplier
  CFSG.LieType.Multipliers

theorem R0_codes : CFSG.Sporadic.Presentation.Suz.R0.map wordCodes = relCodes := by
  rw [KernelCosetJ.Suz.R0_eq]
  decide +kernel

theorem surjWords_eq : CFSG.Sporadic.Bridge.SuzGPL.Native.surjWords = CoverST.W.toArray := by
  have hw := CFSG.KC.WordsT.wordsT_sound coverST_ok
  rw [← CoverST.eq] at hw
  exact hw

theorem coverCheck_true : coverCheck = true := by
  have hK := cover25001K_true
  unfold cover25001K at hK
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hK
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hn, hcan⟩, hval⟩, hrel⟩, hw⟩, hr3⟩, hd⟩, hsA⟩, hsB⟩ := hK
  have hcan' : ∀ k < 9, canonB (cgL k).toArray = true := fun k hk => canonB_toArray (by
    have := hcan k hk
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at this ⊢
    exact this)
  have hCM : coverMats = ((List.range 9).map fun k => (cgL k).toArray).toArray := by
    unfold coverMats
    rw [CG.eq, parseMats_ofList]
    unfold matsK
    rw [hn]
    rfl
  have hE : coverMats.extract 0 7 = ((List.range 7).map fun k => (cgL k).toArray).toArray := by
    rw [hCM]
    apply Array.toList_inj.1
    simp only [Array.toList_extract, List.toList_toArray, List.extract_eq_drop_take,
      List.drop_zero, Nat.sub_zero]
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      simp
  have hEc : ∀ x ∈ coverMats.extract 0 7, canonB x = true := by
    intro x hx
    rw [hE] at hx
    simp only [List.mem_toArray, List.mem_map, List.mem_range] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact hcan' k (by omega)
  have hC : CanonGS coverGS := by
    refine ⟨canonB_getD hEc, canonB_getD fun x hx => ?_⟩
    simp only [coverGS, Array.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    exact canonB_invM _
  have hMR : coverGS.mats.toList.map rowsOf = YM := by
    simp only [coverGS, hE, List.toList_toArray, List.map_map, YM]
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp, rowsOf_toArray]
  have hIR : coverGS.invs.toList.map rowsOf = YI := by
    unfold YI
    rw [← hMR]
    simp only [coverGS, Array.toList_map, List.map_map]
    refine List.map_congr_left fun x hx => ?_
    simp only [Function.comp]
    exact rowsOf_invM (hEc x (Array.mem_toList_iff.1 hx))
  have hvalid : coverGS.valid = true := by
    rw [valid_eq hC, hMR, hIR]
    exact hval
  have heval : ∀ w, rowsOf (coverGS.eval w) = evalR YM YI w := fun w => by
    rw [rowsOf_eval hC, hMR, hIR]
  have eqOne : ∀ w, evalR YM YI w = oneR → coverGS.eval w = oneM := fun w e =>
    rowsOf_inj (canonB_eval _ _) canonB_oneM (by rw [heval, rowsOf_oneM]; exact e)
  have eqNeg : ∀ w, evalR YM YI w = negR → coverGS.eval w = negM := fun w e =>
    rowsOf_inj (canonB_eval _ _) canonB_negM (by rw [heval, rowsOf_negM]; exact e)
  have hS : ∀ j, (CFSG.Sporadic.Bridge.SuzGPL.Native.surjWords.getD j []) = CoverST.W.getD j [] :=
    fun j => by
      rw [surjWords_eq, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
        List.getD_eq_getElem?_getD]
  unfold coverCheck
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨⟨⟨⟨⟨⟨⟨?_, hvalid⟩, fun i hi => ?_⟩, fun w hw' => ?_⟩, eqOne _ hr3⟩, eqNeg _ hd⟩, ?_⟩, ?_⟩
  · rw [hCM]
    simp
  · rw [hCM, Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some]
    exact hcan' i hi
  · simp only [suzCover, coverWords, List.mem_append, List.mem_flatMap, List.mem_map,
      List.mem_finRange, true_and] at hw'
    rcases hw' with ⟨i, r, hr, rfl⟩ | ⟨i, rfl⟩
    · refine eval_commWord_of_central coverGS hvalid _ r ?_
      have hm : wordCodes r ∈ relCodes := R0_codes ▸ List.mem_map_of_mem hr
      have := hrel _ hm
      simp only [pmR, Bool.or_eq_true, beq_iff_eq] at this
      rcases this with e | e
      · exact Or.inl (eqOne _ e)
      · exact Or.inr (eqNeg _ e)
    · exact eqOne _ (hw i (List.mem_finRange i))
  · refine rowsOf_inj (canonB_mulM _ _) (canonB_eval _ _) ?_
    rw [rowsOf_mulM canonB_negM hA, rowsOf_negM, rowsA, heval, hS]
    exact hsA
  · refine rowsOf_inj (canonB_mulM _ _) (canonB_eval _ _) ?_
    rw [rowsOf_mulM canonB_negM hB, rowsOf_negM, rowsB, heval, hS]
    exact hsB

end CertificateChecks.KernelSuz
