module

public import CFSG.Certificates.Kernel.EvenSporSuz.Sound
public import Certificates.Kernel.EvenSporSuz.Data

public section

namespace CertificateChecks.KernelSuz

open CFSG.KC.EvenSporSuz CFSG.KC.Str CFSG.EvenSporadicStandard.TwoSuz

theorem inputs :
    digitsK (swL 0) = true ∧ decVal (swL 0) = 4 ∧ digitsK (jwL 2) = true ∧
      decVal (jwL 2) = 2 ∧ (∀ i < 4, ((swL (i + 1)).splitOn ' ').all digitsK = true) ∧
      ((jwL 1).splitOn ' ').all digitsK = true ∧
      (∀ L ∈ [swL 5, swL 6, jwL 3, jwL 4, jwL 5, jwL 6, jwL 7, jwL 8, jwL 9, jwL 10, jwL 11],
        (L.splitOn ' ').all tokK = true) ∧ (nonEmptyLines CG.chars).length / 12 = 9 ∧
      ((cgL 7).length == 144 && (cgL 7).all (· < 3)) = true ∧
      ((cgL 8).length == 144 && (cgL 8).all (· < 3)) = true := by
  have h := inputsOK_true
  unfold inputsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9a, h9b⟩, h10a, h10b⟩ := h
  refine ⟨h1, h2, h3, h4, fun i hi => List.all_eq_true.2 (h5 i hi), List.all_eq_true.2 h6,
    fun L hL => List.all_eq_true.2 (h7 L hL), h8, ?_, ?_⟩
  · simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
    exact ⟨h9a, h9b⟩
  · simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq]
    exact ⟨h10a, h10b⟩

theorem tok {L : List Char}
    (hL : L ∈ [swL 5, swL 6, jwL 3, jwL 4, jwL 5, jwL 6, jwL 7, jwL 8, jwL 9, jwL 10, jwL 11]) :
    (L.splitOn ' ').all tokK = true :=
  inputs.2.2.2.2.2.2.1 L hL

theorem lineS (i : ℕ) : sylowLines.getD i "" = String.ofList (swL i) := by
  unfold sylowLines swL linesK
  rw [SW.eq, nl_eq, splitOn_ofList, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getD_eq_getElem?_getD]
  cases (SW.chars.splitOn '\n')[i]? <;> simp

theorem lineJ (i : ℕ) : jLines.getD i "" = String.ofList (jwL i) := by
  unfold jLines jwL linesK
  rw [JW.eq, nl_eq, splitOn_ofList, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    List.getElem?_map, List.getD_eq_getElem?_getD]
  cases (JW.chars.splitOn '\n')[i]? <;> simp

theorem ngS_eq : ngS = 4 := by
  unfold ngS sylowNat
  rw [lineS, toNat?_ofList inputs.1, Option.getD_some, inputs.2.1]

theorem nComm_eq : nComm = 2 := by
  unfold nComm
  rw [lineJ, toNat?_ofList inputs.2.2.1, Option.getD_some, inputs.2.2.2.1]

theorem sGenWords_eq :
    sGenWords = (List.range 4).map (fun i => (natsK (swL (i + 1))).map (2 * ·)) := by
  unfold sGenWords
  rw [ngS_eq]
  refine List.map_congr_left fun i hi => ?_
  rw [lineS, parseNats_ofList _ (inputs.2.2.2.2.1 i (List.mem_range.1 hi))]

theorem jWords_eq : jWords = jW := by
  unfold jWords jW jExtraWord
  rw [sGenWords_eq, lineJ, parseNats_ofList _ inputs.2.2.2.2.2.1]

theorem wx1_eq : wx1 = lettersK (swL 5) := by
  unfold wx1
  rw [ngS_eq, lineS, parseLetters_ofList _ (tok (by simp))]

theorem wx2_eq : wx2 = lettersK (swL 6) := by
  unfold wx2
  rw [ngS_eq, lineS, parseLetters_ofList _ (tok (by simp))]

theorem commU_eq {j : ℕ} (hj : j < 2) : commU j = uK j := by
  unfold commU uK
  rw [lineJ, parseLetters_ofList _ (tok (by rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp))]

theorem commV_eq {j : ℕ} (hj : j < 2) : commV j = vK j := by
  unfold commV vK
  rw [lineJ, parseLetters_ofList _ (tok (by rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;> simp))]

theorem genInComm_eq {i : ℕ} (hi : i < 5) : genInComm i = lettersK (jwL (7 + i)) := by
  unfold genInComm
  rw [nComm_eq, show 3 + 2 * 2 + i = 7 + i by omega, lineJ, parseLetters_ofList _ (tok (by
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;>
      simp))]

theorem matA_eq : matA = (cgL 7).toArray := by
  unfold matA coverMats cgL
  rw [CG.eq, parseMats_ofList, matsK_getD _ (by rw [inputs.2.2.2.2.2.2.2.1]; omega)]

theorem matB_eq : matB = (cgL 8).toArray := by
  unfold matB coverMats cgL
  rw [CG.eq, parseMats_ofList, matsK_getD _ (by rw [inputs.2.2.2.2.2.2.2.1]; omega)]

theorem hA : canonB matA = true := matA_eq ▸ canonB_toArray inputs.2.2.2.2.2.2.2.2.1

theorem hB : canonB matB = true := matB_eq ▸ canonB_toArray inputs.2.2.2.2.2.2.2.2.2

theorem rowsA : rowsOf matA = AR := by rw [matA_eq, rowsOf_toArray]; rfl

theorem rowsB : rowsOf matB = BR := by rw [matB_eq, rowsOf_toArray]; rfl

theorem abCanon : CanonGS abGS := by
  have hm : ∀ x ∈ abGS.mats, canonB x = true := by
    intro x hx
    simp only [abGS, matA2, matA3, matB2, List.mem_toArray, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    exacts [hA, canonB_mulM _ _, canonB_mulM _ _, hB, canonB_mulM _ _]
  have hi : ∀ x ∈ abGS.invs, canonB x = true := by
    intro x hx
    simp only [abGS, matA2, matA3, matB2, List.mem_toArray, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    exacts [canonB_mulM _ _, canonB_mulM _ _, hA, canonB_mulM _ _, hB]
  exact ⟨canonB_getD hm, canonB_getD hi⟩

theorem abMats : abGS.mats.toList.map rowsOf = abM := by
  simp only [abGS, matA2, matA3, matB2, List.toList_toArray, List.map_cons, List.map_nil, abM,
    rowsOf_mulM hA hA, rowsOf_mulM (canonB_mulM _ _) hA, rowsOf_mulM hB hB, rowsA, rowsB]

theorem abInvs : abGS.invs.toList.map rowsOf = abI := by
  simp only [abGS, matA2, matA3, matB2, List.toList_toArray, List.map_cons, List.map_nil, abI,
    rowsOf_mulM hA hA, rowsOf_mulM (canonB_mulM _ _) hA, rowsOf_mulM hB hB, rowsA, rowsB]

theorem jMatsCanon : ∀ x ∈ jMats, canonB x = true := by
  intro x hx
  simp only [jMats, List.mem_toArray, List.mem_map] at hx
  obtain ⟨w, -, rfl⟩ := hx
  exact canonB_eval _ _

theorem jCanon : CanonGS jGS := by
  refine ⟨canonB_getD jMatsCanon, canonB_getD fun x hx => ?_⟩
  simp only [jGS, Array.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact canonB_invM' _

theorem jMatsRows : jMats.toList.map rowsOf = jM := by
  unfold jMats jM
  rw [List.toList_toArray, List.map_map, jWords_eq]
  refine List.map_congr_left fun w _ => ?_
  simp only [Function.comp]
  rw [rowsOf_eval abCanon, abMats, abInvs]

theorem jGSMats : jGS.mats.toList.map rowsOf = jM := jMatsRows

theorem jGSInvs : jGS.invs.toList.map rowsOf = jI := by
  unfold jI
  rw [← jMatsRows, List.map_map]
  simp only [jGS, Array.toList_map, List.map_map]
  refine List.map_congr_left fun x hx => ?_
  simp only [Function.comp]
  exact rowsOf_invM' (jMatsCanon x (Array.mem_toList_iff.1 hx))

theorem cCanon : CanonGS cGS := by
  refine ⟨canonB_getD fun x hx => ?_, canonB_getD fun x hx => ?_⟩
  · simp only [cGS, List.mem_toArray, List.mem_map] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact canonB_eval _ _
  · simp only [cGS, List.mem_toArray, List.mem_map] at hx
    obtain ⟨j, -, rfl⟩ := hx
    exact canonB_eval _ _

theorem cMats : cGS.mats.toList.map rowsOf = cM := by
  simp only [cGS, cM, nComm_eq, List.toList_toArray, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.1 hj
  simp only [Function.comp, commM]
  rw [rowsOf_eval jCanon, jGSMats, jGSInvs, commU_eq hj, commV_eq hj]

theorem cInvs : cGS.invs.toList.map rowsOf = cI := by
  simp only [cGS, cI, nComm_eq, List.toList_toArray, List.map_map]
  refine List.map_congr_left fun j hj => ?_
  have hj := List.mem_range.1 hj
  simp only [Function.comp, commInvM]
  rw [rowsOf_eval jCanon, jGSMats, jGSInvs, commU_eq hj, commV_eq hj]

theorem x1Rows : rowsOf x1M = x1R := by
  unfold x1M x1R
  rw [rowsOf_eval jCanon, jGSMats, jGSInvs, wx1_eq]

theorem x2Rows : rowsOf x2M = x2R := by
  unfold x2M x2R
  rw [rowsOf_eval jCanon, jGSMats, jGSInvs, wx2_eq]

theorem jCheck_true : jCheck = true := by
  have hK := jCheckK_true
  unfold jCheckK at hK
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at hK
  obtain ⟨⟨⟨⟨hab, hj⟩, hc⟩, hgen⟩, hcomm⟩ := hK
  unfold jCheck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq]
  have hx1 : canonB x1M = true := canonB_eval _ _
  have hx2 : canonB x2M = true := canonB_eval _ _
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, nComm_eq⟩, ngS_eq⟩, fun i hi => ?_⟩, fun i hi => ?_⟩
  · rw [valid_eq abCanon, abMats, abInvs]
    exact hab
  · rw [valid_eq jCanon, jGSMats, jGSInvs]
    exact hj
  · rw [valid_eq cCanon, cMats, cInvs]
    exact hc
  · apply rowsOf_inj (canonB_eval _ _) (canonB_getD jMatsCanon i)
    rw [rowsOf_eval cCanon, cMats, cInvs, genInComm_eq hi, rowsOf_getD, jMatsRows]
    exact hgen i hi
  · obtain ⟨h1, h2⟩ := hcomm i hi
    have hg := canonB_getD jMatsCanon i
    refine ⟨rowsOf_inj (canonB_mulM _ _) (canonB_mulM _ _) ?_,
      rowsOf_inj (canonB_mulM _ _) (canonB_mulM _ _) ?_⟩
    · rw [rowsOf_mulM hg hx1, rowsOf_mulM hx1 hg, rowsOf_getD, jMatsRows, x1Rows]
      exact h1
    · rw [rowsOf_mulM hg hx2, rowsOf_mulM hx2 hg, rowsOf_getD, jMatsRows, x2Rows]
      exact h2

end CertificateChecks.KernelSuz
