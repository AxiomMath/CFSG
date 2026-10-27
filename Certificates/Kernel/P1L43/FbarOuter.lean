module

public import Certificates.Kernel.P1L43.FbarGlue
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.K442264

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.U43Case
open CertificateChecks.KernelP1L43 CFSG.ComponentClassification.HarrisLit.P1.L43
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native CFSG.KC.Misc.ArrEnum
open CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.HarrisLit.P1
open Certificates.Asc82Fbar CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Co2.Native

theorem rho_mem {x : Table} (hx : x ∈ fbarRho ()) :
    ∃ c < 81, x = (fbarRho ()).getD c (idT 80) := by
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hx
  have h81 : (fbarRho ()).length = 81 := by simp [fbarRho]
  exact ⟨c, h81 ▸ hc, by rw [List.getD_eq_getElem _ _ hc]⟩

theorem rho_none {c : Nat} (hc : c < 81) (h : rhoPairs.lookup c = none) :
    (fbarRho ()).getD c (idT 80) = idT 80 := by
  unfold fbarRho
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hc]
  simp [h]

theorem pocket_true : pocketOK 80 100000 [tm 18085123, tm 27169507] (tm 38855539) (fbarRho ()) =
    true := by
  obtain ⟨-, hcM, hhM, hGM, hgjM, hcnM⟩ := rec_facts fb442headM
  obtain ⟨-, hcK, hhK, hGK, hgjK, hcnK⟩ := rec_facts fb442headK
  obtain ⟨-, -, -, -, b5, b6, -, -, -, -, -, -, -, b14⟩ := fb442binds
  have hi := fb442innK
  unfold fb442inn at hi
  simp only [bAnd_iff] at hi
  have cF : ∀ j < 10, Cn 80 7 (FB j) := fun j hj => allN_spec hi.1 j hj
  have ho := fb442outK
  unfold fb442out at ho
  simp only [bAnd_iff] at ho
  obtain ⟨-, -, -, -, -, o6, o7, o8, o9, o10⟩ := ho
  have hpM : ∀ i < FM.cnt, penumPtK 80 7 (mask 7) (80 * 7) true FM.G FM.GI 2 FM.cnt FM.T FM.PL
      FM.POS FM.SRT FM.SRI i = true :=
    peAll (L := 96) (K := 3) (by norm_num) (by omega) fun q hq => by
      interval_cases q
      exacts [fb442peM0, fb442peM1, fb442peM2]
  have hsM : ∀ i < FM.cnt, hsortPtK 80 7 (mask 7) FM.cnt FM.T FM.HS FM.HSI i = true :=
    slAll (L := 288) (K := 1) (by norm_num) (by omega) fun q hq => by
      interval_cases q
      exact fb442hsM0
  have hpK : ∀ i < FK.cnt, penumPtK 80 7 (mask 7) (80 * 7) true FK.G FK.GI 24 FK.cnt FK.T FK.PL
      FK.POS FK.SRT FK.SRI i = true :=
    peAll (L := 24) (K := 1) (by norm_num) (by omega) fun q hq => by
      interval_cases q
      exact fb442peK0
  have hsK : ∀ i < FK.cnt, hsortPtK 80 7 (mask 7) FK.cnt FK.T FK.HS FK.HSI i = true :=
    slAll (L := 24) (K := 1) (by norm_num) (by omega) fun q hq => by
      interval_cases q
      exact fb442hsK0
  have hclK : ∀ c < Nat.mul FK.cnt 48, findPtK FK.cnt FK.T
      (prodQK 80 7 (mask 7) 48 FK.T (bothK 24 FK.GI FKI)) FKCl c = true :=
    slAll (L := 288) (K := 4) (by norm_num) (hcK ▸ (by decide : Nat.mul 24 48 ≤ 288 * 4))
      fun q hq => by
        interval_cases q
        exacts [fb442clK0, fb442clK1, fb442clK2, fb442clK3]
  have tM : TabsOK 80 7 2 FM.GI [tm 18085123, tm 27169507].toArray :=
    tabs2 (tab_of b5) (tab_of b6) hcnM
  have hmM := (mulH_sound fb442sz hGM tM hhM hpM hsM).1
  have tK : TabsOK 80 7 24 FK.GI ((slList ()).map (rhoT 80 (fbarRho ()))).toArray := by
    rw [kl_eq]
    refine ⟨by simp [fb442cdL], fun j hj => ⟨?_, hcnK j hj⟩⟩
    rw [getElem!_pos _ j (by simpa [fb442cdL] using hj)]
    simp only [List.getElem_toArray, List.getElem_map]
    have e : fb442cdL[j]'(by simpa [fb442cdL] using hj) = fb442cd j := by
      unfold fb442cd
      rw [List.getD_eq_getElem]
    rw [e]
    exact rho_cd hj
  unfold pocketOK
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨by simp [fbarRho], ?_, ?_, ?_, ?_, ?_, enumOK_of fb442sz hGK tK hgjK hhK hpK hsK hclK hcK,
    normOK_of fb442sz hGK tK hhK hpK hsK tM hgjM fun c hc => slK_spec o10 c (Nat.zero_le _)
      (by rw [hcK] at hc; omega) hc⟩
  · rw [List.all_eq_true]
    intro x hx
    obtain ⟨c, hc, rfl⟩ := rho_mem hx
    have hr := List.all_eq_true.1 fb442rho c (List.mem_range.2 hc)
    cases hl : rhoPairs.lookup c
    · rw [rho_none hc hl, idT_tb fb442sz]
      exact perm_tb fb442idK
    · rw [hl] at hr
      simp only [Option.isNone_some, Bool.false_or, List.contains_iff_mem] at hr
      obtain ⟨j, hj, e⟩ := List.getElem_of_mem hr
      have e' : c = fb442cd j := by
        rw [← e]
        unfold fb442cd
        rw [List.getD_eq_getElem _ _ hj]
      rw [e', rho_cd hj]
      exact permOK_unpack (hcnK j hj) (hgjK j hj).1
  · rw [List.all_eq_true]
    intro A hA
    rw [List.all_eq_true]
    intro B hB
    obtain ⟨i, hi, ei⟩ := cd_of_mem hA
    obtain ⟨j, hj, ej⟩ := cd_of_mem hB
    have hm := allN_spec (allN_spec o6 i hi) j hj
    rw [strictB_eq''] at hm
    simp only [bAnd_iff] at hm
    obtain ⟨m1, m3, m4⟩ := hm
    have hm' : r32 FKT (Nat.add (Nat.mul 24 i) j) < 24 := Nat.le_of_ble_eq_true m1
    rw [rhoT_of hi ei, rhoT_of hj ej, rhoT_of hm' (by
        rw [slCode_mul, ei, ej]
        exact (Nat.eq_of_beq_eq_true m4).symm),
      compT_tb (hcnK i hi) (hcnK j hj),
      tblEq_tb (cn_pp (hcnK i hi) (hcnK j hj)) (hcnK _ hm')]
    exact m3
  · rw [List.all_eq_true]
    intro A hA
    obtain ⟨i, hi, ei⟩ := cd_of_mem hA
    rw [rhoT_of hi ei, idT_tb fb442sz, tblEq_tb (hcnK i hi) (cn_id fb442sz)]
    have ht := allN_spec o7 i hi
    cases hb : Nat.beq (FK.GI i) (pidn 80 7)
    · rfl
    · rw [hb] at ht
      change Nat.beq (fb442cd i) 28 = true at ht
      rw [Bool.not_true, Bool.false_or]
      exact decide_eq_true (eq_one_of_slCode (ei.trans (Nat.eq_of_beq_eq_true ht)))
  · have h56 : 56 ∈ (slList ()).map slCode := by
      rw [p_codes]
      decide
    obtain ⟨A, hA, eA⟩ := List.mem_map.1 h56
    rw [List.any_eq_true]
    refine ⟨A, hA, ?_⟩
    rw [rhoT_of (j := 15) (by norm_num) (by rw [eA]; rfl), Nat.eq_of_beq_eq_true o8, tab_of b14]
    exact tblEq_self (cF 9 (by norm_num))
  · rw [hmM, kl_eq, List.all_eq_true]
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hc
    have e' : c = fb442cd j := by
      rw [← e]
      unfold fb442cd
      rw [List.getD_eq_getElem _ _ hj]
    rw [e', rho_cd hj]
    exact memT_rec (Q := FK.GI) (POS := FMx) (j := j) (hcnK j hj) rfl (allN_spec o9 j hj)

theorem outer_eq : outerOK 80 100000 l43Sift l43Runs (tm 28947042) (tm 5634355) (fbarOuter ()) =
    (enumOK 80 100000 360 [tm 28947042, tm 5634355] &&
      CFSG.Sporadic.SmallOddCore.permOK 80 (tm 19250485) && involOK 80 (tm 19250485) &&
      memT 80 (mulClosureH 80 [tm 28947042, tm 5634355].toArray 100000).1 (tm 19250485) &&
      allInvConj 80 (mulClosureH 80 [tm 28947042, tm 5634355].toArray 100000).1 (tm 19250485) &&
      CFSG.Sporadic.SmallOddCore.permOK 80 (tm 31901178) && l43Sift (tm 31901178) &&
      tblEq 80 (compT 80 (tm 31901178) (tm 38855539)) (compT 80 (tm 19250485) (tm 31901178)) &&
      pocketOK 80 100000 [tm 18085123, tm 27169507] (tm 38855539) (fbarRho ())) := rfl

theorem outer_true : outerOK 80 100000 l43Sift l43Runs (tm 28947042) (tm 5634355) (fbarOuter ()) =
    true := by
  obtain ⟨-, hcO, hhO, hGO, hgjO, hcnO⟩ := rec_facts fb442headO
  obtain ⟨-, -, b3, b4, -, -, -, -, -, -, -, b12, b13, b14⟩ := fb442binds
  have eB := tab_of b12
  have eC := tab_of b13
  have eT := tab_of b14
  have hi := fb442innK
  unfold fb442inn at hi
  simp only [bAnd_iff] at hi
  have cF : ∀ j < 10, Cn 80 7 (FB j) := fun j hj => allN_spec hi.1 j hj
  have cB := cF 6 (by norm_num)
  have cC := cF 7 (by norm_num)
  have cT := cF 9 (by norm_num)
  have ho := fb442outK
  unfold fb442out at ho
  simp only [bAnd_iff] at ho
  obtain ⟨o1, o2, o3, o4, o5, -⟩ := ho
  have hpO : ∀ i < FO.cnt, penumPtK 80 7 (mask 7) (80 * 7) true FO.G FO.GI 2 FO.cnt FO.T FO.PL
      FO.POS FO.SRT FO.SRI i = true :=
    peAll (L := 120) (K := 3) (by norm_num) (by omega) fun q hq => by
      interval_cases q
      exacts [fb442peO0, fb442peO1, fb442peO2]
  have hsO : ∀ i < FO.cnt, hsortPtK 80 7 (mask 7) FO.cnt FO.T FO.HS FO.HSI i = true :=
    slAll (L := 360) (K := 1) (by norm_num) (by omega) fun q hq => by
      interval_cases q
      exact fb442hsO0
  have hclO : ∀ c < Nat.mul FO.cnt 4, findPtK FO.cnt FO.T
      (prodQK 80 7 (mask 7) 4 FO.T (bothK 2 FO.GI FOI)) FOCl c = true :=
    slAll (L := 360) (K := 4) (by norm_num) (hcO ▸ (by decide : Nat.mul 360 4 ≤ 360 * 4))
      fun q hq => by
        interval_cases q
        exacts [fb442clO0, fb442clO1, fb442clO2, fb442clO3]
  have hTO : ∀ i < FO.cnt, Cn 80 7 (FO.T i) := fun i hi => penumPt_canon (hpO i hi)
  have tO : TabsOK 80 7 2 FO.GI [tm 28947042, tm 5634355].toArray :=
    tabs2 (tab_of b3) (tab_of b4) hcnO
  have hmO := (mulH_sound fb442sz hGO tO hhO hpO hsO).1
  rw [outer_eq, hmO]
  simp only [Bool.and_eq_true, and_assoc]
  refine ⟨enumOK_of fb442sz hGO tO hgjO hhO hpO hsO hclO hcO, ?_, ?_, ?_, ?_, ?_,
    sift_of' _ fb442sift.2, ?_, pocket_true⟩
  · rw [eB]
    exact perm_tb o1
  · rw [eB]
    exact invol_tb cB o2
  · rw [eB]
    exact memT_rec (Q := fun _ => FB 6) (POS := FOx) (j := 0) cB rfl o3
  · rw [eB]
    exact allInvConj_of hTO cB (slAll (L := 360) (K := 1) (by norm_num) (by omega) fun q hq => by
      interval_cases q
      exact fb442wtO0)
  · rw [eC]
    exact perm_tb o4
  · rw [eC, eT, eB, compT_tb cC cT, compT_tb cB cC, tblEq_tb (cn_pp cC cT) (cn_pp cB cC)]
    exact o5

end CertificateChecks.K442264

end
