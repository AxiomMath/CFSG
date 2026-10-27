module

public import CFSG.LocalAnalysis.SteinbergCCHSChecksCertificate18010Inputs
public import CFSG.Certificates.Kernel.Misc.Coset.TableFact
public import CFSG.Sporadic.Recognition.CoverRecipe
import CFSG.Certificates.Kernel.TabMatSound
import CFSG.Certificates.Kernel.Common.StrLitToList
public import Certificates.Kernel.HSCover18010.Tabs
public import Certificates.Kernel.HSCover18010.ActAll
public import Certificates.Kernel.HSCover18010.TabK
import Certificates.Kernel.HSMult.TabK

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelHS18010

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.LocalAnalysis.HigmanSimsCover CFSG.KC.MiscCoset
  CFSG.KC.StrLitToList CFSG.Certificates.CosetEnumeration

theorem finRange_three : List.finRange 3 = [0, 1, 2] := by decide

theorem relsA : rels.map encW = CFSG.KBRoute.F18010a.rels := by
  simp only [rels, parseXYT, List.map_cons, List.map_nil, strLitToList]
  decide +kernel

theorem relsB : (restrictWords (subsetOf 3 [0, 1]) rels).map encW = CFSG.KBRoute.F18010b.rels := by
  simp only [rels, parseXYT, List.map_cons, List.map_nil, strLitToList]
  decide +kernel

theorem coverC : coverWs.map encW = CFSG.KBRoute.F18010c.rels := by
  simp only [coverWs, coverWords, rels, parseXYT, finRange_three, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, pairs, strLitToList]
  decide +kernel

theorem coverD : (restrictWords (subsetOf 3 [0, 1]) coverWs).map encW =
    CFSG.KBRoute.F18010d.rels := by
  simp only [coverWs, coverWords, rels, parseXYT, finRange_three, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, pairs, strLitToList]
  decide +kernel

theorem presented_bound : Finite (PG 3 rels) ∧ Nat.card (PG 3 rels) ≤ 44352000 := by
  have ha := CFSG.KBFact.F18010a
  rw [← relsA] at ha
  have hb := CFSG.KBFact.F18010b
  rw [← relsB] at hb
  obtain ⟨f, c⟩ := TableFact.card_restrict rels (by norm_num) (subsetOf 3 [0, 1]) (by decide) ha hb
  exact ⟨f, c.trans (by norm_num)⟩

theorem cover_bound : Finite (PG 3 coverWs) ∧ Nat.card (PG 3 coverWs) ≤ 88704000 := by
  have hc := CFSG.KBFact.F18010c
  rw [← coverC] at hc
  have hd := CFSG.KBFact.F18010d
  rw [← coverD] at hd
  obtain ⟨f, c⟩ := TableFact.card_restrict coverWs (by norm_num) (subsetOf 3 [0, 1]) (by decide)
    hc hd
  exact ⟨f, c.trans (by norm_num)⟩

theorem hR : codes rels = CFSG.KHS18010.R := by
  simp only [rels, parseXYT, List.map_cons, List.map_nil, strLitToList]
  decide +kernel

theorem hW : codes ((List.finRange 3).map fun i => (i, false) :: commWords (pairs i)) ++
    codes ([] : List (List (Fin 3 × Bool))) = CFSG.KHS18010.W := by
  simp only [finRange_three, List.map_cons, List.map_nil, pairs, parseXYT, strLitToList]
  decide +kernel

theorem hC : kerWord.map letterCode = CFSG.KHS18010.C0 := by
  simp only [kerWord, parseXYT, strLitToList]
  decide +kernel

theorem kerWord_order : 2 ∣ orderOf (PresentedGroup.mk
    {r : FreeGroup (Fin 3) | r ∈ coverWs.map FreeGroup.mk} (FreeGroup.mk kerWord)) := by
  have hpt := Act.coverPointOK_sound rels (fun i => commWords (pairs i))
    ([] : List (List (Fin 3 × Bool))) hR hW (Act.coverPointOK_of_allR CFSG.KHS18010.all)
  have hc : Act.cycleOK CFSG.KHS18010.A (Nat.add 3 3) (kerWord.map letterCode) 2 = true := by
    rw [hC]
    exact CFSG.KHS18010.cyc0
  have := Act.cycleOK_sound (coverWords rels (fun i => commWords (pairs i)) ++ []) rfl
    (by norm_num) hpt kerWord hc
  rw [List.append_nil] at this
  exact this

@[expose] def hsPairs18 : List (List (Fin 3 × Bool) × List (Fin 2 × Bool)) :=
  rels.map (fun r => (r, [])) ++
    (List.finRange 3).map (fun i => (commWords (pairs i) ++ [(i, false)], [])) ++
    [(abWords.getD 0 [], [(0, false)]), (abWords.getD 1 [], [(1, false)])]

theorem hsWords_eq : hsWords = hsPairs18.map fun q => substWord genWords q.1 ++ q.2 := by
  simp [hsWords, hsPairs18, substAB, Function.comp_def]

open CFSG.Sporadic.Recognition.CoverRecipe in
theorem hG : genWords.map natWord = CFSG.KHS18010.G := by
  simp only [genWords, parseAB, List.map_cons, List.map_nil, strLitToList]
  decide +kernel

open CFSG.Sporadic.Recognition.CoverRecipe in
theorem hQ : hsPairs18.map (fun q => (natWord q.1, natWord q.2)) = CFSG.KHS18010.Q := by
  simp only [hsPairs18, rels, abWords, finRange_three, pairs, parseXYT, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append, strLitToList]
  decide +kernel

open CFSG.KC.VecK CFSG.KC.TabMat CertificateChecks.KernelVec.HS CFSG.Sporadic.HS.Native
  CertificateChecks.KernelHSMult CFSG.Sporadic.Recognition.CoverRecipe in
theorem hs_check : CFSG.Sporadic.Bridge.TwoGen.Native.vecRelCheck hsData
    (hsWords.map (List.map fun l => (l.1.val, l.2))) = true := by
  have horb : ∀ h < (hsData ()).n, orbAt (hsData ()).d (hsData ()).n NA NB Pt AT BT h = true :=
    allS_cover (S := 256) (ns := 5) (fun s hs => by
      match s, hs with
      | 0, _ => exact orb_0
      | 1, _ => exact orb_1
      | 2, _ => exact orb_2
      | 3, _ => exact orb_3
      | 4, _ => exact orb_4
      | _ + 5, h => exact absurd h (by omega)) (Nat.le_of_ble_eq_true rfl)
  have hbfs : ∀ h < (hsData ()).n, bfsAt (hsData ()).n AT BT FO h = true :=
    allS_cover (S := 256) (ns := 5) (fun s hs => by
      match s, hs with
      | 0, _ => exact bfs_0
      | 1, _ => exact bfs_1
      | 2, _ => exact bfs_2
      | 3, _ => exact bfs_3
      | 4, _ => exact bfs_4
      | _ + 5, h => exact absurd h (by omega)) (Nat.le_of_ble_eq_true rfl)
  have hsort : ∀ h < (hsData ()).n, sortAt (hsData ()).n Pt S IP SP h = true :=
    allS_cover (S := 256) (ns := 5) (fun s hs => by
      match s, hs with
      | 0, _ => exact sort_0
      | 1, _ => exact sort_1
      | 2, _ => exact sort_2
      | 3, _ => exact sort_3
      | 4, _ => exact sort_4
      | _ + 5, h => exact absurd h (by omega)) (Nat.le_of_ble_eq_true rfl)
  have hP := vpts_of hn horb hsort
  obtain ⟨ha, hb⟩ := orbit_real (hsData ()) hA hB hseed hn hP0 horb hbfs hsort
  have hai := (real_inv hP ha fun v hv => vmF_inv hAi hv).1
  have hbi := (real_inv hP hb fun v hv => vmF_inv hBi hv).1
  have hk : tabMatK (hsData ()).d NA NAi NB NBi (genWords.map natWord)
      (hsPairs18.map fun q => (natWord q.1, natWord q.2)) = true := by
    rw [hG, hQ]
    exact tabK
  have h := relCheck_of_tabMatK hP ha hai hb hbi genWords (by decide) hsPairs18 hk
  rw [← hsWords_eq] at h
  exact h

end CertificateChecks.KernelHS18010

end
