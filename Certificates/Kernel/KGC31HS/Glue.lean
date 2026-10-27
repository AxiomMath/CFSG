module

public import Certificates.Kernel.KGC31HS.Small
public import Certificates.Kernel.KGC31HS.Cls
public import Certificates.Kernel.HS100.Five
public import Certificates.Kernel.HS100.Chain
public import Certificates.Kernel.LocalQT.He4148.Glue
public import Certificates.Kernel.LocalComp.ExcGlue
public import CFSG.Certificates.Kernel.KGC31PSound
public import CFSG.Certificates.Kernel.KGC31PBSound
public import CFSG.Certificates.Kernel.Child3Reps
public import CFSG.Certificates.Kernel.SporSch.ChainKElem
public import CFSG.Certificates.Kernel.SporSch.CodesImg
public import CFSG.Certificates.Kernel.SporSch.ConjClosureSpec
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.HeModelKSound
public import CFSG.Certificates.Kernel.HexaKSound
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31HS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3 CFSG.KC.BfsPin
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.HS
open CFSG.KS.SporSch.MOC CFSG.Monster.B.Mathieu CFSG.Certificates CertificateChecks.KernelHS100
open CFSG.KS.KeyBfs CFSG.ComponentClassification.J2Cover

theorem hsz : szOK 100 7 = true := hw

theorem and_split {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true :=
  Bool.and_eq_true_iff.1 h

theorem kInvP : invEqK 100 7 (mask 7) (100 * 7) (HP.F 0) (pinvS 100 7 (mask 7) (HP.F 0)) = true ∧
    invEqK 100 7 (mask 7) (100 * 7) (pinvS 100 7 (mask 7) (HP.F 0)) (HP.F 0) = true ∧
    invEqK 100 7 (mask 7) (100 * 7) (HP.F 1) (pinvS 100 7 (mask 7) (HP.F 1)) = true ∧
    invEqK 100 7 (mask 7) (100 * 7) (pinvS 100 7 (mask 7) (HP.F 1)) (HP.F 1) = true ∧
    invEqK 100 7 (mask 7) (100 * 7) (FV.F 2) (pinvS 100 7 (mask 7) (FV.F 2)) = true ∧
    invEqK 100 7 (mask 7) (100 * 7) (pinvS 100 7 (mask 7) (FV.F 2)) (FV.F 2) = true ∧
    invEqK 100 7 (mask 7) (100 * 7) (FV.F 4) (pinvS 100 7 (mask 7) (FV.F 4)) = true ∧
    invEqK 100 7 (mask 7) (100 * 7) (pinvS 100 7 (mask 7) (FV.F 4)) (FV.F 4) = true ∧
    invEqK 100 7 (mask 7) (100 * 7) (FV.F 25) (pinvS 100 7 (mask 7) (FV.F 25)) = true ∧
    invEqK 100 7 (mask 7) (100 * 7) (pinvS 100 7 (mask 7) (FV.F 25)) (FV.F 25) = true := by
  have h := kInv
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, i⟩, j⟩, k⟩ := h
  exact ⟨a, b, c, d, e, f, g, i, j, k⟩

theorem arr0 : CFSG.RankThree.Native.hs100Arr 0 = unpack 100 7 (HP.F 0) := hs100Arr_eq 0 (by norm_num)
theorem arr1 : CFSG.RankThree.Native.hs100Arr 1 = unpack 100 7 (HP.F 1) := hs100Arr_eq 1 (by norm_num)
theorem line0 : CFSG.RankThree.Native.hs100FiveLines[0]! = unpack 100 7 (FV.F 2) :=
  fiveLine_eq (j := 0) (by norm_num)
theorem line2 : CFSG.RankThree.Native.hs100FiveLines[2]! = unpack 100 7 (FV.F 4) :=
  fiveLine_eq (j := 2) (by norm_num)
theorem line23 : CFSG.RankThree.Native.hs100FiveLines[23]! = unpack 100 7 (FV.F 25) :=
  fiveLine_eq (j := 23) (by norm_num)

open CertificateChecks.KernelLQT.He4148 (unpack_facts imageList_of_rep unpack_size') in
theorem img_of {t : Array Nat} {P : Nat} (ht : t = unpack 100 7 P)
    (h1 : invEqK 100 7 (mask 7) (100 * 7) P (pinvS 100 7 (mask 7) P) = true)
    (h2 : invEqK 100 7 (mask 7) (100 * 7) (pinvS 100 7 (mask 7) P) P = true) :
    imageList (CFSG.Sporadic.HeldB.permOrId 100 t) = (unpack 100 7 P).toList :=
  imageList_of_rep (unpack_size' _ _ _) (unpack_facts ht h1 h2).2.1

open CertificateChecks.KernelLQT.He4148 (unpack_facts) in
theorem permOK_of {t : Array Nat} {P : Nat} (ht : t = unpack 100 7 P)
    (h1 : invEqK 100 7 (mask 7) (100 * 7) P (pinvS 100 7 (mask 7) P) = true)
    (h2 : invEqK 100 7 (mask 7) (100 * 7) (pinvS 100 7 (mask 7) P) P = true) :
    CFSG.Quasithin.KGC31.HS.permOK t = true :=
  (unpack_facts ht h1 h2).1

theorem ppOf {P : Nat} (h1 : invEqK 100 7 (mask 7) (100 * 7) P (pinvS 100 7 (mask 7) P) = true) :
    PP 100 7 P := PP_of_permOK hsz h1

theorem imgA : imageList permA = (unpack 100 7 (HP.F 0)).toList :=
  img_of arr0 kInvP.1 kInvP.2.1

theorem imgB : imageList permB = (unpack 100 7 (HP.F 1)).toList :=
  img_of arr1 kInvP.2.2.1 kInvP.2.2.2.1

theorem ppA : PP 100 7 (HP.F 0) := ppOf kInvP.1
theorem ppB : PP 100 7 (HP.F 1) := ppOf kInvP.2.2.1
theorem ppL0 : PP 100 7 (FV.F 2) := ppOf kInvP.2.2.2.2.1
theorem ppL2 : PP 100 7 (FV.F 4) := ppOf kInvP.2.2.2.2.2.2.1
theorem ppL23 : PP 100 7 (FV.F 25) := ppOf kInvP.2.2.2.2.2.2.2.2.1

theorem ppG (l : Int) : PP 100 7 (G l) := by
  unfold G
  split
  · exact ppA
  · exact ppB

theorem aT_eq : aT = tabP 100 7 (HP.F 0) := CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img imgA
theorem bT_eq : bT = tabP 100 7 (HP.F 1) := CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img imgB

theorem gensT_eq (l : Int) : gensT l = tabP 100 7 (G l) := by
  unfold gensT G
  split
  · exact aT_eq
  · exact bT_eq

theorem wT (wd : List Int) : wordT 100 gensT wd = tabP 100 7 (pw wd) :=
  wordT_tabP hsz gensT_eq ppG wd

theorem ppw' (wd : List Int) : PP 100 7 (pw wd) := PP_pword hsz ppG wd

theorem ppL (ws : List (List Int)) : ∀ b ∈ ws.map pw, PP 100 7 b := by
  intro b hb
  obtain ⟨wd, -, rfl⟩ := List.mem_map.1 hb
  exact ppw' wd

theorem mapW (ws : List (List Int)) : ws.map (wordT 100 gensT) = (ws.map pw).map (tabP 100 7) := by
  rw [List.map_map]
  exact List.map_congr_left fun wd _ => wT wd

theorem lineT_eq0 : lineT 0 = tabP 100 7 (FV.F 2) :=
  CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img (img_of line0 kInvP.2.2.2.2.1 kInvP.2.2.2.2.2.1)
theorem lineT_eq2 : lineT 2 = tabP 100 7 (FV.F 4) :=
  CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img
    (img_of line2 kInvP.2.2.2.2.2.2.1 kInvP.2.2.2.2.2.2.2.1)
theorem lineT_eq23 : lineT 23 = tabP 100 7 (FV.F 25) :=
  CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img
    (img_of line23 kInvP.2.2.2.2.2.2.2.2.1 kInvP.2.2.2.2.2.2.2.2.2)

theorem repG (l : Int) : Rep 100 (gensT l) (gensG l) := by
  unfold gensT gensG
  split
  · exact rep_toTable (by norm_num) _
  · exact rep_toTable (by norm_num) _

theorem imgW (wd : List Int) : imageList (wordG gensG wd) = (unpack 100 7 (pw wd)).toList := by
  refine imageList_of_rep (ppw' wd).1 ?_
  rw [← wT]
  exact Rep.wordT (by norm_num) wd fun l _ => repG l

theorem tab_img (w : List Int) :
    imageList (tab (wordG gensG w)) = (unpack 100 7 (pw w)).toList := by
  rw [tab_eq]
  exact imgW w

theorem toTable_tab (w : List Int) : toTable (tab (wordG gensG w)) = tabP 100 7 (pw w) :=
  CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img (tab_img w)

private theorem arr2_get0 {α} [Inhabited α] (a b : α) : #[a, b][0]! = a := rfl
private theorem arr2_get1 {α} [Inhabited α] (a b : α) : #[a, b][1]! = b := rfl

theorem gens_bind : genArr.size = 2 ∧ genInvArr.size = 2 ∧
    ∀ l < 2, genArr[l]! = arrTable 100 (unpack 100 7 (RH.GP l)) ∧
      genInvArr[l]! = arrTable 100 (unpack 100 7 (RH.GIP l)) := by
  have h := kGP
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨g0, g1⟩, i0⟩, i1⟩ := h
  refine ⟨rfl, rfl, fun l hl => ?_⟩
  interval_cases l
  · refine ⟨?_, ?_⟩
    · rw [genArr, arr2_get0, Nat.eq_of_beq_eq_true g0]
      exact aT_eq
    · rw [genInvArr, arr2_get0, Nat.eq_of_beq_eq_true i0, aT_eq, invT_tabP ppA]
      rfl
  · refine ⟨?_, ?_⟩
    · rw [genArr, arr2_get1, Nat.eq_of_beq_eq_true g1]
      exact bT_eq
    · rw [genInvArr, arr2_get1, Nat.eq_of_beq_eq_true i1, bT_eq, invT_tabP ppB]
      rfl

theorem gens_canon : ∀ l < 2, canonK 100 7 (mask 7) (100 * 7) (RH.GP l) = true ∧
    canonK 100 7 (mask 7) (100 * 7) (RH.GIP l) = true := by
  have h := kGc
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  intro l hl
  interval_cases l
  · exact ⟨a, b⟩
  · exact ⟨c, d⟩

theorem cs_pos : ∀ c ∈ RH.CS, 0 < c := by
  rw [kCS]
  decide

#kc_forall_chunks clsAll (fun k => clsBlk k = true) 22 CertificateChecks.KernelKGC31HS.clsBlk 1

theorem of_blocks {f : Nat → Bool}
    (hb : ∀ k < 22, (List.range' (1000 * k) (min 1000 (RH.N - 1000 * k))).all f = true) :
    ∀ j < RH.N, f j = true := by
  intro j hj
  have hN := Nat.eq_of_beq_eq_true kN
  have hk : j / 1000 < 22 := by omega
  apply List.all_eq_true.1 (hb (j / 1000) hk) j
  rw [List.mem_range'_1]
  omega

theorem repK_all : ∀ j < RH.N,
    repK 100 7 RH.GP RH.GIP 2 RH.CS RH.OFF RH.CI RH.E RH.P RH.L RH.K RH.S RH.SI RH.N 20000 j = true :=
  of_blocks fun k hk => clsAll k hk

theorem replayH {i : Nat} (hi : i < RH.CS.length) :
    KReplay 100 (fun l y => conjT 100 genArr[l]! genInvArr[l]! y) genArr.size
      (tabP 100 7 (RH.E (lget RH.OFF i))) (lget RH.CS i) (fun k => tabP 100 7 (RH.E (lget RH.OFF i + k)))
      (fun k => if k = 0 then 0 else RH.P (lget RH.OFF i + k))
      (fun k => if k = 0 then 0 else RH.L (lget RH.OFF i + k))
      (fun h l => RH.K (2 * (lget RH.OFF i + h) + l)) :=
  replay_class gens_bind gens_canon kOff repK_all cs_pos hi

theorem lget_CS0 : lget RH.CS 0 = 5775 := by rw [kCS]; rfl
theorem lget_CS1 : lget RH.CS 1 = 15400 := by rw [kCS]; rfl
theorem lget_OFF0 : lget RH.OFF 0 = 0 := by rw [kOff0]; rfl
theorem lget_OFF1 : lget RH.OFF 1 = 5775 := by rw [kOff0]; rfl

theorem b0T_eq : b0T = tabP 100 7 (RH.E (lget RH.OFF 0)) := by
  have h := kRep
  rw [Bool.and_eq_true] at h
  rw [lget_OFF0, Nat.eq_of_beq_eq_true h.1]
  exact aT_eq

theorem rBT_eq : rBT = tabP 100 7 (RH.E (lget RH.OFF 1)) := by
  have h := kRep
  rw [Bool.and_eq_true] at h
  rw [lget_OFF1, Nat.eq_of_beq_eq_true h.2]
  exact wT wB

theorem closure_eq {i cap : Nat} (hi : i < RH.CS.length) (hcap : lget RH.CS i ≤ cap) :
    conjClosure 100 genArr genInvArr (tabP 100 7 (RH.E (lget RH.OFF i))) cap =
      (Array.ofFn (n := lget RH.CS i) fun k => tabP 100 7 (RH.E (lget RH.OFF i + k.val)),
        Array.ofFn (n := lget RH.CS i) fun k => if k.val = 0 then 0 else RH.P (lget RH.OFF i + k.val),
        Array.ofFn (n := lget RH.CS i) fun k => if k.val = 0 then 0 else RH.L (lget RH.OFF i + k.val)) := by
  have R := replayH hi
  generalize genArr = G at R ⊢
  generalize genInvArr = GI at R ⊢
  rw [conjClosure_eq, keyBfs_replay R hcap]

theorem tree_rec {i : Nat} (hi : i < RH.CS.length) :
    conjTreeOK 100 genArr genInvArr (tabP 100 7 (RH.E (lget RH.OFF i)))
      (Array.ofFn (n := lget RH.CS i) fun k => tabP 100 7 (RH.E (lget RH.OFF i + k.val)))
      (Array.ofFn (n := lget RH.CS i) fun k => if k.val = 0 then 0 else RH.P (lget RH.OFF i + k.val))
      (Array.ofFn (n := lget RH.CS i) fun k => if k.val = 0 then 0 else RH.L (lget RH.OFF i + k.val)) =
      true := by
  have R := replayH hi
  generalize genArr = G at R ⊢
  generalize genInvArr = GI at R ⊢
  have h := conjTreeOK_of R
  convert h using 3

theorem clA_eq : clA = (Array.ofFn (n := lget RH.CS 0) fun k => tabP 100 7 (RH.E (lget RH.OFF 0 + k.val)),
    Array.ofFn (n := lget RH.CS 0) fun k => if k.val = 0 then 0 else RH.P (lget RH.OFF 0 + k.val),
    Array.ofFn (n := lget RH.CS 0) fun k => if k.val = 0 then 0 else RH.L (lget RH.OFF 0 + k.val)) := by
  have h := closure_eq (i := 0) (cap := 5775) (by rw [kCS]; decide) (le_of_eq lget_CS0)
  rw [← b0T_eq] at h
  unfold clA
  exact h

theorem clB_eq : clB = (Array.ofFn (n := lget RH.CS 1) fun k => tabP 100 7 (RH.E (lget RH.OFF 1 + k.val)),
    Array.ofFn (n := lget RH.CS 1) fun k => if k.val = 0 then 0 else RH.P (lget RH.OFF 1 + k.val),
    Array.ofFn (n := lget RH.CS 1) fun k => if k.val = 0 then 0 else RH.L (lget RH.OFF 1 + k.val)) := by
  have h := closure_eq (i := 1) (cap := 15400) (by rw [kCS]; decide) (le_of_eq lget_CS1)
  rw [← rBT_eq] at h
  unfold clB
  exact h

theorem mem_invs : ∀ t ∈ invs, ∃ j < RH.N, t = tabP 100 7 (RH.E j) := by
  have hcl : ∀ i (hi : i < RH.CS.length) (cap : Nat), lget RH.CS i ≤ cap →
      ∀ t ∈ (conjClosure 100 genArr genInvArr (tabP 100 7 (RH.E (lget RH.OFF i))) cap).1.toList,
        ∃ j < RH.N, t = tabP 100 7 (RH.E j) := by
    intro i hi cap hcap t ht
    rw [closure_eq hi hcap] at ht
    simp only [Array.toList_ofFn, List.mem_ofFn] at ht
    obtain ⟨k, rfl⟩ := ht
    exact ⟨lget RH.OFF i + k, (ci_eq kOff repK_all hi k.isLt).1, rfl⟩
  intro t ht
  rw [invs, List.mem_append] at ht
  rcases ht with ht | ht
  · unfold clA at ht
    rw [b0T_eq] at ht
    exact hcl 0 (by rw [kCS]; decide) 5775 (by rw [lget_CS0]) t ht
  · unfold clB at ht
    rw [rBT_eq] at ht
    exact hcl 1 (by rw [kCS]; decide) 15400 (by rw [lget_CS1]) t ht

theorem gens_img {ws : List (List Int)} {S : Nat → Nat} {m : Nat} (hl : ws.length = m)
    (h : (List.range m).all (fun j => Nat.beq (S j) (pw (ws.getD j []))) = true) :
    ∀ j < (ws.map fun w => tab (wordG gensG w)).length,
      imageList ((ws.map fun w => tab (wordG gensG w)).getD j 1) = (unpack 100 7 (S j)).toList := by
  intro j hj
  have hj' : j < ws.length := by simpa using hj
  rw [List.getD_eq_getElem _ _ hj, List.getElem_map, tab_img, ← List.getD_eq_getElem _ [] hj',
    Nat.eq_of_beq_eq_true (List.all_eq_true.1 h j (List.mem_range.2 (hl ▸ hj')))]

theorem kGensP : (List.range 2).all (fun j => Nat.beq (CCA.S j) (pw (caGenW.getD j []))) = true ∧
    (List.range 3).all (fun j => Nat.beq (CCR.S j) (pw (crGenW.getD j []))) = true ∧
    (List.range 3).all (fun j => Nat.beq (CT0.S j) (pw (t0GenW.getD j []))) = true ∧
    (List.range 2).all (fun j => Nat.beq (CM16.S j) (pw (m16GenW.getD j []))) = true ∧
    (List.range 2).all (fun j => Nat.beq (CN8.S j) (pw (n8GenW.getD j []))) = true ∧
    (List.range 3).all (fun j => Nat.beq (CQ.S j) (pw (qGenW.getD j []))) = true := by
  have h := kGens
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := h
  exact ⟨a, b, c, d, e, f⟩

theorem kOrdP : ordK CCA.LR 3 = 7680 ∧ ordK CCR.LR 4 = 2880 ∧ ordK CT0.LR 2 = 512 ∧
    ordK CM16.LR 4 = 5760 ∧ ordK CN8.LR 3 = 10752 ∧ ordK CQ.LR 1 = 64 := by
  have h := kOrdC
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := h
  exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c,
    Nat.eq_of_beq_eq_true d, Nat.eq_of_beq_eq_true e, Nat.eq_of_beq_eq_true f⟩

theorem chainCA : ChainK 100 7 (permsOf caGenW) caChainW (#v[0, 2, 3] : Vector (Fin 100) 3)
    CCA.S CCA.SI CCA.LR CCA.TR CCA.TRI 6 CCA.BP 1 100 :=
  ⟨by norm_num, by norm_num, by norm_num, gens_img rfl kGensP.1, by decide, CCA.head,
    CCA.hl, by norm_num, CCA.hs⟩

theorem chainCR : ChainK 100 7 (permsOf crGenW) crChainW (#v[0, 1, 2, 3] : Vector (Fin 100) 4)
    CCR.S CCR.SI CCR.LR CCR.TR CCR.TRI 7 CCR.BP 1 100 :=
  ⟨by norm_num, by norm_num, by norm_num, gens_img rfl kGensP.2.1, by decide, CCR.head,
    CCR.hl, by norm_num, CCR.hs⟩

theorem chainT0 : ChainK 100 7 (permsOf t0GenW) t0ChainW (#v[2, 0] : Vector (Fin 100) 2)
    CT0.S CT0.SI CT0.LR CT0.TR CT0.TRI 11 CT0.BP 1 100 :=
  ⟨by norm_num, by norm_num, by norm_num, gens_img rfl kGensP.2.2.1, by decide, CT0.head,
    CT0.hl, by norm_num, CT0.hs⟩

theorem chainM16 : ChainK 100 7 (permsOf m16GenW) m16ChainW (#v[0, 1, 2, 3] : Vector (Fin 100) 4)
    CM16.S CM16.SI CM16.LR CM16.TR CM16.TRI 8 CM16.BP 1 100 :=
  ⟨by norm_num, by norm_num, by norm_num, gens_img rfl kGensP.2.2.2.1, by decide, CM16.head,
    CM16.hl, by norm_num, CM16.hs⟩

theorem chainN8 : ChainK 100 7 (permsOf n8GenW) n8ChainW (#v[0, 1, 2] : Vector (Fin 100) 3)
    CN8.S CN8.SI CN8.LR CN8.TR CN8.TRI 6 CN8.BP 1 100 :=
  ⟨by norm_num, by norm_num, by norm_num, gens_img rfl kGensP.2.2.2.2.1, by decide, CN8.head,
    CN8.hl, by norm_num, CN8.hs⟩

theorem chainQ : ChainK 100 7 (permsOf qGenW) qChainW (#v[0] : Vector (Fin 100) 1)
    CQ.S CQ.SI CQ.LR CQ.TR CQ.TRI 6 CQ.BP 1 100 :=
  ⟨by norm_num, by norm_num, by norm_num, gens_img rfl kGensP.2.2.2.2.2, by decide, CQ.head,
    CQ.hl, by norm_num, CQ.hs⟩

theorem countP_congr' {α : Type} : ∀ {l : List α} {f g : α → Bool}, (∀ a ∈ l, f a = g a) →
    l.countP f = l.countP g
  | [], _, _, _ => rfl
  | a :: l, f, g, H => by
    rw [List.countP_cons, List.countP_cons, H a List.mem_cons_self,
      countP_congr' fun b hb => H b (List.mem_cons_of_mem _ hb)]

theorem ppTR {LR TR : Nat → Nat} {k : Nat}
    (h : (trPL 100 7 LR TR k).all (fun L => L.all fun t =>
      permOK 100 7 (mask 7) (100 * 7) t (pinv 100 7 t)) = true) :
    ∀ L ∈ trPL 100 7 LR TR k, ∀ t ∈ L, PP 100 7 t := fun L hL t ht =>
  PP_of_permOK hsz (List.all_eq_true.1 (List.all_eq_true.1 h L hL) t ht)

theorem kTRP : (∀ L ∈ trPL 100 7 CCA.LR CCA.TR 3, ∀ t ∈ L, PP 100 7 t) ∧
    (∀ L ∈ trPL 100 7 CT0.LR CT0.TR 2, ∀ t ∈ L, PP 100 7 t) := by
  have h := kTR
  rw [Bool.and_eq_true] at h
  exact ⟨ppTR h.1, ppTR h.2⟩

theorem ppcb : ∀ c ∈ cbP, PP 100 7 c :=
  PP_pfilterProducts hsz _ kTRP.1 _ [] (PP.id hsz) (fun _ h => absurd h List.not_mem_nil)

theorem cbT_eq : cbT = cbP.map (tabP 100 7) := by
  have hL : levelTables caChain = (trPL 100 7 CCA.LR CCA.TR 3).map (List.map (tabP 100 7)) :=
    levelTables_eq chainCA (by decide) (by decide)
  rw [cbT, hL, idT_tabP hsz]
  have := filterProducts_tabP (f := fun _ => true) (fk := fun _ => true) (fun _ _ => rfl)
    (trPL 100 7 CCA.LR CCA.TR 3) kTRP.1 (pidn 100 7) [] (PP.id hsz)
  rwa [List.map_nil] at this

end CertificateChecks.KernelKGC31HS

end
