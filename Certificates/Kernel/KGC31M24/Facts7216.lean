module

public import Certificates.Kernel.KGC31M24.Glue
public import Certificates.Kernel.KGC31M24.Small
public import Certificates.Kernel.KGC31M24.Inv0
public import Certificates.Kernel.KGC31M24.Inv1
public import Certificates.Kernel.KGC31M24.Inv2
public import Certificates.Kernel.KGC31M24.Inv3
public import Certificates.Kernel.KGC31M24.Cls
public import Certificates.Kernel.KGC31M24.Frame
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.Quasithin.Vol2.KGFactC31M24Data
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.HeModelKSound
public import CFSG.Certificates.Kernel.HexaKSound
public import CFSG.Certificates.Kernel.SporSch.ChainKElem
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelKGC31M24

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.KGC31P CFSG.KC.Child3 CFSG.KC.BfsPin
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M24 CFSG.Sporadic.Mathieu
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M24OC
open CFSG.KS.SporSch.MOC CFSG.Monster.B.Mathieu CFSG.ComponentClassification.J2Cover

#kc_forall_chunks invAll (fun k => invBlk k = true) 44 CertificateChecks.KernelKGC31M24.invBlk 1

#kc_forall_chunks clsAll (fun k => clsBlk k = true) 44 CertificateChecks.KernelKGC31M24.clsBlk 1

theorem of_blocks {f : Nat → Bool}
    (hb : ∀ k < 44, (List.range' (1000 * k) (min 1000 (RI.N - 1000 * k))).all f = true) :
    ∀ j < RI.N, f j = true := by
  intro j hj
  have hN := Nat.eq_of_beq_eq_true kN
  have hk : j / 1000 < 44 := by omega
  apply List.all_eq_true.1 (hb (j / 1000) hk) j
  rw [List.mem_range'_1]
  omega

theorem invOK_all : ∀ j < RI.N, invOne j = true := of_blocks fun k hk => invAll k hk

theorem repK_all : ∀ j < RI.N,
    repK 24 5 RI.GP RI.GIP 2 RI.CS RI.OFF RI.CI RI.E RI.P RI.L RI.K RI.S RI.SI RI.N 40000 j = true :=
  of_blocks fun k hk => clsAll k hk

theorem inv_facts {j : Nat} (hj : j < RI.N) :
    PP 24 5 (RI.E j) ∧ porbOne 24 5 5 X5 C5 (RI.E j) = true ∧
      porbOne 24 5 7 X7 C7 (RI.E j) = true ∧ pactOne 24 5 11 X11 (RI.E j) = true ∧
      pactOne 24 5 23 X23 (RI.E j) = true := by
  have h := invOK_all j hj
  simp only [invOne, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨PP_of_permOK hsz h1, h2, h3, h4, h5⟩

theorem gens_bind : (pairTables m24gA m24gB).size = 2 ∧ (pairTables m24gA⁻¹ m24gB⁻¹).size = 2 ∧
    ∀ l < 2, (pairTables m24gA m24gB)[l]! = arrTable 24 (unpack 24 5 (RI.GP l)) ∧
      (pairTables m24gA⁻¹ m24gB⁻¹)[l]! = arrTable 24 (unpack 24 5 (RI.GIP l)) := by
  have hP := kGP
  have hI := kGIP
  simp only [Bool.and_eq_true] at hP hI
  obtain ⟨g0, g1⟩ := hP
  obtain ⟨i0, i1⟩ := hI
  refine ⟨rfl, rfl, fun l hl => ?_⟩
  interval_cases l
  · refine ⟨?_, ?_⟩
    · change toTable m24gA = _
      rw [Nat.eq_of_beq_eq_true g0]
      exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img imgA
    · change toTable m24gA⁻¹ = _
      exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img (invK_rep imgA i0)
  · refine ⟨?_, ?_⟩
    · change toTable m24gB = _
      rw [Nat.eq_of_beq_eq_true g1]
      exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img imgB
    · change toTable m24gB⁻¹ = _
      exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img (invK_rep imgB i1)

theorem gens_canon : ∀ l < 2, canonK 24 5 (mask 5) (24 * 5) (RI.GP l) = true ∧
    canonK 24 5 (mask 5) (24 * 5) (RI.GIP l) = true := by
  have h := kGc
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  intro l hl
  interval_cases l
  · exact ⟨a, b⟩
  · exact ⟨c, d⟩

theorem cs_pos : ∀ c ∈ RI.CS, 0 < c := by
  rw [kCS]
  decide

theorem kRep : (Nat.beq (M24CK.getD 0 CFSG.KS.SporSch.MOC.clsD0).R (RI.E (lget RI.OFF 0)) &&
    Nat.beq (M24CK.getD 1 CFSG.KS.SporSch.MOC.clsD0).R (RI.E (lget RI.OFF 1))) = true := by
  quickRfl

theorem rep_table {i : Nat} (hi : i < m24InvReps.length) :
    toTable m24InvReps[i] = arrTable 24 (unpack 24 5 (RI.E (lget RI.OFF i))) := by
  have h := kRep
  simp only [Bool.and_eq_true] at h
  obtain ⟨r0, r1⟩ := h
  have hi2 : i < 2 := by simpa [m24InvReps, m24InvRepWords] using hi
  rw [← List.getD_eq_getElem _ 1 hi]
  interval_cases i
  · rw [← Nat.eq_of_beq_eq_true r0]
    exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img imgRep0
  · rw [← Nat.eq_of_beq_eq_true r1]
    exact CFSG.KS.SporSch.CodesImg.toTable_eq_arrTable_of_img imgRep1

theorem mem_invs : ∀ t ∈ invs, ∃ j < RI.N, t = tabP 24 5 (RI.E j) := by
  intro t ht
  rw [invs, closureTabs, List.mem_flatMap] at ht
  obtain ⟨r, hr, ht⟩ := ht
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hr
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
  have hiCS : i < RI.CS.length := by
    rw [kCS]
    simpa [m24InvReps, m24InvRepWords] using hi
  rw [rep_table hi, closure_rep gens_bind gens_canon kOff repK_all cs_pos hiCS] at ht
  simp only [Array.toList_ofFn, List.mem_ofFn] at ht
  obtain ⟨k, rfl⟩ := ht
  exact ⟨lget RI.OFF i + k, (ci_eq kOff repK_all hiCS k.isLt).1, rfl⟩

theorem orb5 : orbCheck 24 5 invs [x5T] cands5 = true := by
  have hx : x5T = tabP 24 5 X5 := wT w5
  rw [hx, cands5_eq, orbCheck, List.all_cons, List.all_nil, Bool.and_true, invOK_tabP ppX5,
    Bool.true_and, List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [orbOne_tabP hsz ppX5 (inv_facts hj).1 ppC5]
  exact (inv_facts hj).2.1

theorem orb7 : orbCheck 24 7 invs [x7T] cands7 = true := by
  have hx : x7T = tabP 24 5 X7 := wT w7
  rw [hx, cands7_eq, orbCheck, List.all_cons, List.all_nil, Bool.and_true, invOK_tabP ppX7,
    Bool.true_and, List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [orbOne_tabP hsz ppX7 (inv_facts hj).1 ppC7]
  exact (inv_facts hj).2.2.1

theorem act11 : actCheck 24 11 invs [x11T] = true := by
  have hx : x11T = tabP 24 5 X11 := wT w11
  rw [hx, actCheck, List.all_cons, List.all_nil, Bool.and_true, invOK_tabP ppX11,
    Bool.true_and, List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [actOne_tabP ppX11 (inv_facts hj).1]
  exact (inv_facts hj).2.2.2.1

theorem act23 : actCheck 24 23 invs [x23T] = true := by
  have hx : x23T = tabP 24 5 X23 := wT w23
  rw [hx, actCheck, List.all_cons, List.all_nil, Bool.and_true, invOK_tabP ppX23,
    Bool.true_and, List.all_eq_true]
  intro t ht
  obtain ⟨j, hj, rfl⟩ := mem_invs t ht
  rw [actOne_tabP ppX23 (inv_facts hj).1]
  exact (inv_facts hj).2.2.2.2

theorem ord5 : ordTest 24 5 x5T = true := by rw [x5T, wT, ordTest_tabP (ppw' w5)]; exact kOrd5
theorem ord7 : ordTest 24 7 x7T = true := by rw [x7T, wT, ordTest_tabP (ppw' w7)]; exact kOrd7
theorem ord11 : ordTest 24 11 x11T = true := by
  rw [x11T, wT, ordTest_tabP (ppw' w11)]; exact kOrd11
theorem ord23 : ordTest 24 23 x23T = true := by
  rw [x23T, wT, ordTest_tabP (ppw' w23)]; exact kOrd23

theorem candInv : ((List.range 26).all fun k => invOK 24 (candT k) (invT 24 (candT k))) = true := by
  rw [List.all_eq_true]
  intro k _
  rw [candT, wT]
  exact invOK_tabP (ppw' _)

theorem frameInv : (frameConjT.all fun c => invOK 24 c (invT 24 c)) = true := by
  rw [frameConjT, List.all_map, List.all_eq_true]
  intro p _
  simp only [Function.comp_apply]
  rw [wT]
  exact invOK_tabP (ppw' _)

theorem repG (l : Int) : Rep 24 (gensT l) (gensG l) := by
  unfold gensT gensG
  split
  · exact rep_toTable (by norm_num) _
  · exact rep_toTable (by norm_num) _

theorem imgW (wd : List Int) : imageList (wordG gensG wd) = (unpack 24 5 (pw wd)).toList := by
  refine imageList_of_rep (ppw' wd).1 ?_
  rw [← wT]
  exact Rep.wordT (by norm_num) wd fun l _ => repG l

theorem qImg : ∀ j < qGen.length, imageList (qGen.getD j 1) = (unpack 24 5 (QQ.S j)).toList := by
  intro j hj
  have hj' : j < qGenW.length := by simpa [qGen] using hj
  have e : qGen.getD j 1 = tab (wordG gensG qGenW[j]) := by
    rw [List.getD_eq_getElem _ _ hj]
    simp [qGen]
  rw [e, tab_eq, imgW, ← List.getD_eq_getElem _ [] hj']
  have h := kQS
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h
  have hj4 : j < 4 := by simpa [qGenW] using hj'
  interval_cases j
  · rw [Nat.eq_of_beq_eq_true a]
  · rw [Nat.eq_of_beq_eq_true b]
  · rw [Nat.eq_of_beq_eq_true c]
  · rw [Nat.eq_of_beq_eq_true d]

theorem chainQ : ChainK 24 5 qGen qChainW (#v[1, 0] : Vector (Fin 24) 2)
    QQ.S QQ.SI QQ.LR QQ.TR QQ.TRI 7 QQ.BP 2 16 :=
  ⟨by norm_num, by norm_num, by norm_num, qImg, by decide, QQ.head, QQ.hl, by norm_num, QQ.hs⟩

theorem mem_allTables_q : ∀ T ∈ allTables qChain, ∃ j < 128, T = tabP 24 5 (qE j) := by
  intro T hT
  obtain ⟨g, hg, hRep⟩ := exists_mem_of_forall₂_right
    (forall₂_allTables_elem chainQ (by decide) (by decide)) T hT
  rw [List.mem_reverse, List.mem_map] at hg
  obtain ⟨j, hj, rfl⟩ := hg
  refine ⟨j, ?_, eq_tabP_of_rep (by norm_num) (allTables_size _ T hT) hRep
    (imageList_of_prep (prep_elemK chainQ j))⟩
  rw [List.mem_range, Nat.eq_of_beq_eq_true kQN] at hj
  exact hj

theorem ppU5 : ∀ b ∈ u5P, PP 24 5 b := ppL u5W

theorem frame_of (k : Nat) (fr : List (ℕ × List ℤ)) (hk : (List.range 128).all (frOne k fr) = true) :
    frameCheck 24 7 x7T (conjAll (candT k) u5T) (frameVs k) (frameCands fr) = true := by
  have hub : conjAll (candT k) u5T = (cAll (cnd k) u5P).map (tabP 24 5) := by
    rw [candT, u5T]
    exact cA _ _
  have hc : candT k = tabP 24 5 (cnd k) := wT _
  have hx : x7T = tabP 24 5 X7 := wT w7
  rw [hub, frameCands_eq, hx, frameCheck, invOK_tabP ppX7, Bool.true_and, frameVs,
    List.all_map, List.all_eq_true]
  intro T hT
  obtain ⟨j, hj, rfl⟩ := mem_allTables_q T hT
  have h := List.all_eq_true.1 hk j (List.mem_range.2 hj)
  simp only [frOne, Bool.and_eq_true] at h
  obtain ⟨hp, hf⟩ := h
  have hq : PP 24 5 (qE j) := PP_of_permOK hsz hp
  have hcd : PP 24 5 (cnd k) := ppw' _
  simp only [Function.comp_apply]
  rw [hc, invT_tabP hcd, conjTab_tabP hcd hcd.pinv hq,
    frameOne_tabP hsz ppX7 (PP_pcj hcd hcd.pinv hq) (ppcAll hcd ppU5) (ppfC fr)]
  exact hf

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Quasithin.KGC31.Native CFSG.Quasithin.KGC31.M24 in
open Certificates in
theorem cert7216 : ordTest 24 5 x5T = true ∧ ordTest 24 7 x7T = true ∧ ordTest 24 11 x11T = true ∧
    ordTest 24 23 x23T = true ∧
    orbCheck 24 5 invs [x5T] cands5 = true ∧
    orbCheck 24 7 invs [x7T] cands7 = true ∧
    actCheck 24 11 invs [x11T] = true ∧
    actCheck 24 23 invs [x23T] = true ∧
    ((List.range 26).all fun k => invOK 24 (candT k) (invT 24 (candT k))) = true ∧
    (frameConjT.all fun c => invOK 24 c (invT 24 c)) = true ∧
    frameCheck 24 7 x7T (conjAll (candT 12) u5T) (frameVs 12) (frameCands fr0W) = true ∧
    frameCheck 24 7 x7T (conjAll (candT 17) u5T) (frameVs 17) (frameCands fr1W) = true ∧
    frameCheck 24 7 x7T (conjAll (candT 18) u5T) (frameVs 18) (frameCands fr2W) = true :=
  ⟨ord5, ord7, ord11, ord23, orb5, orb7, act11, act23, candInv, frameInv,
    frame_of 12 fr0W kFr0, frame_of 17 fr1W kFr1, frame_of 18 fr2W kFr2⟩

end CertificateChecks.KernelKGC31M24

end
