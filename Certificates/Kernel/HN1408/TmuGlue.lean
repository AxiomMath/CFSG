module

public import Certificates.Kernel.HN1408.TmuChk
public import Certificates.Kernel.HN1408.Spec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Simple2S5.S2S5TCheck
import CFSG.Certificates.Kernel.BfsPinSetSound
public import Certificates.Kernel.HN1408.EnumH

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Simple2S5
open CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem tmBA {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := (bAnd_iff _ _).1 h

theorem tmNot {c : Bool} (h : bIf(c, false, true) = true) : c = false := by
  cases c
  · rfl
  · exact absurd h (by decide)

theorem tmY_ok : ∀ k, ∀ w ∈ ykWords.getD k [], lettersOK w = true
  | 0 => by decide
  | 1 => by decide
  | _ + 2 => by
    intro w hw
    simp [ykWords] at hw

theorem expandL_eq (subs : List (List Nat)) (l : List Nat) :
    expandL subs l = specWord subs (l.map fun i => (i, 1)) := by
  simp [expandL, specWord, List.flatMap_map]

theorem WK_expandL (k : Nat) (l : List Nat) : WK (expandL (ykWords.getD k []) l) = tmL k l := by
  rw [expandL_eq, WK_specWord (tmY_ok k)]
  rfl

theorem lettersOK_expandL (k : Nat) (l : List Nat) :
    lettersOK (expandL (ykWords.getD k []) l) = true := by
  rw [expandL_eq]
  exact lettersOK_specWord (tmY_ok k) _

abbrev TmFacts (ws : List (List Nat)) (m cnt : Nat) (T PL GI : Nat → Nat) : Prop :=
  enumW 1000 m ws = true ∧ subgroupList 1000 ws = (hRec 1408 11 cnt T PL).1 ∧
    (∀ i < cnt, Cn (T i)) ∧ (∀ w ∈ ws, lettersOK w = true) ∧ ws.length = 2 ∧
    (∀ j < 2, GI j = WK (ws.getD j [])) ∧ (∀ j < 2, Cn (GI j)) ∧ cnt = m

theorem tmRec_of {k m cnt : Nat} {ls : List (List Nat)}
    {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat}
    (h : tmHd k ls m G GI GJ T PL cnt = true)
    (hr : tmRec G GI GJ T PL POS SRT SRI HS HSI CL cnt = true) :
    TmFacts (ls.map (expandL (ykWords.getD k []))) m cnt T PL GI := by
  unfold tmHd at h
  obtain ⟨h1, h2⟩ := tmBA h
  obtain ⟨h3, h4⟩ := tmBA h2
  obtain ⟨h5, h6⟩ := tmBA h4
  have hlen : ls.length = 2 := Nat.eq_of_beq_eq_true h1
  have hm : cnt = m := Nat.eq_of_beq_eq_true h5
  have hg : ∀ j < 2, GI j = tmL k (ls.getD j []) ∧ G j = idK ∧
      canonK 1408 11 (mask 11) (1408 * 11) (GJ j) = true ∧
      invEqK 1408 11 (mask 11) (1408 * 11) (GI j) (GJ j) = true := by
    intro j hj
    obtain ⟨a, h8⟩ := tmBA (allN_spec h3 j hj)
    obtain ⟨b, h9⟩ := tmBA h8
    obtain ⟨c, d⟩ := tmBA h9
    exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, c, d⟩
  have hwl : (ls.map (expandL (ykWords.getD k []))).length = 2 := by rw [List.length_map, hlen]
  have hgd : ∀ j, (ls.map (expandL (ykWords.getD k []))).getD j [] =
      expandL (ykWords.getD k []) (ls.getD j []) := by
    clear h h1 h2 h3 h4 hlen hg hwl
    induction ls with
    | nil => intro j; rfl
    | cons a l ih =>
      intro j
      cases j with
      | zero => rfl
      | succ j => exact ih j
  have hGI : ∀ j < 2, GI j = WK ((ls.map (expandL (ykWords.getD k []))).getD j []) := by
    intro j hj
    rw [hgd, WK_expandL]
    exact (hg j hj).1
  have hl : ∀ w ∈ ls.map (expandL (ykWords.getD k [])), lettersOK w = true := by
    intro w hw
    rw [List.mem_map] at hw
    obtain ⟨l, -, rfl⟩ := hw
    exact lettersOK_expandL k l
  unfold tmRec at hr
  obtain ⟨hp, hr2⟩ := tmBA hr
  obtain ⟨hs, hc⟩ := tmBA hr2
  have hp' : ∀ i < cnt, penumPtK 1408 11 (mask 11) (1408 * 11) true G GI
      (ls.map (expandL (ykWords.getD k []))).length cnt T PL POS SRT SRI i = true := by
    rw [hwl]
    exact fun i hi => penumSl_spec hp i (Nat.zero_le _) (by omega) hi
  have hcl : ∀ c < cnt * ((ls.map (expandL (ykWords.getD k []))).length +
      (ls.map (expandL (ykWords.getD k []))).length),
      findPtK cnt T (prodQK 1408 11 (mask 11) ((ls.map (expandL (ykWords.getD k []))).length +
        (ls.map (expandL (ykWords.getD k []))).length) T
        (bothK (ls.map (expandL (ykWords.getD k []))).length GI GJ)) CL c = true := by
    rw [hwl]
    exact fun c hc' => slK_spec hc c (Nat.zero_le _) (by change c < 0 + cnt * 4; omega)
      (by change c < cnt * 4; omega)
  obtain ⟨e1, e2⟩ := enumW_of (cap := 1000) hl (fun j hj => (hg j (by omega)).2.1)
    (fun j hj => hGI j (by omega)) (fun j hj => ⟨(hg j (by omega)).2.2.2, (hg j (by omega)).2.2.1⟩)
    h6 hp' (fun i hi => slK_spec hs i (Nat.zero_le _) (by omega) hi) hcl hm
  refine ⟨e1, e2, fun i hi => penumPt_canon (hp' i hi), hl, hwl, hGI, fun j hj => ?_, hm⟩
  rw [hGI j hj, hgd]
  exact cn_WK (lettersOK_expandL k _)

theorem tabsW_two {ws : List (List Nat)} {GI : Nat → Nat} (hl : ∀ w ∈ ws, lettersOK w = true)
    (hlen : ws.length = 2) (hg : ∀ j < 2, GI j = WK (ws.getD j [])) (f : Table → Bool) :
    (tabsW ws).all f = (f (tabT (unpack 1408 11 (GI 0))) && f (tabT (unpack 1408 11 (GI 1)))) := by
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hlen
  rw [hg 0 (by omega), hg 1 (by omega)]
  have ha := tabW_eq (hl a (by simp))
  have hb := tabW_eq (hl b (by simp))
  simp only [tabsW, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true]
  rw [ha.1, hb.1]
  rfl

theorem tmMem {cnt q : Nat} {T PL : Nat → Nat} {X : Nat} (hT : ∀ i < cnt, Cn (T i)) (hX : Cn X)
    (hq : Nat.blt q cnt = true) (he : Nat.beq (T q) X = true) :
    memT 1408 (hRec 1408 11 cnt T PL).1 (tabT (unpack 1408 11 X)) = true := by
  have hq' := Nat.blt_eq.mp hq
  refine memT_of hq' ?_
  rw [tblEq_eq hX (hT _ hq'), ← Nat.eq_of_beq_eq_true he]
  exact Nat.beq_refl _

theorem tmNotMem {cnt : Nat} {T PL : Nat → Nat} {X : Nat} (hT : ∀ i < cnt, Cn (T i)) (hX : Cn X)
    (h : allN cnt (fun i => bIf(Nat.beq (T i) X, false, true)) = true) :
    memT 1408 (hRec 1408 11 cnt T PL).1 (tabT (unpack 1408 11 X)) = false := by
  unfold memT
  rw [Bool.eq_false_iff, ne_eq, Array.any_eq_true]
  rintro ⟨i, hi, he⟩
  have hi' : i < cnt := by simpa [hRec] using hi
  rw [← getElem!_pos _ i hi, hRec_get hi', tblEq_eq hX (hT i hi')] at he
  have e := Nat.eq_of_beq_eq_true he
  have := tmNot (allN_spec h i hi')
  rw [← e, Nat.beq_refl] at this
  cases this

theorem tmWT {wd : List Nat} (h : lettersOK wd = true) :
    tabW wd = tabT (unpack 1408 11 (WK wd)) ∧ Cn (WK wd) := tabW_eq h

theorem tmU (k : Nat) : WK (uWord k) = tmL k (uLetters.getD k []) := WK_expandL k _

theorem tmuOne_of {k tc mc : Nat} {TT TPL TGI MT MPL MGI P : Nat → Nat}
    (hT : TmFacts (tWords k) 16 tc TT TPL TGI) (hM : TmFacts (mWords k) 8 mc MT MPL MGI)
    (hs : tmScan k TT TGI tc MT MGI mc P = true) : tmuOne k = true := by
  obtain ⟨eT, sT, cT, lT, nT, gT, gcT, mT⟩ := hT
  obtain ⟨eM, sM, cM, lM, nM, gM, gcM, mM⟩ := hM
  subst mT mM
  have wAZ' := tmWT (wd := wordAZ) (by decide)
  have hu : lettersOK (uWord k) = true := lettersOK_expandL k _
  have eu := tmWT hu
  have hy0 : lettersOK (yWord k 0) = true := lettersOK_getD (tmY_ok k) 0
  have hy1 : lettersOK (yWord k 1) = true := lettersOK_getD (tmY_ok k) 1
  have ey0 := tmWT hy0
  have ey1 := tmWT hy1
  unfold tmScan at hs
  simp only [strictB_app, bAnd_iff] at hs
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := hs
  rw [← tmU] at s6 s8 s9 s10
  have c1 : memT 1408 (hRec 1408 11 16 TT TPL).1 (tabT (unpack 1408 11 (WK wordAZ))) = true :=
    tmMem cT wAZ'.2 s3 s4
  have c2 : (hRec 1408 11 16 TT TPL).1.all (fun x => tblEq 1408 x (tabT (unpack 1408 11 idK)) ||
      tblEq 1408 x (tabT (unpack 1408 11 (WK wordAZ))) ||
      !((tabsW (tWords k)).all (commTT 1408 x))) = true := by
    rw [Array.all_eq_true]
    intro i hi
    have hi' : i < 16 := by simpa [hRec] using hi
    rw [← getElem!_pos _ i hi, hRec_get hi', tabsW_two lT nT gT, commTT_eq (cT i hi') (gcT 0 (by omega)),
      commTT_eq (cT i hi') (gcT 1 (by omega)), tblEq_eq (cT i hi') cId, tblEq_eq (cT i hi') wAZ'.2]
    have h := allN_spec s1 i hi'
    simp only [strictB_app] at h
    revert h
    generalize Nat.beq (TT i) idK = a
    generalize Nat.beq (TT i) (WK wordAZ) = b
    generalize commP (TT i) (TGI 0) = c
    generalize commP (TT i) (TGI 1) = d
    cases a <;> cases b <;> cases c <;> cases d <;> simp
  have c3 : (tabsW (mWords k)).all (memT 1408 (hRec 1408 11 16 TT TPL).1) = true := by
    rw [tabsW_two lM nM gM, Bool.and_eq_true]
    have t0 := tmBA (allN_spec s7 0 (by omega))
    have t1 := tmBA (allN_spec s7 1 (by omega))
    exact ⟨tmMem cT (gcM 0 (by omega)) t0.1 t0.2, tmMem cT (gcM 1 (by omega)) t1.1 t1.2⟩
  have c4 : (hRec 1408 11 8 MT MPL).1.all (fun x => tblEq 1408 x (tabT (unpack 1408 11 idK)) ||
      tblEq 1408 x (tabT (unpack 1408 11 (WK wordAZ))) || !invoOK 1408 x) = true := by
    rw [Array.all_eq_true]
    intro i hi
    have hi' : i < 8 := by simpa [hRec] using hi
    rw [← getElem!_pos _ i hi, hRec_get hi', invoOK_eq (cM i hi'), tblEq_eq (cM i hi') cId,
      tblEq_eq (cM i hi') wAZ'.2]
    have h := allN_spec s2 i hi'
    revert h
    generalize Nat.beq (MT i) idK = a
    generalize Nat.beq (MT i) (WK wordAZ) = b
    generalize Nat.beq (pc (MT i) (MT i)) idK = c
    cases a <;> cases b <;> cases c <;> simp
  have c5 : memT 1408 (hRec 1408 11 16 TT TPL).1 (tabT (unpack 1408 11 (WK (uWord k)))) = true :=
    tmMem cT eu.2 s5 s6
  have c6 : memT 1408 (hRec 1408 11 8 MT MPL).1 (tabT (unpack 1408 11 (WK (uWord k)))) = false :=
    tmNotMem cM eu.2 s8
  have c7 : involOK 1408 (tabT (unpack 1408 11 (WK (uWord k)))) = true := by
    rw [involOK_eq eu.2]
    exact s9
  have c8 : tblEq 1408 (tabT (unpack 1408 11 (WK (uWord k)))) (tabT (unpack 1408 11 (WK wordAZ))) =
      false := by
    rw [tblEq_eq eu.2 wAZ'.2]
    exact tmNot s10
  have c9 : commTT 1408 (tabT (unpack 1408 11 (WK (yWord k 0))))
      (tabT (unpack 1408 11 (WK (yWord k 1)))) = false := by
    rw [commTT_eq ey0.2 ey1.2]
    have := tmNot s11
    rwa [tmY, getD_map_WK, getD_map_WK] at this
  unfold tmuOne
  simp only []
  rw [wordOK_of (by decide), wordOK_of hy0, wordOK_of hy1, wordOK_of hu, eT, eM, sT, sM, eu.1,
    wAZ'.1, ey0.1, ey1.1, idT_eq]
  simp only [c1, c2, c3, c4, c5, c6, c7, c8, c9, Bool.and_true, Bool.true_and, Bool.not_false]

theorem c8Check_of {tc : Nat} {TT TPL TGI : Nat → Nat} (hT : TmFacts (tWords 0) 16 tc TT TPL TGI)
    (hs : tmC8 TT tc = true) : c8Check = true := by
  obtain ⟨-, sT, cT, -, -, -, -, mT⟩ := hT
  subst mT
  have wAZ' := tmWT (wd := wordAZ) (by decide)
  have hu : lettersOK (uWord 0) = true := lettersOK_expandL 0 _
  have eu := tmWT hu
  have hU := tmU 0
  have ctu : Cn (pcomp 1408 11 (mask 11) (WK wordAZ) (WK (uWord 0))) := cn_pc wAZ'.2 eu.2
  unfold c8Check
  simp only []
  rw [sT, wAZ'.1, eu.1, compT_unpack wAZ'.2 eu.2, Array.all_eq_true]
  intro v hv
  have hv' : v < 16 := by simpa [hRec] using hv
  rw [← getElem!_pos _ v hv, hRec_get hv', involOK_eq (cT v hv'), tblEq_eq (cT v hv') wAZ'.2]
  unfold tmC8 at hs
  simp only [strictB_app] at hs
  have h := allN_spec hs v hv'
  rw [← hU] at h
  revert h
  cases e1 : involK (TT v)
  · simp
  · cases e2 : Nat.beq (TT v) (WK wordAZ)
    · simp only [Bool.not_true, Bool.false_or, Bool.or_false]
      intro h
      rw [CFSG.KC.BfsPin.anyN_eq, List.any_eq_true] at h
      obtain ⟨i, hi, hx⟩ := h
      have hi' := List.mem_range.1 hi
      rw [Array.any_eq_true]
      refine ⟨i, by rw [hRec_size]; exact hi', ?_⟩
      rw [← getElem!_pos _ i (by rw [hRec_size]; exact hi'), hRec_get hi',
        compT_unpack (cT i hi') (cT v hv'), compT_unpack eu.2 (cT i hi'),
        compT_unpack ctu (cT i hi'),
        tblEq_eq (canonK_pcomp (cT i hi') (cT v hv')) (canonK_pcomp eu.2 (cT i hi')),
        tblEq_eq (canonK_pcomp (cT i hi') (cT v hv')) (canonK_pcomp ctu (cT i hi'))]
      change (Nat.beq (pc (TT i) (TT v)) (pc (WK (uWord 0)) (TT i)) ||
        Nat.beq (pc (TT i) (TT v)) (pc (pc (WK wordAZ) (WK (uWord 0))) (TT i))) = true
      revert hx
      cases Nat.beq (pc (TT i) (TT v)) (pc (WK (uWord 0)) (TT i)) <;> simp
    · simp

theorem fixCheck_of (hs : tmFix = true) : fixCheck = true := by
  have wAZ' := tmWT (wd := wordAZ) (by decide)
  have hu : lettersOK (uWord 1) = true := lettersOK_expandL 1 _
  have eu := tmWT hu
  unfold tmFix at hs
  simp only [strictB_app, bAnd_iff] at hs
  obtain ⟨h1, h2⟩ := hs
  rw [← tmU 1] at h1
  unfold fixCheck
  simp only []
  rw [eu.1, wAZ'.1, Bool.and_eq_true]
  constructor
  · rw [CFSG.KS.TW.allIn_iff]
    intro p hp
    rw [ap_eq eu.2 hp]
    have := Nat.ne_of_beq_eq_false (tmNot (allN_spec h1 p hp))
    simpa using this
  · rw [CFSG.KC.BfsPin.anyN_eq, List.any_eq_true] at h2
    rw [List.any_eq_true]
    obtain ⟨p, hp, hq⟩ := h2
    refine ⟨p, hp, ?_⟩
    rw [ap_eq wAZ'.2 (List.mem_range.1 hp)]
    simpa using Nat.eq_of_beq_eq_true hq

theorem tmuCheck_true : tmuCheck = true := by
  have rT0 := tmRec_of tmkHT0 tmkRT0
  have rT1 := tmRec_of tmkHT1 tmkRT1
  unfold tmuCheck
  rw [tmuOne_of rT0 (tmRec_of tmkHM0 tmkRM0) tmkS0, tmuOne_of rT1 (tmRec_of tmkHM1 tmkRM1) tmkS1,
    c8Check_of rT0 tmkC8, fixCheck_of tmkFix]
  rfl

end CFSG.KD.HN1408

end
