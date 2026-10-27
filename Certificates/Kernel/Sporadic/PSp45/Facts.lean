module

public import Certificates.Kernel.Sporadic.PSp45.Data
public import Certificates.Kernel.Sporadic.PSp45.Direct
public import CFSG.Certificates.Kernel.SporSch.MathieuOCSound
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.GH74.KGroups.NativeChecks2
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.PSp45

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.M11 CFSG.KS.MEnum CFSG.KS.SporSch.MOC
open CFSG.GH74.KGroups

theorem bindX : bindListK 45 6 (P45Q.S 0) tX = true := by quickRfl

theorem bindY : bindListK 45 6 (P45Q.S 1) tY = true := by quickRfl

theorem bindAX : bindListK 45 6 (A45Q.S 0) tX = true := by quickRfl

theorem bindAY : bindListK 45 6 (A45Q.S 1) tY = true := by quickRfl

theorem bindAF : bindListK 45 6 (A45Q.S 2) tF = true := by quickRfl

theorem pX : permOK 45 6 (mask 6) (45 * 6) (P45Q.S 0) (P45Q.SI 0) = true := by quickRfl

theorem pY : permOK 45 6 (mask 6) (45 * 6) (P45Q.S 1) (P45Q.SI 1) = true := by quickRfl

theorem cOne : canonK 45 6 (mask 6) (45 * 6) One = true := by quickRfl

theorem rep0a : abOK (invRepWords.getD 0 []) = true := by quickRfl

theorem rep0b : Nat.beq (abWordK 45 6 (mask 6) (pidn 45 6) (P45Q.S 0) (P45Q.SI 0) (P45Q.S 1)
    (P45Q.SI 1) (invRepWords.getD 0 [])) R0 = true := by quickRfl

theorem rep1a : abOK (invRepWords.getD 1 []) = true := by quickRfl

theorem rep1b : Nat.beq (abWordK 45 6 (mask 6) (pidn 45 6) (P45Q.S 0) (P45Q.SI 0) (P45Q.S 1)
    (P45Q.SI 1) (invRepWords.getD 1 [])) R1 = true := by quickRfl

theorem clsOK' : allC (clsOneR 45 6 tX tY 2 1000) P45CL = true := by quickRfl

theorem disjOK : clsDisj 45 6 P45CL = true := by quickRfl

theorem neOK : allC (fun d => Nat.blt 0 (CFSG.KS.Mathieu.lenN d.2.2.2.2.2.2)) P45CL = true := by
  quickRfl

theorem szOK' : szOK 45 6 = true := by quickRfl

theorem tX_eq : tX = imageList x45 := by decide +kernel

theorem tY_eq : tY = imageList y45 := by decide +kernel

theorem tF_eq : tF = imageList f45 := by decide +kernel

theorem img_of_bind {g : Equiv.Perm (Fin 45)} {l : List Nat} {P : Nat} (hl : l = imageList g)
    (h : bindListK 45 6 P l = true) : imageList g = (unpack 45 6 P).toList := by
  rw [← hl, ← toArray_eq_of_bindListK h]

theorem imgX : imageList x45 = (unpack 45 6 (P45Q.S 0)).toList := img_of_bind tX_eq bindX

theorem imgY : imageList y45 = (unpack 45 6 (P45Q.S 1)).toList := img_of_bind tY_eq bindY

theorem getD_map_eval (ws : List (List Int)) (S : List (Equiv.Perm (Fin 45))) (j : Nat) :
    (ws.map (evalCodes S)).getD j 1 = evalCodes S (ws.getD j []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[j]? <;> rfl

theorem img_word {wd : List Int} {P : Nat} (hw : abOK wd = true)
    (h : Nat.beq (abWordK 45 6 (mask 6) (pidn 45 6) (P45Q.S 0) (P45Q.SI 0) (P45Q.S 1) (P45Q.SI 1)
      wd) P = true) :
    imageList (evalCodes [x45, y45] wd) = (unpack 45 6 P).toList := by
  rw [abWordK_rep szOK' imgX imgY pX pY hw, Nat.eq_of_beq_eq_true h]

theorem imgOne : imageList (1 : Equiv.Perm (Fin 45)) = (unpack 45 6 One).toList := by
  decide +kernel

theorem imgRep0 : imageList (invReps.getD 0 1) = (unpack 45 6 R0).toList := by
  rw [invReps, getD_map_eval]
  exact img_word rep0a rep0b

theorem imgRep1 : imageList (invReps.getD 1 1) = (unpack 45 6 R1).toList := by
  rw [invReps, getD_map_eval]
  exact img_word rep1a rep1b

theorem chainP : ChainK 45 6 [tab x45, tab y45] wordsP (#v[0, 1, 16, 3] : Vector (Fin 45) 4)
    P45Q.S P45Q.SI P45Q.LR P45Q.TR P45Q.TRI 8 P45Q.BP 3 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, P45Q.head, P45Q.hl,
    by norm_num, P45Q.hs⟩
  have hj2 : j < 2 := hj
  interval_cases j
  · simp only [tab_eq, List.getD_cons_succ, List.getD_cons_zero]
    exact imgX
  · simp only [tab_eq, List.getD_cons_succ, List.getD_cons_zero]
    exact imgY

theorem chainA : ChainK 45 6 [tab x45, tab y45, tab f45] wordsA
    (#v[0, 1, 3, 9] : Vector (Fin 45) 4) A45Q.S A45Q.SI A45Q.LR A45Q.TR A45Q.TRI 11 A45Q.BP 3 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, A45Q.head, A45Q.hl,
    by norm_num, A45Q.hs⟩
  have hj3 : j < 3 := hj
  interval_cases j
  · simp only [tab_eq, List.getD_cons_succ, List.getD_cons_zero]
    exact img_of_bind tX_eq bindAX
  · simp only [tab_eq, List.getD_cons_succ, List.getD_cons_zero]
    exact img_of_bind tY_eq bindAY
  · simp only [tab_eq, List.getD_cons_succ, List.getD_cons_zero]
    exact img_of_bind tF_eq bindAF

theorem qp_eq : QP45 = certificate (by decide) [tab x45, tab y45] wordsP
    (#v[0, 1, 16, 3] : Vector (Fin 45) 4) (by decide) := rfl

theorem qa_eq : QA45 = certificate (by decide) [tab x45, tab y45, tab f45] wordsA
    (#v[0, 1, 3, 9] : Vector (Fin 45) 4) (by decide) := rfl

theorem validP : QP45.check = true ∧ QP45.orderCertificate = 25920 := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainP
  rw [qp_eq]
  exact ⟨h1, h2.trans (by decide)⟩

theorem validA : QA45.check = true ∧ QA45.orderCertificate = 51840 := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainA
  rw [qa_eq]
  exact ⟨h1, h2.trans (by decide)⟩

theorem gens_mem : ∀ g ∈ [x45, y45], g ∈ QP45.originalSubgroup := by
  rw [qp_eq, certificate_originalSubgroup]
  intro g hg
  apply Subgroup.subset_closure
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · simp [tab_eq]
  · simp [tab_eq]

theorem cosetX : (cosetOrderTables QP45 1 2).length = P45X.CS.sum := by
  rw [qp_eq]
  exact chainK_cosetCount (by decide) (by decide) chainP imgOne cOne (by norm_num) (by norm_num)
    (by decide) P45X.hc

theorem hR : invReps.length = P45CL.length ∧ ∀ j < P45CL.length,
    imageList (invReps.getD j 1) =
      (unpack 45 6 (P45CL.getD j (0, 0, 0, [], [], [], [])).2.2.1).toList := by
  refine ⟨by decide, fun j hj => ?_⟩
  have hj2 : j < 2 := by simpa [P45CL] using hj
  interval_cases j
  · exact imgRep0
  · exact imgRep1

theorem cover : repsOK 45 (pairTables x45 y45) (pairTables x45⁻¹ y45⁻¹)
        (cosetOrderTables QP45 1 2) (invReps.map toTable) 1000 = true ∧
      repSizes 45 (pairTables x45 y45) (pairTables x45⁻¹ y45⁻¹)
        (invReps.map toTable) 1000 = [45, 270] ∧
      (invReps.map toTable).all (ordTest 45 2) = true := by
  obtain ⟨h1, h2, h3⟩ := chainK_reps tX_eq tY_eq szOK' clsOK' disjOK hR (by norm_num)
    (X := cosetOrderTables QP45 1 2) (by rw [cosetX]; decide) neOK (by norm_num)
  exact ⟨h1, h2.trans (by decide), h3⟩

theorem total : repsTotal 45 (pairTables x45 y45) (pairTables x45⁻¹ y45⁻¹)
    (invReps.map toTable) (orderTables QP45 5) 1000 (wordsTest 45 2 5 ws45N) = 51840 := by
  have h := chainK_repsTotal (mx := 2) (my := 5) (by decide) (by decide) chainP tX_eq tY_eq
    (by norm_num) clsOK' hR (by norm_num) (by norm_num) (CW := [P45Y0.CS, P45Y1.CS])
    ⟨rfl, fun j hj => by
      have hj2 : j < 2 := by simpa [P45CL] using hj
      interval_cases j
      · exact ⟨by decide, P45Y0.hc⟩
      · exact ⟨by decide, P45Y1.hc⟩⟩ neOK
  rw [qp_eq]
  exact h.trans (by decide)

theorem pairInv_iff {M : Type*} [Group M] (a b : M) : PairInv ws45 a b ↔ WordsRel ws45N a b := by
  simp only [PairInv, WordsRel, ws45, ws45N, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, CFSG.GH74.KGroups.evalW, CFSG.Sporadic.Schreier.evalW,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, letterW, mul_one]
  simp

theorem count : NativeChecks.pairCountE QP45 2 5 ws45 = 51840 := by
  have hn : (45 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier QP45 := validP.1
  rw [← NativeChecks.pairCountB_eq_E, pairCountB,
    ← card_pairs QP45 hQ 2 5 (by norm_num) (by norm_num) ws45 (by decide)]
  have hA : x45 ∈ QP45.originalSubgroup := gens_mem _ (by simp)
  have hB : y45 ∈ QP45.originalSubgroup := gens_mem _ (by simp)
  have hreps : ∀ r ∈ invReps, r ∈ QP45.originalSubgroup ∧ orderOf r = 2 := by
    intro r hr
    have hmem : r ∈ QP45.originalSubgroup := by
      rw [invReps, List.mem_map] at hr
      obtain ⟨wd, -, rfl⟩ := hr
      exact evalCodes_mem _ gens_mem wd
    refine ⟨hmem, ?_⟩
    have h3 := cover.2.2
    rw [List.all_eq_true] at h3
    exact (ordTest_iff perm_faithful (rep_toTable hn r) (by norm_num)).1
      (h3 _ (List.mem_map_of_mem hr))
  have hcount := card_pairs_eq_repsTotal hn QP45 hQ (mx := 2) (my := 5) (ws := ws45N) (by norm_num)
    (by norm_num) (by decide) (pairTables_spec hn hA hB) invReps hreps 1000 cover.1
  rw [total] at hcount
  rw [← hcount]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun p => by rw [pairInv_iff])

theorem commute_evalW {M : Type*} [Monoid M] {σ a b : M} (ha : Commute σ a) (hb : Commute σ b) :
    ∀ w : List Bool, Commute σ (CFSG.GH74.KGroups.evalW a b w)
  | [] => Commute.one_right σ
  | false :: w => ha.mul_right (commute_evalW ha hb w)
  | true :: w => hb.mul_right (commute_evalW ha hb w)

theorem cent_eq_one_of {m : Nat} {a b σ : Equiv.Perm (Fin m)} {r : Fin m} (u : List Bool)
    (ws : List (List Bool)) (hfix : ∀ p, CFSG.GH74.KGroups.evalW a b u p = p → p = r)
    (hr : CFSG.GH74.KGroups.evalW a b u r = r)
    (horb : ∀ q : Fin m, CFSG.GH74.KGroups.evalW a b (ws.getD q.val []) r = q)
    (hx : σ * a = a * σ) (hy : σ * b = b * σ) : σ = 1 := by
  have hcx : Commute σ a := hx
  have hcy : Commute σ b := hy
  have hu := congrArg (fun g : Equiv.Perm (Fin m) => g r) (commute_evalW hcx hcy u).eq
  simp only [Equiv.Perm.mul_apply, hr] at hu
  have h0 : σ r = r := hfix _ hu.symm
  refine Equiv.ext fun q => ?_
  have hw := congrArg (fun g : Equiv.Perm (Fin m) => g r)
    (commute_evalW hcx hcy (ws.getD q.val [])).eq
  simp only [Equiv.Perm.mul_apply, h0, horb] at hw
  rw [hw, Equiv.Perm.one_apply]

theorem fix_only : ∀ p : Fin 45, CFSG.GH74.KGroups.evalW x45 y45 fixWord p = p → p = 0 := by
  decide +kernel

theorem orb_ok : ∀ q : Fin 45, CFSG.GH74.KGroups.evalW x45 y45 (orbWords.getD q.val []) 0 = q := by
  decide +kernel

theorem fix0 : CFSG.GH74.KGroups.evalW x45 y45 fixWord 0 = 0 := by
  decide +kernel

theorem cent_eq_one {σ : Equiv.Perm (Fin 45)} (hx : σ * x45 = x45 * σ) (hy : σ * y45 = y45 * σ) :
    σ = 1 :=
  cent_eq_one_of fixWord orbWords fix_only fix0 orb_ok hx hy

theorem centA : CFSG.KGroups.Native.centTrivA 45 (NativeChecks.enumA QA45)
    (NativeChecks.toA x45) (NativeChecks.toA y45) = true := by
  rw [← NativeChecks.centTrivCheck_enumA, centTrivCheck, List.all_eq_true]
  intro σ _
  by_cases h : σ * x45 = x45 * σ ∧ σ * y45 = y45 * σ
  · simp [cent_eq_one h.1 h.2]
  · rw [not_and_or] at h
    rcases h with h | h <;> simp [h]

theorem facts : (QP45.check = true ∧ QP45.orderCertificate = 25920)
    ∧ (QA45.check = true ∧ QA45.orderCertificate = 51840)
    ∧ ((List.finRange 45).all (fun j => QP45.sift (tauPerm j) 0) = true)
    ∧ (orderIs x45 2 = true ∧ orderIs y45 5 = true ∧ pairInvB ws45 x45 y45 = true)
    ∧ (NativeChecks.pairCountE QP45 2 5 ws45 = 51840)
    ∧ (normCheck QP45 QA45.original.toList x45 y45 = true)
    ∧ (CFSG.KGroups.Native.centTrivA 45 (NativeChecks.enumA QA45)
      (NativeChecks.toA x45) (NativeChecks.toA y45) = true) := by
  have hxy := xyFacts
  simp only [Bool.and_eq_true] at hxy
  exact ⟨validP, validA, tauSift, ⟨hxy.1.1, hxy.1.2, hxy.2⟩, count, normOK, centA⟩

end CertificateChecks.KernelSpor.PSp45

end
