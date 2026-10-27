module

public import Certificates.Kernel.SporSch.Ly.FiveLanesData
public import Certificates.Kernel.SporSch.Ly.BS18009
public import CFSG.RankThree.Native.LyFiveCheckInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LyFL

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy CFSG.KC.LyFiveLane
open CFSG.RankThree.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
open CertificateChecks.KernelSporSch.LyBS CertificateChecks.KernelSporSch.LyBSF

local notation "U" X:max => unpackL 111 12 1332 X

theorem powE {X : Nat} (hX : vld X = true) (e : Nat) :
    powM 5 111 (U X) e = U (pw X e) ∧ vld (pw X e) = true :=
  powM_eq consts (hv hX) e

theorem forceL_eq (y : Nat) (k : Nat → List Nat) : forceL y k = k y := by
  cases y <;> rfl

@[expose] def Rep (r : Array (Array (Array Nat))) (L : List Nat) : Prop :=
  r.size = 65 ∧ L.length = 65 ∧ ∀ i < 65, r[i]! = U (L.getD i 0) ∧ vld (L.getD i 0) = true

theorem arr_set_get {r : Array (Array (Array Nat))} {k t : Nat} (hk : k < r.size) (ht : t < r.size)
    (v : Array (Array Nat)) : (r.set! k v)[t]! = if t = k then v else r[t]! := by
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ t (by simpa using ht), getElem!_pos r t ht]
  by_cases h : t = k
  · subst h; simp [Array.getElem_setIfInBounds, hk]
  · rw [if_neg h, Array.getElem_setIfInBounds_ne ht (Ne.symm h)]

theorem list_set_getD {L : List Nat} {k t : Nat} (hk : k < L.length) (v : Nat) :
    (L.set k v).getD t 0 = if t = k then v else L.getD t 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases h : t = k
  · subst h; simp [hk]
  · simp [h, Ne.symm h]

theorem rep_set {r : Array (Array (Array Nat))} {L : List Nat} (h : Rep r L) {k : Nat} (hk : k < 65)
    {v : Nat} (hv' : vld v = true) : Rep (r.set! k (U v)) (L.set k v) := by
  obtain ⟨hs, hl, hr⟩ := h
  refine ⟨by simp [hs], by simp [hl], fun i hi => ?_⟩
  rw [arr_set_get (by omega) (by omega), list_set_getD (by omega)]
  by_cases e : i = k
  · simp [e, hv']
  · simp only [e, if_false]
    exact hr i hi

theorem rep_step {r : Array (Array (Array Nat))} {L : List Nat} (h : Rep r L) (ins : FiveIns)
    (hi : insIdxOK 65 ins = true) : Rep (fiveStepArr r ins) (stepL mul pw L ins) := by
  cases ins with
  | mu i j k =>
    simp only [insIdxOK, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨hi, hj⟩, hk⟩ := hi
    obtain ⟨ri, vi⟩ := h.2.2 i hi
    obtain ⟨rj, vj⟩ := h.2.2 j hj
    simp only [fiveStepArr, stepL, forceL_eq]
    rw [ri, rj, mulE vi vj]
    exact rep_set h hk (mulV vi vj)
  | pwr e i k =>
    simp only [insIdxOK, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨hi, hk⟩ := hi
    obtain ⟨ri, vi⟩ := h.2.2 i hi
    simp only [fiveStepArr, stepL, forceL_eq]
    rw [ri, (powE vi e).1]
    exact rep_set h hk (powE vi e).2

theorem rep_run : ∀ (prog : List FiveIns) {r : Array (Array (Array Nat))} {L : List Nat},
    Rep r L → CFSG.KC.LyFiveLane.insOK 65 prog = true → Rep (fiveRunArr prog r) (runL mul pw prog L)
  | [], _, _, h, _ => h
  | ins :: prog, r, L, h, hp => by
    simp only [CFSG.KC.LyFiveLane.insOK, List.all_cons, Bool.and_eq_true] at hp
    exact rep_run prog (rep_step h ins hp.1) hp.2

theorem rep_init : Rep fiveInitArr R0 := by
  have h0 : Rep (Array.replicate 65 (idM 111)) (List.replicate 65 ONE) := by
    refine ⟨by simp, by simp, fun i hi => ?_⟩
    rw [getElem!_pos _ i (by simpa using hi), Array.getElem_replicate,
      List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_replicate, idE]
    exact ⟨rfl, vOne⟩
  have h1 := rep_set h0 (k := 1) (by norm_num) vA
  have h2 := rep_set h1 (k := 2) (by norm_num) vB
  unfold fiveInitArr R0
  rw [matA_eq, matB_eq]
  exact h2

theorem regs_rep : Rep lyFiveRegsArr (runL mul pw lyFiveProg R0) :=
  rep_run lyFiveProg rep_init idx

theorem reg_eq {k : Nat} (hk : k < 65) {X : Nat} (h : (runL mul pw lyFiveProg R0).getD k 0 = X) :
    lyFiveRegsArr[k]! = U X ∧ vld X = true := by
  have := regs_rep.2.2 k hk
  rw [h] at this
  exact this

theorem run12 : (runL mul pw lyFiveProg R0).getD 1 0 = D.AA ∧
    (runL mul pw lyFiveProg R0).getD 2 0 = D.BB := by
  have h := run
  unfold runOK at h
  generalize runL mul pw lyFiveProg R0 = r at h ⊢
  beta_reduce at h
  obtain ⟨h1, h2⟩ := andOf h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩

theorem run1 : (runL mul pw lyFiveProg R0).getD 1 0 = D.AA := run12.1

theorem run2 : (runL mul pw lyFiveProg R0).getD 2 0 = D.BB := run12.2

theorem aa_eq : lyFiveAArr = U D.AA := (reg_eq (by norm_num) run1).1
theorem vAA : vld D.AA = true := (reg_eq (by norm_num) run1).2
theorem bb_eq : lyFiveBArr = U D.BB := (reg_eq (by norm_num) run2).1
theorem vBB : vld D.BB = true := (reg_eq (by norm_num) run2).2

theorem pw_ai : pw D.AA 24 = D.AI := Nat.eq_of_beq_eq_true powAI
theorem pw_bi : pw D.BB 7 = D.BI := Nat.eq_of_beq_eq_true powBI
theorem pw_x : pw D.AA 5 = D.XX := Nat.eq_of_beq_eq_true powX

theorem ai_eq : lyFiveAiArr = U D.AI := by
  unfold lyFiveAiArr; rw [aa_eq, (powE vAA 24).1, pw_ai]
theorem vAI : vld D.AI = true := by rw [← pw_ai]; exact (powE vAA 24).2
theorem bi_eq : lyFiveBiArr = U D.BI := by
  unfold lyFiveBiArr; rw [bb_eq, (powE vBB 7).1, pw_bi]
theorem vBI : vld D.BI = true := by rw [← pw_bi]; exact (powE vBB 7).2
theorem x_eq : lyFiveXArr = U D.XX := by
  unfold lyFiveXArr; rw [aa_eq, (powE vAA 5).1, pw_x]
theorem vXX : vld D.XX = true := by rw [← pw_x]; exact (powE vAA 5).2

theorem letter_eq (z : Int) : fiveLetterArr z = U (LT z) ∧ vld (LT z) = true := by
  unfold fiveLetterArr LT
  by_cases h1 : z = 1
  · simp only [h1, if_true]; exact ⟨aa_eq, vAA⟩
  by_cases h2 : z = 2
  · simp only [h2, if_true, show ¬ (2 : Int) = 1 by decide, if_false]; exact ⟨bb_eq, vBB⟩
  by_cases h3 : z = -1
  · simp only [h3, if_true, show ¬ (-1 : Int) = 1 by decide, show ¬ (-1 : Int) = 2 by decide,
      if_false]
    exact ⟨ai_eq, vAI⟩
  · simp only [h1, h2, h3, if_false]; exact ⟨bi_eq, vBI⟩

theorem foldl_eq : ∀ (w : List Int) {M : Array (Array Nat)} {X : Nat}, M = U X → vld X = true →
    w.foldl (fun acc z => mulM 5 111 acc (fiveLetterArr z)) M =
      U (w.foldl (fun acc z => mul acc (LT z)) X) ∧
    vld (w.foldl (fun acc z => mul acc (LT z)) X) = true
  | [], _, _, hM, hX => ⟨hM, hX⟩
  | z :: w, M, X, hM, hX => by
    simp only [List.foldl_cons]
    obtain ⟨lz, vz⟩ := letter_eq z
    refine foldl_eq w ?_ (mulV hX vz)
    rw [hM, lz, mulE hX vz]

theorem word_eq (w : List Int) : fiveWordArr w = U (wordL w) ∧ vld (wordL w) = true :=
  foldl_eq w idE vOne

theorem v_eq (i : Fin 4) : lyFiveVArr[i.val]! = U (V i.val) ∧ vld (V i.val) = true := by
  have e : lyFiveVArr[i.val]! = fiveWordArr (lyFiveVWords i) := by
    unfold lyFiveVArr
    rw [getElem!_pos _ i.val (by simp), Array.getElem_ofFn]
  rw [e]
  fin_cases i
  · have := word_eq (lyFiveVWords 0); rw [Nat.eq_of_beq_eq_true word0] at this; exact this
  · have := word_eq (lyFiveVWords 1); rw [Nat.eq_of_beq_eq_true word1] at this; exact this
  · have := word_eq (lyFiveVWords 2); rw [Nat.eq_of_beq_eq_true word2] at this; exact this
  · have := word_eq (lyFiveVWords 3); rw [Nat.eq_of_beq_eq_true word3] at this; exact this

theorem nf_eq (c : Nat) (e : Fin 4 → Nat) : fiveNFDirect c e = U (nfL c e) ∧ vld (nfL c e) = true := by
  obtain ⟨r0, v0⟩ := v_eq 0
  obtain ⟨r1, v1⟩ := v_eq 1
  obtain ⟨r2, v2⟩ := v_eq 2
  obtain ⟨r3, v3⟩ := v_eq 3
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at r0 v0 r1 v1 r2 v2
  have e3 : ((3 : Fin 4) : Nat) = 3 := rfl
  rw [e3] at r3 v3
  obtain ⟨p3, q3⟩ := powE v3 (e 3)
  obtain ⟨p2, q2⟩ := powE v2 (e 2)
  obtain ⟨p1, q1⟩ := powE v1 (e 1)
  obtain ⟨p0, q0⟩ := powE v0 (e 0)
  obtain ⟨px, qx⟩ := powE vXX c
  unfold fiveNFDirect nfL
  rw [r0, r1, r2, r3, x_eq, p3, p2, p1, p0, px, mulE q3 q2, mulE (mulV q3 q2) q1,
    mulE (mulV (mulV q3 q2) q1) q0, mulE (mulV (mulV (mulV q3 q2) q1) q0) qx]
  exact ⟨rfl, mulV (mulV (mulV (mulV q3 q2) q1) q0) qx⟩

end CertificateChecks.KernelSporSch.LyFL

end
