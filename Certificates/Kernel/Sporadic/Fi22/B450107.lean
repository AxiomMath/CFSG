module

public import Certificates.Kernel.Sporadic.Fi22.B450107K
public import Certificates.Kernel.Sporadic.Fi22.Q450106
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.B450107

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.FischerOddCore CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
open CertificateChecks.KernelSpor

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem checkBlocks_unfold : checkBlocks () =
    (blocks45.length == 45 && tauWords.length == 10 && genWords.length == 3 && xyfArr.size == 3 &&
      tauWords.all (lettersOK 3) && genWords.all (lettersOK 10) && qWordsOK &&
      allLt 3 (fun j => isInvA 45 xyfArr[j]! (xyfArr.map (invCand 45))[j]!) &&
      allLt 10 (fun k => isInvA 45 (tauArrs ())[k]! ((tauArrs ()).map (invCand 45))[k]!) &&
      allLt 3 (fun j => eqA 45 (wordA 45 (tauArrs ()) ((tauArrs ()).map (invCand 45))
        (genWords.getD j [])) xyfArr[j]!) &&
      allLt 45 (fun i => decide ((blocks45.getD i []).headD 0 < 3510) &&
        (labelArr ())[(blocks45.getD i []).headD 0]! == i) &&
      allLt 10 (fun k => allLt 3510 fun p =>
        (labelArr ())[(Q450106.S1[k]!)[p]!]! == extGet (tauArrs ())[k]! (labelArr ())[p]!) &&
      allLt 3510 (fun p => (labelArr ())[t1Arr[p]!]! == (labelArr ())[p]!) &&
      allLt 10 (fun j => allLt 3510 fun p =>
        (labelArr ())[(Q450106.qa1[j]!)[p]!]! == (labelArr ())[p]!)) := rfl

theorem lab_all {c : Nat} (hc : c < 10) : labCk c = true := by
  interval_cases c
  exacts [lab0, lab1, lab2, lab3, lab4, lab5, lab6, lab7, lab8, lab9]

theorem gen_all {k : Nat} (hk : k < 10) : genK k = true := by
  interval_cases k
  exacts [gen0, gen1, gen2, gen3, gen4, gen5, gen6, gen7, gen8, gen9]

theorem qfix_all {j : Nat} (hj : j < 10) : qFixK j = true := by
  interval_cases j
  exacts [qfix0, qfix1, qfix2, qfix3, qfix4, qfix5, qfix6, qfix7, qfix8, qfix9]

theorem lab_get {x : Nat} (hx : x < 3510) : (labelArr ())[x]! = pg 6 (mask 6) LAB x := by
  unfold labelArr
  rw [Perf450108.get_ofFn _ hx]
  have h := lab_all (c := x / 351) (by omega)
  unfold labCk at h
  simp only [sB] at h
  have h2 := allN_spec h (x % 351) (Nat.mod_lt _ (by norm_num))
  beta_reduce at h2
  have e : Nat.add (Nat.mul 351 (x / 351)) (x % 351) = x := by
    change 351 * (x / 351) + x % 351 = x
    omega
  rw [e] at h2
  exact Nat.eq_of_beq_eq_true h2

theorem tau_parts : (∀ k < 10, permOK 45 6 (mask 6) (45 * 6) (Perf450108.TK k)
      (Perf450108.inv45 (Perf450108.TK k)) = true ∧ Perf450108.cn45 (Perf450108.TK k) = true) ∧
    (∀ j < 3, Perf450108.cn45 (Perf450108.XY45 j) = true ∧
      lettersK 10 (genWords.getD j []) = true) ∧
    (∀ j < 3, Nat.beq (wordK 45 6 (mask 6) (pidn 45 6) Perf450108.TK
      (fun k => Perf450108.inv45 (Perf450108.TK k)) (genWords.getD j []))
        (Perf450108.XY45 j) = true) := by
  have h := tau_ok
  unfold tauK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun k hk => ?_, fun j hj => (bAnd_iff _ _).1 (allN_spec h2 j hj),
    fun j hj => allN_spec h3 j hj⟩
  obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (allN_spec h1 k hk)
  exact ⟨a, ((bAnd_iff _ _).1 b).1⟩

theorem T_bind : (tauArrs ()).size = 10 ∧
    ∀ k < 10, (tauArrs ())[k]! = unpack 45 6 (Perf450108.TK k) :=
  ⟨by simp [tauArrs], fun _ hk => Perf450108.tau_get hk⟩

theorem permT : allN 10 (fun k => permOK 45 6 (mask 6) (45 * 6) (Perf450108.TK k)
    (Perf450108.inv45 (Perf450108.TK k))) = true :=
  allN_of_forall fun k hk => (tau_parts.1 k hk).1

theorem inv_get (S : Array (Array Nat)) (j : Nat) (hj : j < S.size) :
    (S.map (invCand 45))[j]! = invCand 45 S[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), getElem!_pos S j hj]
  simp

theorem ext_eq (τ m : Nat) : extGet (unpack 45 6 τ) m = extK τ m := by
  unfold extGet extK
  by_cases hm : m < 45
  · have hb : Nat.blt m 45 = true := Nat.blt_eq.mpr hm
    simp only [hm, hb, unpack_getElem!, ↓reduceIte]
  · have hb : Nat.blt m 45 = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hm (Nat.blt_eq.mp h)
    simp only [hm, hb, ↓reduceIte]

theorem fix_of {g : Nat} {a : Array Nat} (ha : a = unpack 3510 12 g) (hg : Fi22X.cn g = true)
    (h : fixK LAB g = true) :
    allLt 3510 (fun p => (labelArr ())[a[p]!]! == (labelArr ())[p]!) = true := by
  rw [CFSG.Monster.B.Co2.allLt_iff]
  intro p hp
  have h1 := allN_spec h p hp
  rw [ha, Fi22W.get_eq_of_cn hg, lab_get (Q450106.lt_cn hg hp), lab_get hp]
  exact beq_iff_eq.mpr (Nat.eq_of_beq_eq_true h1)

theorem words_ok : (blocks45.length == 45 && tauWords.length == 10 && genWords.length == 3 &&
    xyfArr.size == 3 && tauWords.all (lettersOK 3) && genWords.all (lettersOK 10)) = true := by
  decide +kernel

theorem check : checkBlocks () = true := by
  rw [checkBlocks_unfold]
  have hw := words_ok
  simp only [Bool.and_eq_true, and_assoc] at hw ⊢
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := hw
  refine ⟨w1, w2, w3, w4, w5, w6, Q450106.words, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    rw [inv_get _ j (by rw [Perf450108.xyf_bind.1]; exact hj)]
    exact Fi22E2067.isInv_of (Perf450108.xy_eq j hj) (allN_spec Perf450108.rho_parts.2.1 j hj)
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    rw [inv_get _ k (by rw [T_bind.1]; exact hk)]
    exact Fi22E2067.isInv_of (T_bind.2 k hk) (tau_parts.1 k hk).1
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    have hT : (tauArrs ()).map (invCand 45) = rawInvs 45 (tauArrs ()) := rfl
    have hc := (tau_parts.2.1 j hj).1
    rw [hT, Perf450108.wordG_eq T_bind permT Perf450108.rho_parts.1 (tau_parts.2.1 j hj).2,
      Perf450108.xy_eq j hj, Nat.eq_of_beq_eq_true (tau_parts.2.2 j hj), eqA_unpack hc hc]
    exact Nat.beq_refl _
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro i hi
    have h := head_ok
    unfold headK at h
    simp only [sB] at h
    obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (allN_spec h i hi)
    have ha : hd i < 3510 := Nat.blt_eq.mp a
    change (decide (hd i < 3510) && (labelArr ())[hd i]! == i) = true
    rw [lab_get ha]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    exact ⟨ha, Nat.eq_of_beq_eq_true b⟩
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro k hk
    rw [CFSG.Monster.B.Co2.allLt_iff]
    intro p hp
    have h := gen_all hk
    unfold genK at h
    simp only [sB] at h
    unfold labK at h
    have h1 := allN_spec h p hp
    rw [Q450106.S_bind.2 k hk, Fi22W.get_eq_of_cn (Q450106.cCG hk),
      lab_get (Q450106.lt_cn (Q450106.cCG hk) hp), lab_get hp, T_bind.2 k hk, ext_eq]
    exact beq_iff_eq.mpr (Nat.eq_of_beq_eq_true h1)
  · have h := tfix
    unfold tFixK at h
    simp only [sB] at h
    exact fix_of Q450106.t_eq Q450106.cT h
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    have h := qfix_all hj
    unfold qFixK at h
    simp only [sB] at h
    exact fix_of (Q450106.qa_get hj) (Q450106.cQD hj) h

end CertificateChecks.KernelSpor.B450107

end
