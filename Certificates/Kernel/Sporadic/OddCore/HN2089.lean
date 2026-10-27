module

public import Certificates.Kernel.Sporadic.OddCore.HN2089K
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.BfsPinSound
import Mathlib.Tactic.IntervalCases
import CFSG.Sporadic.Schreier.ONPermArr
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.HN2089

open CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native CFSG.Sporadic.HNOddCore.InvData
open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Monster.B.Co2.Native CFSG.KC.BfsPin CertificateChecks.KernelSpor.HND

theorem listPK_spec {w P : Nat} :
    ∀ (L : List Nat) (i : Nat), listPK w P L i = true →
      ∀ j < L.length, L[j]! = pg w (mask w) P (i + j)
  | [], _, _, j, hj => absurd hj (by simp)
  | x :: xs, i, h, j, hj => by
    unfold listPK at h
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
    cases j with
    | zero => simpa using Nat.eq_of_beq_eq_true h1
    | succ j =>
      have := listPK_spec xs (i + 1) h2 j (by simpa using hj)
      simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

theorem toArray_unpack {n w P : Nat} {L : List Nat} (hl : L.length = n)
    (h : listPK w P L 0 = true) : L.toArray = unpack n w P := by
  apply Array.ext
  · simp [unpack, hl]
  · intro j h1 h2
    have hj : j < L.length := by simpa using h1
    have e := listPK_spec L 0 h j hj
    rw [← getElem!_pos L.toArray j h1]
    simp only [List.getElem!_toArray] at e ⊢
    simp [unpack, e]

theorem pcomp_eq (n : Nat) (t u : Array Nat) : pcomp n t u = compA n t u := rfl
theorem pid_eq (n : Nat) : pid n = idA n := rfl
theorem peq_eq (n : Nat) (t u : Array Nat) : peq n t u = eqA n t u := rfl
theorem pinvCand_eq (n : Nat) (t : Array Nat) : pinvCand n t = invCand n t := rfl
theorem pisInv_eq (n : Nat) (t r : Array Nat) : pisInv n t r = isInvA n t r := rfl

theorem pword_eq_wordA (n : Nat) (S Si : Array (Array Nat)) :
    ∀ w : List Int, pword n S Si w = wordA n S Si w
  | [] => rfl
  | l :: w => by
    change pcomp n (pletter S Si l) (pword n S Si w) = compA n (letterA S Si l) (wordA n S Si w)
    rw [pword_eq_wordA n S Si w]
    rfl

theorem pinvs_eq_rawInvs (n : Nat) (S : Array (Array Nat)) :
    pinvs n S = CFSG.Certificates.Native.rawInvs n S := rfl

theorem pinvs_get {n g : Nat} {S : Array (Array Nat)} (hg : g < S.size) :
    (pinvs n S)[g]! = pinvCand n S[g]! := by
  unfold pinvs
  rw [getElem!_pos _ g (by simpa using hg), getElem!_pos _ g hg]
  simp

theorem lines_get {E : List (List Nat)} (i : Nat) :
    ((E.map List.toArray).toArray)[i]! = (E.getD i []).toArray := by
  by_cases h : i < E.length
  · have e : E.getD i [] = E[i] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
    rw [getElem!_pos _ i (by simpa using h), e]
    simp
  · have e : E.getD i [] = [] := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : E.length ≤ i),
        Option.getD_none]
    rw [getElem!_neg _ i (by simpa using h), e]
    rfl

theorem lines_bind {n w k : Nat} {P : Nat → Nat} {E : List (List Nat)} (hk : E.length = k)
    (h : allN k (fun g => bAnd(Nat.beq (E.getD g []).length n,
      listPK w (P g) (E.getD g []) 0)) = true) :
    ((E.map List.toArray).toArray).size = k ∧
      ∀ g < k, ((E.map List.toArray).toArray)[g]! = unpack n w (P g) := by
  refine ⟨by simp [hk], fun g hg => ?_⟩
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec h g hg)
  rw [lines_get]
  exact toArray_unpack (Nat.eq_of_beq_eq_true h1) h2

theorem s_get : s4Perms.size = 11 ∧ ∀ g < 11, s4Perms[g]! = unpack 800 10 (HQS g) := by
  rw [s4_eq]
  exact lines_bind (by decide +kernel) sb

theorem q_get : qPerms.size = 8 ∧ ∀ i < 8, qPerms[i]! = unpack 800 10 (HQQ i) := by
  rw [qp_eq]
  exact lines_bind (by decide +kernel) qb

theorem foldl_unpack {n w m : Nat} {Q : Array (Array Nat)} {P : Nat → Nat} (L : List Nat)
    (hQ : ∀ i ∈ L, Q[i]! = unpack n w (P i) ∧ canonK n w (mask w) (n * w) (P i) = true) :
    ∀ a, canonK n w (mask w) (n * w) a = true →
      L.foldl (fun acc i => if m.testBit i then pcomp n acc Q[i]! else acc) (unpack n w a) =
        unpack n w (L.foldl (fun acc i =>
          if m.testBit i then CFSG.KC.Enum.pcomp n w (mask w) acc (P i) else acc) a) := by
  induction L with
  | nil => intro a _; rfl
  | cons i L ih =>
    intro a ha
    have hi := hQ i (by simp)
    have hL : ∀ j ∈ L, Q[j]! = unpack n w (P j) ∧ canonK n w (mask w) (n * w) (P j) = true :=
      fun j hj => hQ j (by simp [hj])
    simp only [List.foldl_cons]
    by_cases hb : m.testBit i = true
    · simp only [hb, ↓reduceIte]
      rw [hi.1, pcomp_eq, compA_unpack ha hi.2]
      exact ih hL _ (canonK_pcomp ha hi.2)
    · simp only [hb, Bool.false_eq_true, ↓reduceIte]
      exact ih hL a ha

theorem b_get : (qbList 800 qPerms).size = 256 ∧
    ∀ m < 256, (qbList 800 qPerms)[m]! = unpack 800 10 (HQB m) := by
  refine ⟨by simp [qbList], fun m hm => ?_⟩
  unfold qbList
  rw [getElem!_pos _ m (by simpa using hm), Array.getElem_ofFn]
  unfold subQ
  rw [q_get.1, pid_eq, ← idK_sound idk]
  rw [foldl_unpack (List.range 8)
    (fun i hi => ⟨q_get.2 i (List.mem_range.1 hi), allN_spec cQ i (List.mem_range.1 hi)⟩)
    (pidn 800 10) cI]
  rw [Nat.eq_of_beq_eq_true (allN_spec bb m hm)]

theorem k_get : colPerms.size = 11 ∧ ∀ g < 11, colPerms[g]! = unpack 256 9 (HQK g) := by
  have hs : colPerms.size = 11 := by simp [colPerms]; rfl
  have hq : qColumns.size = 11 := by simpa [colPerms] using hs
  refine ⟨hs, fun g hg => ?_⟩
  unfold colPerms
  rw [getElem!_pos _ g (by rw [Array.size_map, hq]; exact hg), Array.getElem_map,
    ← getElem!_pos qColumns g (by rw [hq]; exact hg)]
  unfold colPerm unpack
  congr 1
  funext m
  exact Nat.eq_of_beq_eq_true (allN_spec (allN_spec kb g hg) m.val m.isLt)

theorem f_inv : (allBelowN 11 fun g => pisInv 800 s4Perms[g]! (pinvs 800 s4Perms)[g]!) = true := by
  rw [allBelowN_iff]
  intro g hg
  have hp := allN_spec pS g hg
  rw [pinvs_get (by rw [s_get.1]; exact hg), s_get.2 g hg, pisInv_eq, pinvCand_eq,
    invCand_unpack hp]
  exact (invEqK_sound hp).2

theorem f_letters : ∀ i < 8, plettersOK 11 QData.qFlat[i]! = true := by decide +kernel

theorem f_words : (allBelowN 8 fun i => plettersOK 11 QData.qFlat[i]! &&
    peq 800 (pword 800 s4Perms (pinvs 800 s4Perms) QData.qFlat[i]!) qPerms[i]!) = true := by
  rw [allBelowN_iff]
  intro i hi
  rw [Bool.and_eq_true]
  have hw := wordEqK_sound (r := HQQ i) s_get pS (allN_spec wq i hi)
  refine ⟨f_letters i hi, ?_⟩
  have hc := allN_spec cQ i hi
  rw [peq_eq, pword_eq_wordA, pinvs_eq_rawInvs, hw.1, q_get.2 i hi, eqA_unpack hc hc]
  exact Nat.beq_refl _

theorem f_comm : (allBelowN 8 fun i => allBelowN 8 fun j =>
    peq 800 (pcomp 800 qPerms[i]! qPerms[j]!) (pcomp 800 qPerms[j]! qPerms[i]!)) = true := by
  rw [allBelowN_iff]
  intro i hi
  rw [allBelowN_iff]
  intro j hj
  have ci := allN_spec cQ i hi
  have cj := allN_spec cQ j hj
  rw [q_get.2 i hi, q_get.2 j hj]
  simp only [peq_eq, pcomp_eq]
  rw [compA_unpack ci cj, compA_unpack cj ci, eqA_unpack (canonK_pcomp ci cj) (canonK_pcomp cj ci)]
  exact allN_spec (allN_spec cm i hi) j hj

theorem f_sq : (allBelowN 8 fun i => peq 800 (pcomp 800 qPerms[i]! qPerms[i]!) (pid 800)) =
    true := by
  rw [allBelowN_iff]
  intro i hi
  have ci := allN_spec cQ i hi
  rw [q_get.2 i hi]
  simp only [peq_eq, pcomp_eq, pid_eq]
  rw [← idK_sound idk, compA_unpack ci ci, eqA_unpack (canonK_pcomp ci ci) cI]
  exact allN_spec sq i hi

theorem f_qb : (allBelowN 8 fun i => allBelowN 256 fun m =>
    decide (m ^^^ (1 <<< i) < 256) &&
      peq 800 (pcomp 800 qPerms[i]! (qbList 800 qPerms)[m]!)
        (qbList 800 qPerms)[m ^^^ (1 <<< i)]!) = true := by
  rw [allBelowN_iff]
  intro i hi
  rw [allBelowN_iff]
  intro m hm
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec (allN_spec qb2 i hi) m hm)
  have hlt : m ^^^ (1 <<< i) < 256 := Eq.mp Nat.blt_eq h1
  have ci := allN_spec cQ i hi
  have cm' := allN_spec cB m hm
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hlt, ?_⟩
  rw [q_get.2 i hi, b_get.2 m hm, b_get.2 _ hlt]
  simp only [peq_eq, pcomp_eq]
  rw [compA_unpack ci cm', eqA_unpack (canonK_pcomp ci cm') (allN_spec cB _ hlt)]
  exact h2

theorem f_K : (allBelowN 11 fun g => pisInv 256 colPerms[g]! (pinvCand 256 colPerms[g]!) &&
    allBelowN 256 fun m => decide ((colPerms[g]!)[m]! < 256) &&
      peq 800 (pcomp 800 (pinvs 800 s4Perms)[g]! (pcomp 800 (qbList 800 qPerms)[m]! s4Perms[g]!))
        (qbList 800 qPerms)[(colPerms[g]!)[m]!]!) = true := by
  rw [allBelowN_iff]
  intro g hg
  have hpk := allN_spec pK g hg
  have hps := allN_spec pS g hg
  have cs := allN_spec cS g hg
  have csi := allN_spec cSI g hg
  rw [Bool.and_eq_true, k_get.2 g hg, pinvs_get (by rw [s_get.1]; exact hg), s_get.2 g hg]
  refine ⟨?_, ?_⟩
  · rw [pisInv_eq, pinvCand_eq, invCand_unpack hpk]
    exact (invEqK_sound hpk).2
  rw [allBelowN_iff]
  intro m hm
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (allN_spec (allN_spec kc g hg) m hm)
  have hkm : (unpack 256 9 (HQK g))[m]! = pg 9 (mask 9) (HQK g) m := by
    unfold unpack
    rw [getElem!_pos _ m (by simpa using hm)]
    simp
  have hlt : pg 9 (mask 9) (HQK g) m < 256 := Eq.mp Nat.blt_eq h1
  have cb := allN_spec cB m hm
  rw [hkm, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hlt, ?_⟩
  rw [pinvCand_eq, invCand_unpack hps, b_get.2 m hm, b_get.2 _ hlt]
  rw [show pinvS 800 10 (mask 10) (HQS g) = siP g from rfl]
  simp only [peq_eq, pcomp_eq]
  rw [compA_unpack cb cs, compA_unpack csi (canonK_pcomp cb cs),
    eqA_unpack (canonK_pcomp csi (canonK_pcomp cb cs)) (allN_spec cB _ hlt)]
  exact h2

theorem cv_get : ∀ j < 10, (cvGens s4Perms)[j]! = s4Perms[if j < 9 then j else 10]! := by
  intro j hj
  have hs := s_get.1
  unfold cvGens
  rw [getElem!_pos _ j (by simp [hs]; omega)]
  by_cases h : j < 9
  · simp only [h, ↓reduceIte]
    rw [getElem!_pos _ j (by rw [hs]; omega)]
    simp [Array.getElem_push, h, hs]
  · have e : j = 9 := by omega
    subst e
    simp [Array.getElem_push, hs]

theorem cv_O : (cvGens s4Perms).size = 10 ∧
    ∀ j < 10, (cvGens s4Perms)[j]! = unpack 800 10 (HQCV.S j) := by
  refine ⟨by simp [cvGens, s_get.1], fun j hj => ?_⟩
  rw [cv_get j hj, s_get.2 _ (by split <;> omega), Nat.eq_of_beq_eq_true (allN_spec hcv j hj)]

theorem q_O : qPerms.size = 8 ∧ ∀ j < 8, qPerms[j]! = unpack 800 10 (HQQC.S j) :=
  ⟨q_get.1, fun j hj => by rw [q_get.2 j hj, Nat.eq_of_beq_eq_true (allN_spec hqc j hj)]⟩

theorem k_O : colPerms.size = 11 ∧ ∀ j < 11, colPerms[j]! = unpack 256 9 (HQKC.S j) :=
  ⟨k_get.1, fun j hj => by rw [k_get.2 j hj, Nat.eq_of_beq_eq_true (allN_spec hkc j hj)]⟩

theorem base_of {n w nb BP : Nat} {base : List (Fin n)} (hs : (base.map Fin.val).toArray.size = nb)
    (h : allN nb (fun t => Nat.beq (pg w (mask w) BP t) ((base.map Fin.val).toArray[t]!)) = true) :
    (base.map Fin.val).toArray.size = nb ∧
      ∀ t < nb, (base.map Fin.val).toArray[t]! = pg w (mask w) BP t :=
  ⟨hs, fun t ht => (Nat.eq_of_beq_eq_true (allN_spec h t ht)).symm⟩

theorem chCV : chainCheck 800 (cvGens s4Perms) QData.cvWords QData.cvBase QData.cvSizes = true :=
  chainCheck_of cv_O (by decide +kernel) (by decide +kernel) (by simp only [cvD, Array.toArray_toList]) (by norm_num)
    (base_of (by decide +kernel) bCV) HQCV.head HQCV.hl (by decide +kernel) HQCV.hs pCV
    (by decide +kernel)

theorem chQ : chainCheck 800 qPerms QData.qWords QData.qBase QData.qSizes = true :=
  chainCheck_of q_O (by decide +kernel) (by decide +kernel) (by simp only [qD, Array.toArray_toList]) (by norm_num)
    (base_of (by decide +kernel) bQC) HQQC.head HQQC.hl (by decide +kernel) HQQC.hs pQC
    (by decide +kernel)

theorem chK : chainCheck 256 colPerms QData.conjWords QData.conjBase QData.conjSizes = true :=
  chainCheck_of k_O (by decide +kernel) (by decide +kernel) (by simp only [kD, Array.toArray_toList]) (by norm_num)
    (base_of (by decide +kernel) bKC) HQKC.head HQKC.hl (by decide +kernel) HQKC.hs pKC
    (by decide +kernel)

theorem facts2089 : qChecks = true := by
  unfold qChecks qChecksH
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨s_get.1, q_get.1⟩, b_get.1⟩, k_get.1⟩, f_inv⟩, f_words⟩, f_comm⟩, f_sq⟩,
    f_qb⟩, f_K⟩, chCV⟩, chQ⟩, chK⟩

end CertificateChecks.KernelSpor.HN2089

end
