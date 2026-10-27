module

public import Certificates.Kernel.Sporadic.Fi22.Q450106K
public import Certificates.Kernel.Sporadic.Fi22.Perf450108
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Q450106

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.FischerOddCore CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
open CertificateChecks.KernelSpor
open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

@[expose] def S1 : Array (Array Nat) := Array.ofFn (n := 10) fun h => genArr h
@[expose] def Si1 : Array (Array Nat) := S1.map (invCand 3510)
@[expose] def qa1 : Array (Array Nat) :=
  Array.ofFn (n := 10) fun j => wordA 3510 S1 Si1 (qWords.getD j [])

theorem checkQ_unfold : checkQ () =
    (qWordsOK && relOK t1Arr qa1 && Fi22TwoB.commOK t1Arr qa1 && conjOK S1 Si1 t1Arr qa1 &&
      centOK S1 t1Arr) := rfl

theorem q_parts : Fi22X.cn T = true ∧ Fi22X.cn ID = true ∧
    (∀ h < 10, permOK 3510 12 (mask 12) (3510 * 12) (CG h) (CGI h) = true ∧
      Fi22X.cn (CG h) = true ∧ Fi22X.cn (CGI h) = true) ∧
    (∀ j < 10, lettersK 10 (qWords.getD j []) = true ∧ Fi22X.cn (QD j) = true ∧
      Nat.beq (wordK 3510 12 (mask 12) ID CG CGI (qWords.getD j [])) (QD j) = true) := by
  have h := q_ok
  unfold qK at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun k hk => ?_, fun j hj => ?_⟩
  · obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (allN_spec h3 k hk)
    obtain ⟨b, c⟩ := (bAnd_iff _ _).1 b
    exact ⟨a, b, c⟩
  · obtain ⟨a, b⟩ := (bAnd_iff _ _).1 (allN_spec h4 j hj)
    obtain ⟨b, c⟩ := (bAnd_iff _ _).1 b
    exact ⟨a, b, c⟩

theorem cT : Fi22X.cn T = true := q_parts.1
theorem cID : Fi22X.cn ID = true := q_parts.2.1
theorem cCG {h : Nat} (hh : h < 10) : Fi22X.cn (CG h) = true := (q_parts.2.2.1 h hh).2.1
theorem cCGI {h : Nat} (hh : h < 10) : Fi22X.cn (CGI h) = true := (q_parts.2.2.1 h hh).2.2
theorem cQD {j : Nat} (hj : j < 10) : Fi22X.cn (QD j) = true := (q_parts.2.2.2 j hj).2.1

theorem permCG : allN 10 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (CG j) (CGI j)) = true :=
  allN_of_forall fun j hj => (q_parts.2.2.1 j hj).1

theorem id_eq : idA 3510 = unpack 3510 12 ID := idA_eq Fi22W.szOK'

theorem t_eq : t1Arr = unpack 3510 12 T := Fi22E2067.ext_eq (L := 22) (by norm_num)

theorem S_bind : S1.size = 10 ∧ ∀ j < 10, S1[j]! = unpack 3510 12 (CG j) := by
  refine ⟨by simp [S1], fun j hj => ?_⟩
  rw [S1, Perf450108.get_ofFn _ hj]
  have e : cl j = cLine j := by interval_cases j <;> rfl
  rw [CG, e]
  exact N2070.cent_eq (by interval_cases j <;> simp [cLine])

theorem Si_eq : Si1 = rawInvs 3510 S1 := rfl

theorem Si_get {k : Nat} (hk : k < 10) : Si1[k]! = unpack 3510 12 (CGI k) := by
  have e : Si1[k]! = invCand 3510 S1[k]! := by
    rw [getElem!_pos _ k (by simp [Si1, S_bind.1]; omega),
      getElem!_pos S1 k (by rw [S_bind.1]; omega)]
    simp [Si1]
  rw [e, S_bind.2 k hk]
  exact (invEqK_sound (q_parts.2.2.1 k hk).1).1

theorem qa_get {j : Nat} (hj : j < 10) : qa1[j]! = unpack 3510 12 (QD j) := by
  rw [qa1, Perf450108.get_ofFn _ hj]
  change wordA 3510 S1 Si1 (qWords.getD j []) = _
  obtain ⟨hl, -, hb⟩ := q_parts.2.2.2 j hj
  rw [Si_eq, Perf450108.wordG_eq S_bind permCG Fi22W.szOK' hl]
  exact congrArg (unpack 3510 12) (Nat.eq_of_beq_eq_true hb)

theorem tp_eq (b : Bool) : tPowA t1Arr b = unpack 3510 12 (tp b) ∧ Fi22X.cn (tp b) = true := by
  cases b
  · exact ⟨id_eq, cID⟩
  · exact ⟨t_eq, cT⟩

theorem lt_cn {a : Nat} (ha : Fi22X.cn a = true) {i : Nat} (hi : i < 3510) :
    pg 12 (mask 12) a i < 3510 := by
  have h' : bAnd(Nat.beq (Nat.shiftRight a (3510 * 12)) (nat_lit 0),
      allN 3510 (fun i => Nat.blt (pg 12 (mask 12) a i) 3510)) = true := ha
  have h := allN_spec ((bAnd_iff _ _).1 h').2 i hi
  rw [Nat.blt_eq] at h
  exact h

theorem id_comp {a : Nat} (ha : Fi22X.cn a = true) :
    compA 3510 (idA 3510) (unpack 3510 12 a) = unpack 3510 12 a := by
  apply Array.ext
  · simp [compA, CFSG.KS.Raw.unpack]
  · intro i h1 h2
    have hi : i < 3510 := by simpa [compA] using h1
    have hx := lt_cn ha hi
    simp only [compA, Array.getElem_ofFn, Fi22W.get_eq_of_cn ha]
    rw [idA, getElem!_pos _ _ (by simpa using hx), Array.getElem_ofFn]
    simp [CFSG.KS.Raw.unpack]

theorem sN (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem monL_cons (v i : Nat) (l : List Nat) : monL v (i :: l) =
    Bool.rec (motive := fun _ => Nat) (monL v l) (Fi22X.c (QD i) (monL v l)) (Nat.testBit v i) :=
  sN (monL v l) (fun a => Bool.rec (motive := fun _ => Nat) a (Fi22X.c (QD i) a) (Nat.testBit v i))

theorem monL_eq (v : Nat) : ∀ l : List Nat, (∀ i ∈ l, i < 10) →
    prodA (l.map fun i => if v.testBit i then qa1[i]! else idA 3510) = unpack 3510 12 (monL v l) ∧
      Fi22X.cn (monL v l) = true
  | [], _ => ⟨id_eq, cID⟩
  | i :: l, hl => by
    obtain ⟨ih, cih⟩ := monL_eq v l fun x hx => hl x (List.mem_cons_of_mem _ hx)
    have hi : i < 10 := hl i List.mem_cons_self
    rw [monL_cons]
    simp only [List.map_cons, prodA]
    rw [ih]
    cases hb : v.testBit i
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨id_comp cih, cih⟩
    · simp only [↓reduceIte]
      rw [qa_get hi]
      exact ⟨Fi22X.comp_eq (cQD hi) cih, Fi22X.cn_c (cQD hi) cih⟩

theorem mon_eq (v : Nat) : monA qa1 v = unpack 3510 12 (monL v L10) ∧
    Fi22X.cn (monL v L10) = true := by
  have e : (List.ofFn fun i : Fin 10 => if v.testBit i then qa1[(i : Nat)]! else idA 3510) =
      L10.map fun i => if v.testBit i then qa1[i]! else idA 3510 := by
    simp [List.ofFn_succ, L10]
  unfold monA
  rw [e]
  exact monL_eq v L10 (by decide)

theorem nf_eq (code : Nat) : nfA t1Arr qa1 code = unpack 3510 12 (nfK code) ∧
    Fi22X.cn (nfK code) = true := by
  obtain ⟨tp1, tp2⟩ := tp_eq (code.testBit 10)
  obtain ⟨m1, m2⟩ := mon_eq code
  refine ⟨?_, Fi22X.cn_c tp2 m2⟩
  unfold nfA
  rw [tp1, m1]
  exact Fi22X.comp_eq tp2 m2

theorem rel : relOK t1Arr qa1 = true := by
  have hp := rel_ok
  unfold relK at hp
  simp only [Bool.and_eq_true, and_assoc] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  unfold relOK
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range]
  refine ⟨⟨?_, ?_⟩, fun j hj => ⟨?_, ?_⟩⟩
  · rw [t_eq, id_eq, Fi22X.comp_eq cT cT]
    exact Fi22X.eqA_of (Fi22X.cn_c cT cT) cID h1
  · rw [t_eq, id_eq, eqA_unpack cT cID]
    simpa using h2
  · obtain ⟨a, -⟩ := (bAnd_iff _ _).1 (allN_spec h3 j hj)
    rw [t_eq, qa_get hj, Fi22X.comp_eq cT (cQD hj), Fi22X.comp_eq (cQD hj) cT]
    exact Fi22X.eqA_of (Fi22X.cn_c cT (cQD hj)) (Fi22X.cn_c (cQD hj) cT) a
  · obtain ⟨-, b⟩ := (bAnd_iff _ _).1 (allN_spec h3 j hj)
    rw [id_eq, qa_get hj, Fi22X.comp_eq (cQD hj) (cQD hj)]
    exact Fi22X.eqA_of (Fi22X.cn_c (cQD hj) (cQD hj)) cID b

theorem comm_all {i : Nat} (hi : i < 10) : commK i = true := by
  interval_cases i
  exacts [comm0, comm1, comm2, comm3, comm4, comm5, comm6, comm7, comm8, comm9]

theorem conj_all {k : Nat} (hk : k < 10) : conjK k = true := by
  interval_cases k
  exacts [conj0, conj1, conj2, conj3, conj4, conj5, conj6, conj7, conj8, conj9]

theorem comm : Fi22TwoB.commOK t1Arr qa1 = true := by
  unfold Fi22TwoB.commOK
  simp only [List.all_eq_true, List.mem_range]
  intro i hi j hj
  have h := allN_spec (comm_all hi) j hj
  obtain ⟨tp1, tp2⟩ := tp_eq (cBit i j)
  rw [qa_get hi, qa_get hj, tp1, Fi22X.comp_eq (cQD hi) (cQD hj), Fi22X.comp_eq (cQD hj) (cQD hi),
    Fi22X.comp_eq (Fi22X.cn_c (cQD hj) (cQD hi)) tp2]
  exact Fi22X.eqA_of (Fi22X.cn_c (cQD hi) (cQD hj)) (Fi22X.cn_c (Fi22X.cn_c (cQD hj) (cQD hi)) tp2) h

theorem conj : conjOK S1 Si1 t1Arr qa1 = true := by
  unfold conjOK
  simp only [List.all_eq_true, List.mem_range]
  intro k hk j hj
  have h := allN_spec (conj_all hk) j hj
  obtain ⟨n1, n2⟩ := nf_eq (actCodes.getD (10 * k + j) 0)
  rw [S_bind.2 k hk, Si_get hk, qa_get hj, n1, Fi22X.comp_eq (cCG hk) (cQD hj),
    Fi22X.comp_eq (Fi22X.cn_c (cCG hk) (cQD hj)) (cCGI hk)]
  exact Fi22X.eqA_of (Fi22X.cn_c (Fi22X.cn_c (cCG hk) (cQD hj)) (cCGI hk)) n2 h

theorem cent : centOK S1 t1Arr = true := by
  unfold centOK
  simp only [List.all_eq_true, List.mem_range]
  intro k hk
  have h := allN_spec cent_ok k hk
  rw [S_bind.2 k hk, t_eq, Fi22X.comp_eq (cCG hk) cT, Fi22X.comp_eq cT (cCG hk)]
  exact Fi22X.eqA_of (Fi22X.cn_c (cCG hk) cT) (Fi22X.cn_c cT (cCG hk)) h

theorem words : qWordsOK = true := by decide +kernel

theorem check : checkQ () = true := by
  rw [checkQ_unfold, words, rel, comm, conj, cent]
  rfl

end CertificateChecks.KernelSpor.Q450106

end
