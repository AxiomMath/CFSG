
module

public import Certificates.Kernel.SporSch.Co2M.ThirdCnt
public import CFSG.Sporadic.Co2Schreier.ThirdChainBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.KernelSporSch.Co2M

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Co2M CFSG.KS.Co2Third
open CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.Sporadic.Co2Cert CFSG.Monster.B.Mathieu

abbrev S3 : Array (Array ℕ) := extendArrs aArrs witRec.third.strongDerivations

set_option maxRecDepth 100000 in
theorem ds_facts : witRec.third.strongDerivations.length = 28 ∧
    MatRep.extOK 2 witRec.third.strongDerivations = true ∧
    extWordsOK 2 witRec.third.strongDerivations = true ∧ thB.size = 13 ∧
    ∀ t < 13, thB[t]! < 2300 := by
  decide +kernel

theorem thB_size' : thB.size = 13 := ds_facts.2.2.2.1

theorem thB_len : witRec.third.baseIndices.length = 13 := by
  have := thB_size'
  simpa using this

theorem thB_lt' {t : ℕ} (ht : t < 13) : thB[t]! < 2300 := ds_facts.2.2.2.2 t ht

theorem bpt_val' {t : ℕ} (ht : t < 13) : (bpt t : ℕ) = thB[t]! :=
  Nat.mod_eq_of_lt (thB_lt' ht)

theorem t3_rep : MatRep.RepT 22 co2PackedVecs S3 t3T :=
  MatRep.repT_extend good V_size mmK_eq I22_eq _ aRep (by
    change MatRep.extOK 2 witRec.third.strongDerivations = true
    exact ds_facts.2.1)

theorem bind_t3 {k : ℕ} (hk : k < 30) : bindK (PV 0) (Co2T3.S k) (t3T.getD k (0, 0)).1
    (t3T.getD k (0, 0)).2 = true := by
  rcases (by omega : k < 10 ∨ (10 ≤ k ∧ k < 20) ∨ (20 ≤ k ∧ k < 30)) with h | h | h
  · exact allN_spec bind_t3a k h
  · have := allN_spec bind_t3b (k - 10) (by omega)
    rwa [show Nat.add 10 (k - 10) = k from by rw [Nat.add_eq]; omega] at this
  · have := allN_spec bind_t3c (k - 20) (by omega)
    rwa [show Nat.add 20 (k - 20) = k from by rw [Nat.add_eq]; omega] at this

theorem mem_foldl_steps (base : Array ℕ) (j : ℕ) (s : Array ℕ) :
    ∀ (l : List (Array ℕ)) (acc : Array (Array ℕ)),
    s ∈ l.foldl (fun acc g => if fixesFirst base g j then (acc.push g).push (invCand 2300 g)
      else acc) acc ↔
      s ∈ acc ∨ ∃ g ∈ l, fixesFirst base g j = true ∧ (s = g ∨ s = invCand 2300 g)
  | [], acc => by simp
  | g :: l, acc => by
    rw [List.foldl_cons, mem_foldl_steps base j s l]
    simp only [List.mem_cons, exists_eq_or_imp]
    by_cases hg : fixesFirst base g j = true
    · rw [if_pos hg]
      simp only [Array.mem_push, hg, true_and, or_assoc]
    · rw [if_neg hg]
      simp only [hg, Bool.false_eq_true, false_and, false_or]

theorem mem_thirdSteps_iff {S : Array (Array ℕ)} {base : Array ℕ} {j : ℕ} {s : Array ℕ} :
    s ∈ thirdSteps S base j ↔ ∃ i < S.size, fixesFirst base S[i]! j = true ∧
      (s = S[i]! ∨ s = invCand 2300 S[i]!) := by
  rw [thirdSteps, ← Array.foldl_toList, mem_foldl_steps]
  simp only [List.mem_toArray, List.not_mem_nil, false_or, Array.mem_toList_iff]
  constructor
  · rintro ⟨g, hg, h⟩
    obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hg
    exact ⟨i, hi, by rw [getElem!_pos S i hi]; exact h.1, by rw [getElem!_pos S i hi]; exact h.2⟩
  · rintro ⟨i, hi, h⟩
    rw [getElem!_pos S i hi] at h
    exact ⟨_, Array.getElem_mem hi, h⟩

theorem mem_rawSteps_iff {S : Array (Array ℕ)} {base : Array ℕ} {j : ℕ} {s : Array ℕ} :
    s ∈ rawSteps 2300 S base j ↔ s ∈ thirdSteps S base j := by
  rw [mem_thirdSteps_iff, rawSteps, levelSteps, levelIdx]
  simp only [Array.mem_append, List.mem_toArray, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro (⟨i, ⟨hi, hf⟩, rfl⟩ | ⟨i, ⟨hi, hf⟩, rfl⟩)
    · exact ⟨i, hi, hf, Or.inl rfl⟩
    · refine ⟨i, hi, hf, Or.inr ?_⟩
      rw [rawInvs, getElem!_pos _ i (by simpa using hi), Array.getElem_map, ← getElem!_pos S i hi]
  · rintro ⟨i, hi, hf, rfl | rfl⟩
    · exact Or.inl ⟨i, ⟨hi, hf⟩, rfl⟩
    · refine Or.inr ⟨i, ⟨hi, hf⟩, ?_⟩
      rw [rawInvs, getElem!_pos _ i (by simpa using hi), Array.getElem_map, ← getElem!_pos S i hi]

theorem fixesFirst_mono {base t : Array ℕ} {j j' : ℕ} (hjj : j ≤ j')
    (h : fixesFirst base t j' = true) : fixesFirst base t j = true :=
  allLt_iff.2 fun k hk => allLt_iff.1 h k (by omega)

theorem fix_of_fixesFirst {t : Array ℕ} {g : Equiv.Perm (Fin 2300)} (hg : Rep 2300 t g) {j : ℕ}
    (hj : j ≤ 13) (h : fixesFirst thB t j = true) : ∀ i < j, g (bpt i) = bpt i := by
  intro i hi
  apply Fin.ext
  rw [← hg (bpt i), bpt_val' (by omega)]
  have := allLt_iff.1 h i hi
  simpa using this

@[expose] def Gj (j : ℕ) : Subgroup (Equiv.Perm (Fin 2300)) :=
  Subgroup.closure {g | ∃ s ∈ thirdSteps S3 thB j, Rep 2300 s g}

theorem Gj_mono {j j' : ℕ} (hjj : j ≤ j') : Gj j' ≤ Gj j := by
  refine Subgroup.closure_mono ?_
  rintro g ⟨s, hs, hg⟩
  obtain ⟨i, hi, hf, hs'⟩ := mem_thirdSteps_iff.1 hs
  exact ⟨s, mem_thirdSteps_iff.2 ⟨i, hi, fixesFirst_mono hjj hf, hs'⟩, hg⟩

theorem thL_get {j : ℕ} (hj : j < 13) : thL[j]! = orbitTr (thirdSteps S3 thB j) thB[j]! := by
  have hs : thL.size = 13 := by simp [thL, thirdLevels, thB_len]
  rw [getElem!_pos thL j (by rw [hs]; exact hj)]
  simp [thL, thirdLevels]

theorem thL_size' : thL.size = 13 := by simp [thL, thirdLevels, thB_len]

theorem recF {j : ℕ} (hj : j < 13) :
    RecFacts 2300 12 Co2T3.S Co2T3.SI 30 (pg 12 (mask 12) Co2T3.BP j) (t3St j) (Co2T3.LR j) :=
  recFacts_of (Co2T3.ho.1 j hj) (fun s hs => Co2T3.ho.2 j hj s hs) (by norm_num)

theorem rawStep_mem {j l : ℕ} (hl : l < (rawSteps 2300 S3 thB j).size) :
    (rawSteps 2300 S3 thB j)[l]! ∈ thirdSteps S3 thB j := by
  rw [← mem_rawSteps_iff, getElem!_pos _ l hl]
  exact Array.getElem_mem hl

theorem u_get {x : ℕ} (hx : x < 2300) : uArr[x]! = pg 12 (mask 12) (UP 0) x := by
  have h2 := (bindK_sound good V_size (fun i hi => V_get hi) rfl bind_u).1
  rw [uRep.1, ← h2, unpack_get hx]

theorem base_get {t : ℕ} (ht : t < 13) : thB[t]! = pg 12 (mask 12) Co2T3.BP t :=
  Nat.eq_of_beq_eq_true (allN_spec base_ok t ht)

theorem u_fixK : fixesFirst thB uArr 12 = true := by
  refine allLt_iff.2 fun t ht => ?_
  rw [base_get (by omega), u_get (by rw [← base_get (by omega)]; exact thB_lt' (by omega))]
  exact allN_spec ufix_ok t ht

end CertificateChecks.KernelSporSch.Co2M
