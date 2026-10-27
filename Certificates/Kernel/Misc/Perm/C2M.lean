module

public import Certificates.Kernel.Misc.Perm.C2J
public import Certificates.Kernel.Misc.Perm.C2Q

public section

namespace CertificateChecks.KernelMisc.Co2K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.RankThree.Native.F2
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Mathieu (powArr)
open CFSG.Monster.B.Fischer (ArrCert)

theorem good_mmM {A B : ℕ} (hA : ∀ v ∈ co2FiveV, vmul 22 v A ∈ co2FiveV)
    (hB : ∀ v ∈ co2FiveV, vmul 22 v B ∈ co2FiveV) : Good (mmK A B) := by
  rw [hmm]
  exact ⟨maps_mmul hA hB, mmul_lt _ _⟩

theorem compA_maps {A B : ℕ} (hB : ∀ v ∈ co2FiveV, vmul 22 v B ∈ co2FiveV) :
    compA 2300 (permOfMat 22 co2FiveV A) (permOfMat 22 co2FiveV B) =
      permOfMat 22 co2FiveV (mmK B A) := by
  have h := compA_permOfMat (V := co2FiveV) (A := A) hB
  rw [V_size] at h
  rw [h, hmm]

theorem mapsAMI {k : ℕ} (hk : k < 38) : ∀ v ∈ co2FiveV, vmul 22 v (AMI k) ∈ co2FiveV :=
  (amF hk).1.2.1

theorem good_pts {ngen N : ℕ} {GM PM HE HR HL : ℕ → ℕ}
    (hG : ∀ k < ngen, ∀ v ∈ co2FiveV, vmul 22 v (GM k) ∈ co2FiveV)
    (h0 : Nat.beq (PM 0) I22 = true) (hp : ∀ i < N, ptAt ngen N GM PM HE HR HL i = true) :
    ∀ i < N, Good (PM i) :=
  tree_good hd22 sys.lt hmm I22_eq hG (Nat.eq_of_beq_eq_true h0) hp

theorem gQ : ∀ i < 125, Good (PQ i) := good_pts (fun k hk => by
  interval_cases k
  · exact (good_AM (k := 4) (by norm_num)).1
  · exact (good_AM (k := 5) (by norm_num)).1) rootQ ptQ_all

theorem gC0 : ∀ i < 3000, Good (PC0 i) := good_pts (fun k hk => by
  interval_cases k
  · exact (good_AM (k := 2) (by norm_num)).1
  · exact (good_AM (k := 3) (by norm_num)).1) rootC0 ptC0_all

theorem gC1 : ∀ i < 600, Good (PC1 i) := good_pts (fun k hk => by
  interval_cases k
  · exact (good_AM (k := 1) (by norm_num)).1
  · exact (good_AM (k := 6) (by norm_num)).1
  · exact (good_AM (k := 7) (by norm_num)).1) rootC1 ptC1_all

theorem good_GD0 : Good DG0 := by
  rw [DG0]
  exact good_mmM (good_mmM (mapsAMI (by norm_num)) (mapsAMI (by norm_num))).1
    (good_mmM (good_AM (k := 7) (by norm_num)).1 (good_AM (k := 6) (by norm_num)).1).1

theorem gGD : ∀ k < 2, Good (GD k) := by
  intro k hk
  interval_cases k
  · exact good_GD0
  · exact good_AM (k := 7) (by norm_num)

theorem gD : ∀ i < 60, Good (PD i) := good_pts (fun k hk => (gGD k hk).1) rootD ptD_all

theorem gGC1 : ∀ k < 3, Good (GC1 k) := by
  intro k hk
  interval_cases k
  · exact good_AM (k := 1) (by norm_num)
  · exact good_AM (k := 6) (by norm_num)
  · exact good_AM (k := 7) (by norm_num)

theorem ne_zero_one {j : ℕ} (h0 : j ≠ 0) (h1 : j ≠ 1) :
    XL j = mmK (mmK (AMI (j + 7)) (AM 1)) (AM (j + 7)) := by
  have e0 : Nat.beq j 0 = false := by
    cases h : Nat.beq j 0
    · rfl
    · rw [Nat.beq_eq] at h
      exact absurd h h0
  have e1 : Nat.beq j 1 = false := by
    cases h : Nat.beq j 1
    · rfl
    · rw [Nat.beq_eq] at h
      exact absurd h h1
  unfold XL
  rw [e0, e1]

theorem qline {j : ℕ} (hj : j < 31) :
    co2FiveLines[j]! = permOfMat 22 co2FiveV (XL j) ∧ Good (XL j) ∧
      ∃ A', Inv 22 co2FiveV (XL j) A' := by
  have e : co2FiveLines[j]! = co2FiveLineArr j := by
    rw [co2FiveLines, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  rw [e]
  by_cases h0 : j = 0
  · subst h0
    rw [co2FiveLineArr, ite_eq_left rfl, co2FiveX0Arr, arr_eq (by norm_num)]
    exact ⟨rfl, good_AM (by norm_num), _, (amF (k := 0) (by norm_num)).1⟩
  by_cases h1 : j = 1
  · subst h1
    rw [co2FiveLineArr, ite_eq_right h0, ite_eq_left rfl, co2FiveX1Arr, arr_eq (by norm_num)]
    exact ⟨rfl, good_AM (by norm_num), _, (amF (k := 1) (by norm_num)).1⟩
  have hh : j + 7 < 38 := by omega
  rw [co2FiveLineArr, ite_eq_right h0, ite_eq_right h1, co2FiveHArr, ite_eq_right (by omega),
    co2FiveX1Arr, arr_eq hh, arr_eq (k := 1) (by norm_num),
    conj_good (amF hh).1 (good_AM (by norm_num)), ne_zero_one h0 h1]
  refine ⟨rfl, good_mmM (good_mmM (mapsAMI hh) (good_AM (k := 1) (by norm_num)).1).1
    (good_AM hh).1, ?_⟩
  rw [hmm, hmm]
  exact ⟨_, ((amF hh).1.symm.mul hd22 (amF (k := 1) (by norm_num)).1).mul hd22 (amF hh).1⟩

theorem q_parts :
    (∀ k < 125, Nat.beq (pwK (PQ k) 5) I22 = true ∧ (Nat.beq (PQ k) I22 = true ∨
      (WT 0 k < 155 ∧ PQ k = pwK (XL (WT 0 k / 5)) (WT 0 k % 5)))) ∧
    (∀ j < 31, ∀ j' < 31, j = j' ∨ ∀ e < 5, Nat.beq (XL j) (pwK (XL j') e) = false) ∧
    (∀ j < 31, Nat.beq (pwK (XL j) 5) I22 = true ∧ Nat.beq (XL j) I22 = false ∧
      WT 1 j < 125 ∧ PQ (WT 1 j) = XL j) := by
  have h := q_ok
  unfold qK at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun k hk => ?_, fun j hj j' hj' => ?_, fun j hj => ?_⟩
  · have := allN_spec h1 k hk
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at this
    refine ⟨this.1, this.2.imp id fun h => ⟨h.1, Nat.eq_of_beq_eq_true h.2⟩⟩
  · have := allN_spec (allN_spec h2 j hj) j' hj'
    rw [Bool.or_eq_true, Nat.beq_eq] at this
    refine this.imp id fun h e he => ?_
    have := allN_spec h e he
    rwa [Bool.not_eq_true'] at this
  · have := allN_spec h3 j hj
    simp only [Bool.and_eq_true, Bool.not_eq_true', Nat.blt_eq] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, Nat.eq_of_beq_eq_true this.2⟩

theorem qcheck_ok : co2FiveQCheck co2FiveQLit co2FiveLines = true := by
  obtain ⟨hN, hP, -, -⟩ := litQ
  obtain ⟨p1, p2, p3⟩ := q_parts
  have q3 : allLt 125 (fun k => eqA 2300 (powArr 2300 co2FiveQLit.pts[k]! 5) (idA 2300)) =
      true := by
    rw [allLt_iff]
    intro k hk
    rw [hP k hk, pow_good (gQ k hk), idA_eq, eqA_good (good_pw (gQ k hk) 5) good_I22]
    exact (p1 k hk).1
  have q4 : allLt 125 (fun k => eqA 2300 co2FiveQLit.pts[k]! (idA 2300) ||
      (List.range 31).any fun j => (List.range 5).any fun e =>
        eqA 2300 co2FiveQLit.pts[k]! (powArr 2300 co2FiveLines[j]! e)) = true := by
    rw [allLt_iff]
    intro k hk
    rw [Bool.or_eq_true]
    rcases (p1 k hk).2 with h | ⟨hw, he⟩
    · left
      rw [hP k hk, idA_eq, eqA_good (gQ k hk) good_I22]
      exact h
    · right
      have hj : WT 0 k / 5 < 31 := by omega
      have he5 : WT 0 k % 5 < 5 := Nat.mod_lt _ (by norm_num)
      rw [List.any_eq_true]
      refine ⟨WT 0 k / 5, List.mem_range.2 hj, List.any_eq_true.2 ⟨WT 0 k % 5,
        List.mem_range.2 he5, ?_⟩⟩
      obtain ⟨hl, hg, -⟩ := qline hj
      rw [hP k hk, hl, pow_good hg, eqA_good (gQ k hk) (good_pw hg _), he]
      exact Nat.beq_refl _
  have q5 : allLt 31 (fun j => allLt 31 fun j' => j == j' ||
      allLt 5 fun e => !(eqA 2300 co2FiveLines[j]! (powArr 2300 co2FiveLines[j']! e))) =
      true := by
    rw [allLt_iff]
    intro j hj
    rw [allLt_iff]
    intro j' hj'
    rw [Bool.or_eq_true]
    rcases p2 j hj j' hj' with h | h
    · left
      rw [h]
      exact beq_self_eq_true _
    · right
      rw [allLt_iff]
      intro e he
      obtain ⟨hl, hg, -⟩ := qline hj
      obtain ⟨hl', hg', -⟩ := qline hj'
      rw [hl, hl', pow_good hg', eqA_good hg (good_pw hg' e), h e he]
      rfl
  have q6 : allLt 31 (fun j => validA 2300 co2FiveLines[j]! &&
      eqA 2300 (powArr 2300 co2FiveLines[j]! 5) (idA 2300) &&
      !(eqA 2300 co2FiveLines[j]! (idA 2300)) &&
      co2FiveQLit.pts.toList.any (eqA 2300 co2FiveLines[j]!)) = true := by
    rw [allLt_iff]
    intro j hj
    obtain ⟨hl, hg, A', hA'⟩ := qline hj
    obtain ⟨h1, h2, h3, h4⟩ := p3 j hj
    rw [hl, pow_good hg, idA_eq, eqA_good (good_pw hg 5) good_I22, eqA_good hg good_I22,
      validA_inv hA', h1, h2, any_good hN hP h3 h4]
    rfl
  have q7 : allLt 31 (fun j => validA 2300 (co2FiveHArr j)) = true := by
    rw [allLt_iff]
    intro j hj
    unfold co2FiveHArr
    split
    · rw [idA_eq, I22_eq]
      exact validA_inv (inv_idM hd22 sys.lt)
    · rw [arr_eq (by omega)]
      exact validA_inv (amF (by omega)).1
  unfold co2FiveQCheck
  rw [enumQ, hN, q3, q4, q5, q6, q7]
  rfl

theorem C0gen : ∀ k < 2, co2FiveC0GenArrs[k]! = permOfMat 22 co2FiveV (GC0 k) := by
  intro k hk
  interval_cases k
  · rw [co2FiveC0GenArrs, get2_0]
    exact arr_eq (k := 2) (by norm_num)
  · rw [co2FiveC0GenArrs, get2_1]
    exact arr_eq (k := 3) (by norm_num)

theorem Agen : ∀ k < 2, co2FiveAGenArrs[k]! = permOfMat 22 co2FiveV (GQ k) := by
  intro k hk
  interval_cases k
  · rw [co2FiveAGenArrs, get2_0]
    exact arr_eq (k := 4) (by norm_num)
  · rw [co2FiveAGenArrs, get2_1]
    exact arr_eq (k := 5) (by norm_num)

theorem gGC0 : ∀ k < 2, Good (GC0 k) := by
  intro k hk
  interval_cases k
  · exact good_AM (k := 2) (by norm_num)
  · exact good_AM (k := 3) (by norm_num)

theorem gGQ : ∀ k < 2, Good (GQ k) := by
  intro k hk
  interval_cases k
  · exact good_AM (k := 4) (by norm_num)
  · exact good_AM (k := 5) (by norm_num)

theorem C0genI : ∀ k < 2, Inv 22 co2FiveV (GC0 k) (GC0I k) := by
  intro k hk
  interval_cases k
  · exact (amF (k := 2) (by norm_num)).1
  · exact (amF (k := 3) (by norm_num)).1

theorem c0_parts : (∀ k < 2, comm (GC0 k) (AM 0) = true) ∧
    (∀ k < 2, WT 2 k < 3000 ∧ PC0 (WT 2 k) = GQ k) ∧
    (∀ k < 2, ∀ l < 2, WT 3 (2 * k + l) < 125 ∧
      PQ (WT 3 (2 * k + l)) = mmK (mmK (GC0I k) (GQ l)) (GC0 k)) ∧
    (∀ k < 3000, (!(comm (PC0 k) (AM 4) && comm (PC0 k) (AM 5)) ||
      (List.range 5).any fun e => Nat.beq (PC0 k) (pwK (AM 0) e)) = true) := by
  have h := c0_ok
  unfold c0K at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨allN_spec h1, fun k hk => ?_, fun k hk l hl => ?_, allN_spec h4⟩
  · have := allN_spec h2 k hk
    rw [Bool.and_eq_true, Nat.blt_eq] at this
    exact ⟨this.1, Nat.eq_of_beq_eq_true this.2⟩
  · have := allN_spec (allN_spec h3 k hk) l hl
    rw [Bool.and_eq_true, Nat.blt_eq] at this
    exact ⟨this.1, Nat.eq_of_beq_eq_true this.2⟩

theorem any_pow {P X : ℕ} (hP : Good P) (hX : Good X)
    (h : ((List.range 5).any fun e => Nat.beq P (pwK X e)) = true) :
    ((List.range 5).any fun e => eqA 2300 (permOfMat 22 co2FiveV P)
      (powArr 2300 (permOfMat 22 co2FiveV X) e)) = true := by
  rw [List.any_eq_true] at h ⊢
  obtain ⟨e, he, hb⟩ := h
  refine ⟨e, he, ?_⟩
  rw [pow_good hX, eqA_good hP (good_pw hX e)]
  exact hb

theorem c0check_ok : co2FiveC0Check co2FiveC0Lit co2FiveQLit = true := by
  obtain ⟨hN, hP, -, -⟩ := litC0
  obtain ⟨hNQ, hPQ, -, -⟩ := litQ
  obtain ⟨p1, p2, p3, p4⟩ := c0_parts
  have hX0 : co2FiveX0Arr = permOfMat 22 co2FiveV (AM 0) := by
    rw [co2FiveX0Arr, arr_eq (by norm_num)]
  have c3 : allLt 2 (fun k => commA 2300 co2FiveC0GenArrs[k]! co2FiveX0Arr) = true := by
    rw [allLt_iff]
    intro k hk
    rw [C0gen k hk, hX0, commA_good (gGC0 k hk) (good_AM (by norm_num))]
    exact p1 k hk
  have c4 : allLt 2 (fun k => co2FiveC0Lit.pts.toList.any (eqA 2300 co2FiveAGenArrs[k]!)) =
      true := by
    rw [allLt_iff]
    intro k hk
    rw [Agen k hk]
    exact any_good hN hP (p2 k hk).1 (p2 k hk).2
  have c5 : allLt 2 (fun k => allLt 2 fun l => co2FiveQLit.pts.toList.any
      (eqA 2300 (conjA 2300 co2FiveC0GenArrs[k]! co2FiveAGenArrs[l]!))) = true := by
    rw [allLt_iff]
    intro k hk
    rw [allLt_iff]
    intro l hl
    rw [C0gen k hk, Agen l hl, conj_good (C0genI k hk) (gGQ l hl)]
    exact any_good hNQ hPQ (p3 k hk l hl).1 (p3 k hk l hl).2
  have c6 : allLt 3000 (fun k => !(commA 2300 co2FiveC0Lit.pts[k]! co2FiveAGenArrs[0]! &&
      commA 2300 co2FiveC0Lit.pts[k]! co2FiveAGenArrs[1]!) ||
      (List.range 5).any fun e => eqA 2300 co2FiveC0Lit.pts[k]! (powArr 2300 co2FiveX0Arr e)) =
      true := by
    rw [allLt_iff]
    intro k hk
    have h := p4 k hk
    rw [Agen 0 (by norm_num), Agen 1 (by norm_num), hP k hk, hX0,
      commA_good (gC0 k hk) (gGQ 0 (by norm_num)), commA_good (gC0 k hk) (gGQ 1 (by norm_num))]
    rw [Bool.or_eq_true] at h ⊢
    exact h.imp id (any_pow (gC0 k hk) (good_AM (by norm_num)))
  unfold co2FiveC0Check
  rw [enumC0, hN, c3, c4, c5, c6]
  rfl

theorem c1_parts : (∀ k < 3, comm (GC1 k) (AM 1) = true) ∧
    Nat.beq (mmK BH BG) (mmK (mmK BG BH) (AM 7)) = true ∧
    (∀ k < 3, ∀ l < 2, WT 4 (2 * k + l) < 60 ∧
      PD (WT 4 (2 * k + l)) = mmK (mmK (GC1I k) (GD l)) (GC1 k)) ∧
    (∀ k < 3, ∀ l < 3, WT 5 (3 * k + l) < 60 ∧
      PD (WT 5 (3 * k + l)) = mmK (mmK (GC1I l) (GC1I k)) (mmK (GC1 l) (GC1 k))) ∧
    comm DG0 (AM 7) = false ∧
    (∀ k < 600, (!(comm (PC1 k) DG0 && comm (PC1 k) (AM 7)) ||
      (List.range 5).any fun e => Nat.beq (PC1 k) (pwK (AM 1) e)) = true) := by
  have h := c1_ok
  unfold c1K at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨allN_spec h1, h2, fun k hk l hl => ?_, fun k hk l hl => ?_, h5, allN_spec h6⟩
  · have := allN_spec (allN_spec h3 k hk) l hl
    rw [Bool.and_eq_true, Nat.blt_eq] at this
    exact ⟨this.1, Nat.eq_of_beq_eq_true this.2⟩
  · have := allN_spec (allN_spec h4 k hk) l hl
    rw [Bool.and_eq_true, Nat.blt_eq] at this
    exact ⟨this.1, Nat.eq_of_beq_eq_true this.2⟩

theorem hX1 : co2FiveX1Arr = permOfMat 22 co2FiveV (AM 1) := by
  rw [co2FiveX1Arr, arr_eq (by norm_num)]

theorem c1_comm : allLt 3 (fun k => commA 2300 co2FiveC1GenArrs[k]! co2FiveX1Arr) = true := by
  rw [allLt_iff]
  intro k hk
  rw [C1gen k hk, hX1, commA_good (gGC1 k hk) (good_AM (by norm_num))]
  exact c1_parts.1 k hk

theorem d_rel : eqA 2300 (compA 2300 (co2BWordG co2FiveC1GenArrs) (co2BWordH co2FiveC1GenArrs))
    (compA 2300 co2FiveC1GenArrs[2]! (compA 2300 (co2BWordH co2FiveC1GenArrs)
      (co2BWordG co2FiveC1GenArrs))) = true := by
  have g1 := gGC1 1 (by norm_num)
  have g2 := gGC1 2 (by norm_num)
  have i2 := C1genI 2 (by norm_num)
  have m2 : Good (mmK (GC1I 2) (GC1I 2)) := good_mmM i2.2.1 i2.2.1
  have gG : Good (mmK (mmK (GC1I 2) (GC1I 2)) (GC1 1)) := good_mmM m2.1 g1.1
  have h21 : Good (mmK (GC1 2) (GC1 1)) := good_mmM g2.1 g1.1
  have h212 : Good (mmK (mmK (GC1 2) (GC1 1)) (GC1 2)) := good_mmM h21.1 g2.1
  have gH : Good (mmK (mmK (mmK (GC1 2) (GC1 1)) (GC1 2)) (GC1 1)) := good_mmM h212.1 g1.1
  have eG : co2BWordG co2FiveC1GenArrs =
      permOfMat 22 co2FiveV (mmK (mmK (GC1I 2) (GC1I 2)) (GC1 1)) := by
    rw [co2BWordG, C1gen 1 (by norm_num), C1gen 2 (by norm_num), invCand_good i2,
      compA_maps i2.2.1, compA_good m2]
  have eH : co2BWordH co2FiveC1GenArrs =
      permOfMat 22 co2FiveV (mmK (mmK (mmK (GC1 2) (GC1 1)) (GC1 2)) (GC1 1)) := by
    rw [co2BWordH, C1gen 1 (by norm_num), C1gen 2 (by norm_num), compA_good g2, compA_good h21,
      compA_good h212]
  rw [eG, eH, C1gen 2 (by norm_num), compA_good gH, compA_good gG, compA_good (good_mmM gG.1 gH.1),
    eqA_good (good_mmM gH.1 gG.1) (good_mmM (good_mmM gG.1 gH.1).1 g2.1)]
  exact c1_parts.2.1

end CertificateChecks.KernelMisc.Co2K

end
