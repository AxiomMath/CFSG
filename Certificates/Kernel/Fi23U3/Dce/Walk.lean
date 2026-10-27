module

public import Certificates.Kernel.Fi23U3.Dce.Folds
public import CFSG.Certificates.Kernel.TwistDce3.Fold
public import CFSG.Certificates.Kernel.TwistDce2.Sound
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.Cover3Sound
public import Certificates.Data.CFSGNative.ComponentPrimary.Cover3Fi23
public import Certificates.Kernel.Fi23U3.Dce.WalkData

public section

namespace CFSG.KD.Fi23Dce3

open CFSG.KC.TwDce3 CFSG.KC.TwDce2 CFSG.CosetTable CFSG.Certificates.CosetEnumeration
  CFSG.Certificates.TwDce CFSG.LieType.Multipliers CFSG.Sporadic.Recognition.CoverRecipe
  CFSG.SectionRank.Native CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary
open CFSG.Certificates.TwDce2 (wdVal)

instance fi23_m_neZero : NeZero fi23U3Cover3.m := ⟨by decide⟩

theorem foldRange_add (m : ℕ) : ∀ n a S,
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a (n + m) S =
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ (a + n) m
      (foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a n S)
  | 0, a, S => by simp only [Nat.zero_add, Nat.add_zero]; rfl
  | n + 1, a, S => by
    rw [show n + 1 + m = (n + m) + 1 by omega, CFSG.Certificates.TwDce3.Fold.foldRange_succ,
      foldRange_add m n (a + 1), CFSG.Certificates.TwDce3.Fold.foldRange_succ,
      show a + 1 + n = a + (n + 1) by omega]

theorem fold_ok : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 44010 1 = 2735 := by
  have h1 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 10650 1 = 1849 := by
    have h := foldRange_add 5343 5307 0 1
    rw [fold0, Nat.zero_add, fold1] at h
    exact h
  have h2 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 15707 1 = 2730 := by
    have h := foldRange_add 5057 10650 0 1
    rw [h1, Nat.zero_add, fold2] at h
    exact h
  have h3 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 18945 1 = 2730 := by
    have h := foldRange_add 3238 15707 0 1
    rw [h2, Nat.zero_add, fold3] at h
    exact h
  have h4 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 24483 1 = 2735 := by
    have h := foldRange_add 5538 18945 0 1
    rw [h3, Nat.zero_add, fold4] at h
    exact h
  have h5 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 30558 1 = 2735 := by
    have h := foldRange_add 6075 24483 0 1
    rw [h4, Nat.zero_add, fold5] at h
    exact h
  have h6 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 35639 1 = 2735 := by
    have h := foldRange_add 5081 30558 0 1
    rw [h5, Nat.zero_add, fold6] at h
    exact h
  have h7 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 40433 1 = 2735 := by
    have h := foldRange_add 4794 35639 0 1
    rw [h6, Nat.zero_add, fold7] at h
    exact h
  have h8 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 42907 1 = 2735 := by
    have h := foldRange_add 2474 40433 0 1
    rw [h7, Nat.zero_add, fold8] at h
    exact h
  have h := foldRange_add 1103 42907 0 1
  rw [h8, Nat.zero_add, fold9] at h
  exact h

@[expose] def topCode (a : ℕ) : ℕ := [2, 0, 4, 12].getD (a / 2) 0 + a % 2

@[expose] def fiCoverCodes : List (List ℕ) :=
  (List.range 4).flatMap (fun i => fi23U3Cover3.relCodes.map fun r =>
      2 * i :: r ++ [2 * i + 1] ++ invRevCodes r) ++
    (List.range 4).map (fun i => [2 * i + 1, 2 * i]) ++
    fi23U3Cover3.relCodes.map (fun r => r ++ r ++ r) ++
    (List.range 4).map (fun i => [2 * i, 2 * i])

theorem codes_lt : ∀ r ∈ fiCoverCodes, ∀ a ∈ r, a < 8 := by decide +kernel

set_option maxRecDepth 100000 in
theorem codes_mem : ∀ r ∈ fiCoverCodes, ofCodes fi23U3Cover3.m r ∈
    coverWords fi23U3Cover3.rels fi23U3Cover3.cwF ++ cubeWords fi23U3Cover3.rels ++
      powWords fi23U3Cover3.ordF := by
  decide +kernel

@[expose] noncomputable def wdF (i : ℕ) : List ℕ := (wList (WD i)).filter (· != 14)

@[expose] noncomputable def wdRel (i : ℕ) : List ℕ := fiCoverCodes.getD ((WH i - 1) / 256) []

@[expose] noncomputable def wdOff (i : ℕ) : ℕ := (WH i - 1) % 256

@[expose] noncomputable def wdBool (i : ℕ) : Bool :=
  (decide (CFSG.KC.TwDce.wLen (WD i) < 2 ^ 12) && (wList (WD i)).all (fun c => decide (c < 15))) &&
    (((wdF i == []) || (wdF i == [12, 13]) || (wdF i == [13, 12])) ||
      ((decide ((WH i - 1) / 256 < fiCoverCodes.length) && decide (wdOff i < (wdRel i).length)) &&
        (((wdRel i).map topCode).drop (wdOff i) ++ ((wdRel i).map topCode).take (wdOff i) ==
          wdF i)))

theorem wd_bool : (List.range 4096).all wdBool = true := by
  quickRfl

theorem wd_ok : ∀ i < 4096, CFSG.KC.TwDce.wLen (WD i) < 2 ^ 12 ∧ (∀ c ∈ wList (WD i), c < 15) ∧
    (wdF i = [] ∨ wdF i = [12, 13] ∨ wdF i = [13, 12] ∨
      ∃ r ∈ fiCoverCodes, wdF i ∈ rotations (r.map topCode)) := by
  intro i hi
  have h := List.all_eq_true.1 wd_bool i (List.mem_range.2 hi)
  simp only [wdBool, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  rcases h3 with ((h | h) | h) | ⟨⟨hj, ho⟩, he⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr ⟨wdRel i, ?_, ?_⟩))
    · rw [wdRel, List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    · rw [← he, rotations]
      exact List.mem_map.2 ⟨wdOff i, List.mem_range.2 (by rw [List.length_map]; exact ho), rfl⟩

abbrev fiPC : Type := PG 4 fi23U3Cover3.cover

@[expose] def fiHGen (c : ℕ) : Fin 4 := ⟨[1, 0, 2].getD (c / 2) 0 % 4, Nat.mod_lt _ (by norm_num)⟩

@[expose] noncomputable def fiX (c : ℕ) : fiPC :=
  if c < 6 then (if c % 2 = 0 then PresentedGroup.of (fiHGen c) else (PresentedGroup.of (fiHGen c))⁻¹)
  else 1

noncomputable abbrev fiT : fiPC := PresentedGroup.of 3

theorem wdVal_topCode {a : ℕ} (ha : a < 8) : wdVal fiX fiT (topCode a) =
    cond (decide (a % 2 = 0)) (PresentedGroup.of (Fin.ofNat 4 (a / 2)) : fiPC)
      (PresentedGroup.of (Fin.ofNat 4 (a / 2)))⁻¹ := by
  interval_cases a <;> rfl

theorem evalWord_codes {r : List ℕ} (hr : r ∈ fiCoverCodes) :
    evalWord (wdVal fiX fiT) (r.map topCode) = 1 := by
  have e : evalWord (wdVal fiX fiT) (r.map topCode) =
      PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ fi23U3Cover3.cover.map FreeGroup.mk}
        (FreeGroup.mk (ofCodes 4 r)) := by
    rw [CFSG.Sporadic.Recognition.CoverTransfer.mk_eq_lift_of, FreeGroup.lift_mk, evalWord,
      List.map_map, ofCodes, List.map_map]
    congr 1
    exact List.map_congr_left fun a ha => wdVal_topCode (codes_lt r hr a ha)
  have hm : ofCodes fi23U3Cover3.m r ∈ fi23U3Cover3.cover := by
    rw [Cover3Data.cover, mem_cover₃Words, ← List.mem_append, ← List.mem_append]
    exact codes_mem r hr
  rw [e]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hm)

theorem wdVal_filter : ∀ l : List ℕ,
    evalWord (wdVal fiX fiT) l = evalWord (wdVal fiX fiT) (l.filter (· != 14))
  | [] => rfl
  | c :: l => by
    by_cases h : c = 14
    · subst h
      rw [List.filter_cons_of_neg (by decide), evalWord_cons, ← wdVal_filter l]
      simp [wdVal]
    · rw [List.filter_cons_of_pos (by simpa using h), evalWord_cons, evalWord_cons,
        wdVal_filter l]

theorem wd_one {i : ℕ} (hi : i < 4096) : evalWord (wdVal fiX fiT) (wList (WD i)) = 1 := by
  rw [wdVal_filter]
  change evalWord (wdVal fiX fiT) (wdF i) = 1
  rcases (wd_ok i hi).2.2 with h | h | h | ⟨r, hr, hv⟩
  · rw [h]; rfl
  · rw [h]; simp [evalWord, wdVal]
  · rw [h]; simp [evalWord, wdVal]
  · exact CFSG.CosetTable.evalWord_rotation hv (evalWord_codes hr)

theorem hWD : ∀ i < 4096, CFSG.KC.TwDce.wLen (WD i) < 2 ^ 12 ∧ (∀ c ∈ wList (WD i), c < 15) ∧
    evalWord (wdVal fiX fiT) (wList (WD i)) = 1 :=
  fun i hi => ⟨(wd_ok i hi).1, (wd_ok i hi).2.1, wd_one hi⟩

end CFSG.KD.Fi23Dce3

end
