module

public import Certificates.Kernel.TwistDce3.ON.Folds
public import CFSG.Certificates.Kernel.TwistDce3.Fold
public import CFSG.Certificates.Kernel.TwistDce2.Sound
public import CFSG.Sporadic.Recognition.ONMultiplierInputs

public section

namespace CFSG.KD.ONDce3

open CFSG.KC.TwDce3 CFSG.KC.TwDce2 CFSG.CosetTable CFSG.Sporadic.Recognition.ONMultiplier
  CFSG.Certificates.CosetEnumeration CFSG.Certificates.TwDce CFSG.LieType.Multipliers
  CFSG.Sporadic.Recognition.CoverRecipe
open CFSG.Certificates.TwDce2 (wdVal)

theorem foldRange_add (m : ℕ) : ∀ n a S,
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a (n + m) S =
    foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ (a + n) m
      (foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ a n S)
  | 0, a, S => by simp only [Nat.zero_add, Nat.add_zero]; rfl
  | n + 1, a, S => by
    rw [show n + 1 + m = (n + m) + 1 by omega, CFSG.Certificates.TwDce3.Fold.foldRange_succ,
      foldRange_add m n (a + 1), CFSG.Certificates.TwDce3.Fold.foldRange_succ,
      show a + 1 + n = a + (n + 1) by omega]

theorem fold_ok : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 4625 1 = 152 := by
  have h1 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 2977 1 = 152 := by
    have h := foldRange_add 1307 1670 0 1
    rw [fold0, Nat.zero_add, fold1] at h
    exact h
  have h2 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 3594 1 = 152 := by
    have h := foldRange_add 617 2977 0 1
    rw [h1, Nat.zero_add, fold2] at h
    exact h
  have h3 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 4015 1 = 152 := by
    have h := foldRange_add 421 3594 0 1
    rw [h2, Nat.zero_add, fold3] at h
    exact h
  have h4 : foldRange PB F INVM BS NB NT PSF PSB RD RW RA WD RJ 0 4367 1 = 152 := by
    have h := foldRange_add 352 4015 0 1
    rw [h3, Nat.zero_add, fold4] at h
    exact h
  have h := foldRange_add 258 4367 0 1
  rw [h4, Nat.zero_add, fold5] at h
  exact h

@[expose] def topCode (l : Fin 4 × Bool) : ℕ :=
  [0, 4, 2, 12].getD l.1.val 0 + bif l.2 then 0 else 1

@[expose] def onTopCodes : List (List ℕ) :=
  (coverWords onRels onCommWord ++ squareWords onRels).map (·.map topCode)

set_option maxRecDepth 100000 in
theorem wd_ok : ∀ i < 4096, CFSG.KC.TwDce.wLen (WD i) < 2 ^ 12 ∧ (∀ c ∈ wList (WD i), c < 15) ∧
    ((wList (WD i)).filter (· != 14) = [] ∨ (wList (WD i)).filter (· != 14) = [12, 13] ∨
      (wList (WD i)).filter (· != 14) = [13, 12] ∨
      ∃ r ∈ onTopCodes, r.length = ((wList (WD i)).filter (· != 14)).length ∧
        (wList (WD i)).filter (· != 14) ∈ rotations r) := by
  decide +kernel

abbrev onPC : Type := PG 4 onCover

@[expose] def onHGen (c : ℕ) : Fin 4 := ⟨[0, 2, 1].getD (c / 2) 0 % 4, Nat.mod_lt _ (by norm_num)⟩

@[expose] noncomputable def onX (c : ℕ) : onPC :=
  if c < 6 then (if c % 2 = 0 then PresentedGroup.of (onHGen c) else (PresentedGroup.of (onHGen c))⁻¹)
  else 1

noncomputable abbrev onT : onPC := PresentedGroup.of 3

theorem wdVal_topCode (l : Fin 4 × Bool) : wdVal onX onT (topCode l) =
    cond l.2 (PresentedGroup.of l.1 : onPC) (PresentedGroup.of l.1)⁻¹ := by
  obtain ⟨i, b⟩ := l
  fin_cases i <;> cases b <;> rfl

theorem evalWord_top {r : List (Fin 4 × Bool)} (hr : r ∈ onCover) :
    evalWord (wdVal onX onT) (r.map topCode) = 1 := by
  have e : evalWord (wdVal onX onT) (r.map topCode) =
      PresentedGroup.mk {r : FreeGroup (Fin 4) | r ∈ onCover.map FreeGroup.mk} (FreeGroup.mk r) := by
    rw [CFSG.Sporadic.Recognition.CoverTransfer.mk_eq_lift_of, FreeGroup.lift_mk, evalWord,
      List.map_map]
    congr 1
    exact List.map_congr_left fun l _ => wdVal_topCode l
  rw [e]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hr)

theorem wdVal_filter : ∀ l : List ℕ,
    evalWord (wdVal onX onT) l = evalWord (wdVal onX onT) (l.filter (· != 14))
  | [] => rfl
  | c :: l => by
    by_cases h : c = 14
    · subst h
      rw [List.filter_cons_of_neg (by decide), evalWord_cons, ← wdVal_filter l]
      simp [wdVal]
    · rw [List.filter_cons_of_pos (by simpa using h), evalWord_cons, evalWord_cons,
        wdVal_filter l]

theorem wd_one {i : ℕ} (hi : i < 4096) : evalWord (wdVal onX onT) (wList (WD i)) = 1 := by
  rw [wdVal_filter]
  rcases (wd_ok i hi).2.2 with h | h | h | ⟨r, hr, -, hv⟩
  · rw [h]; rfl
  · rw [h]; simp [evalWord, wdVal]
  · rw [h]; simp [evalWord, wdVal]
  · obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
    exact CFSG.CosetTable.evalWord_rotation hv
      (evalWord_top (mem_cover₂Words.2 (List.mem_append.1 hr')))

theorem hWD : ∀ i < 4096, CFSG.KC.TwDce.wLen (WD i) < 2 ^ 12 ∧ (∀ c ∈ wList (WD i), c < 15) ∧
    evalWord (wdVal onX onT) (wList (WD i)) = 1 :=
  fun i hi => ⟨(wd_ok i hi).1, (wd_ok i hi).2.1, wd_one hi⟩

end CFSG.KD.ONDce3

end
