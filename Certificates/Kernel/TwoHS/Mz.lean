module

public import Certificates.Kernel.TwoHS.HYWords
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAUModCheck
public import Certificates.Kernel.TwoHS.MzTblU
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.BfsPinAlg

set_option maxRecDepth 400000

public section

set_option Elab.async false

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.MulH CFSG.EvenSporadicStandard.TwoHS

theorem mzPc_assoc {n w p q r : Nat} (hp : canonK n w (mask w) (n * w) p = true)
    (hr : canonK n w (mask w) (n * w) r = true) :
    pcomp n w (mask w) (pcomp n w (mask w) p q) r =
      pcomp n w (mask w) p (pcomp n w (mask w) q r) := by
  obtain ⟨hn, hw, -, -⟩ := PF.canon_facts hp
  obtain ⟨-, -, -, hrr⟩ := PF.canon_facts hr
  have hn32 : n < 2 ^ 32 := by omega
  have hw0 := PF.w_pos hw
  refine PF.eq_of_fields hw0 (PF.pcomp_shr _ _ hn32 hw0) (PF.pcomp_shr _ _ hn32 hw0) fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pcomp hn32 (hrr i hi), PF.pg_pcomp hn32 hi,
    PF.pg_pcomp hn32 hi]

theorem mzPc_idR {n w p : Nat} (hp : canonK n w (mask w) (n * w) p = true) :
    pcomp n w (mask w) p (pidn n w) = p := by
  obtain ⟨hn, hw, hp0, -⟩ := PF.canon_facts hp
  have hn32 : n < 2 ^ 32 := by omega
  refine PF.eq_of_fields (PF.w_pos hw) (PF.pcomp_shr _ _ hn32 (PF.w_pos hw)) hp0 fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw hi]

theorem mzPc_idL {n w p : Nat} (hp : canonK n w (mask w) (n * w) p = true) :
    pcomp n w (mask w) (pidn n w) p = p := by
  obtain ⟨hn, hw, hp0, hp4⟩ := PF.canon_facts hp
  have hn32 : n < 2 ^ 32 := by omega
  refine PF.eq_of_fields (PF.w_pos hw) (PF.pcomp_shr _ _ hn32 (PF.w_pos hw)) hp0 fun i hi => ?_
  rw [PF.pg_pcomp hn32 hi, PF.pg_pidn hn hw (hp4 i hi)]

theorem mzFold_cons {n w m : Nat} {S : Nat → Nat} (l : Nat) (rest : List Nat) (acc : Nat) :
    wfoldK n w m S (l :: rest) acc = wfoldK n w m S rest (pcomp n w m acc (S l)) := by
  change strictN (pcomp n w m acc (S l)) (wfoldK n w m S rest) = _
  rw [CFSG.KS.PEnum.strictN_app']

theorem mzFold_append {n w : Nat} {S : Nat → Nat} (a b : List Nat) (acc : Nat) :
    wfoldK n w (mask w) S (a ++ b) acc = wfoldK n w (mask w) S b (wfoldK n w (mask w) S a acc) := by
  induction a generalizing acc with
  | nil => rfl
  | cons l a ih => rw [List.cons_append, mzFold_cons, mzFold_cons, ih]

theorem mzFold_split {n w : Nat} {S : Nat → Nat} (a b : List Nat) {acc V T : Nat}
    (h1 : Nat.beq (wfoldK n w (mask w) S a acc) V = true)
    (h2 : Nat.beq (wfoldK n w (mask w) S b V) T = true) :
    wfoldK n w (mask w) S (a ++ b) acc = T := by
  rw [mzFold_append, Nat.eq_of_beq_eq_true h1]
  exact Nat.eq_of_beq_eq_true h2

theorem mzBeq_split {n w : Nat} {S : Nat → Nat} (a b : List Nat) {acc V T : Nat}
    (h1 : Nat.beq (wfoldK n w (mask w) S a acc) V = true)
    (h2 : Nat.beq (wfoldK n w (mask w) S b V) T = true) :
    Nat.beq (wfoldK n w (mask w) S (a ++ b) acc) T = true := by
  rw [mzFold_split a b h1 h2]
  exact Nat.beq_refl T

theorem mzBeq_mid {A B V : Nat} (h1 : Nat.beq A V = true) (h2 : Nat.beq B V = true) :
    Nat.beq A B = true := by
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
  exact Nat.beq_refl V

theorem mzFold_pc {n w : Nat} {S : Nat → Nat} (hid : canonK n w (mask w) (n * w) (pidn n w) = true) :
    ∀ wd : List Nat, (∀ l ∈ wd, canonK n w (mask w) (n * w) (S l) = true) →
      ∀ acc, canonK n w (mask w) (n * w) acc = true →
        wfoldK n w (mask w) S wd acc =
            pcomp n w (mask w) acc (wfoldK n w (mask w) S wd (pidn n w)) ∧
          canonK n w (mask w) (n * w) (wfoldK n w (mask w) S wd acc) = true
  | [], _, acc, ha => ⟨(mzPc_idR ha).symm, ha⟩
  | l :: wd, hS, acc, ha => by
    have hl := hS l (List.mem_cons_self ..)
    have hS' : ∀ k ∈ wd, canonK n w (mask w) (n * w) (S k) = true :=
      fun k hk => hS k (List.mem_cons_of_mem _ hk)
    have hal := CFSG.KC.BfsPin.canonK_pcomp ha hl
    have h1 := mzFold_pc hid wd hS' _ hal
    have h2 := mzFold_pc hid wd hS' _ hl
    have h3 := mzFold_pc hid wd hS' _ hid
    have hc := h1.2
    rw [h1.1, mzPc_assoc ha h3.2] at hc
    rw [mzFold_cons, mzFold_cons, mzPc_idL hl, h1.1, h2.1, mzPc_assoc ha h3.2]
    exact ⟨rfl, hc⟩

theorem mzFold_flatMap {n w : Nat} {S X : Nat → Nat} {sym : Nat → List Nat}
    (hid : canonK n w (mask w) (n * w) (pidn n w) = true)
    (hS : ∀ s, ∀ l ∈ sym s, canonK n w (mask w) (n * w) (S l) = true)
    (hX : ∀ s, wfoldK n w (mask w) S (sym s) (pidn n w) = X s) :
    ∀ (su : List Nat) (acc : Nat), canonK n w (mask w) (n * w) acc = true →
      wfoldK n w (mask w) S (su.flatMap sym) acc = wfoldK n w (mask w) X su acc
  | [], _, _ => rfl
  | s :: su, acc, ha => by
    have h := mzFold_pc hid (sym s) (hS s) acc ha
    rw [List.flatMap_cons, mzFold_append, h.1, hX s, mzFold_cons]
    have hc := h.2
    rw [h.1, hX s] at hc
    exact mzFold_flatMap hid hS hX su _ hc

@[expose] def mzRecW : List (List Nat) :=
  sigWords ++ [mzRW, mzAW, mzPW, gamma1Word, gamma2Word] ++ betaWords ++ [tWord]

@[expose] def mzSymW (s : Nat) : List Nat :=
  if s = 0 then [] else if s ≤ 6 then [s] else mzRecW.getD (s - 7) []

@[expose] noncomputable def mzXS (s : Nat) : Nat :=
  if s = 0 then idK else if s ≤ 6 then L s else if s ≤ 21 then mzT (s - 7) else idK

@[expose] def mzSgS (w : List Nat) : List Nat := w.map (· + 6)

@[expose] def mzKapS (c : List Nat) : List Nat :=
  rptW [18] (c.getD 0 0) ++ rptW [19] (c.getD 1 0) ++ rptW [21] (c.getD 2 0 / 2) ++
    rptW [20] (c.getD 3 0)

theorem mz_rec0 : Nat.beq (WK (mzSymW 7)) (mzXS 7) = true := by quickRfl
theorem mz_rec1 : Nat.beq (WK (mzSymW 8)) (mzXS 8) = true := by quickRfl
theorem mz_rec2 : Nat.beq (WK (mzSymW 9)) (mzXS 9) = true := by quickRfl
theorem mz_rec3 : Nat.beq (WK (mzSymW 10)) (mzXS 10) = true := by quickRfl
theorem mz_rec4a : Nat.beq (wfoldK 11200 14 (mask 14) L
    [3, 2, 3, 4, 1, 2, 3, 1, 2, 3, 2, 1, 5, 4] idK) mzU0 = true := by quickRfl
theorem mz_rec4b : Nat.beq (wfoldK 11200 14 (mask 14) L
    [3, 2, 1, 6, 5, 1, 6, 4, 3, 2, 3, 2, 1, 4] mzU0) (mzXS 11) = true := by quickRfl
theorem mz_rec4 : WK (mzSymW 11) = mzXS 11 := by
  have e : mzSymW 11 =
      [3, 2, 3, 4, 1, 2, 3, 1, 2, 3, 2, 1, 5, 4] ++ [3, 2, 1, 6, 5, 1, 6, 4, 3, 2, 3, 2, 1, 4] := rfl
  unfold WK
  rw [e]
  exact mzFold_split _ _ mz_rec4a mz_rec4b
theorem mz_rec5 : Nat.beq (WK (mzSymW 12)) (mzXS 12) = true := by quickRfl
theorem mz_rec6 : Nat.beq (WK (mzSymW 13)) (mzXS 13) = true := by quickRfl
theorem mz_rec7 : Nat.beq (WK (mzSymW 14)) (mzXS 14) = true := by quickRfl
theorem mz_rec8 : Nat.beq (WK (mzSymW 15)) (mzXS 15) = true := by quickRfl
theorem mz_rec9 : Nat.beq (WK (mzSymW 16)) (mzXS 16) = true := by quickRfl
theorem mz_rec10 : Nat.beq (WK (mzSymW 17)) (mzXS 17) = true := by quickRfl
theorem mz_rec11a : Nat.beq (wfoldK 11200 14 (mask 14) L
    [1, 3, 2, 1, 3, 2, 3, 4, 3, 2, 3, 5, 4] idK) mzU1 = true := by quickRfl
theorem mz_rec11b : Nat.beq (wfoldK 11200 14 (mask 14) L
    [3, 2, 6, 3, 5, 4, 2, 1, 6, 1, 2, 5, 6] mzU1) (mzXS 18) = true := by quickRfl
theorem mz_rec11 : WK (mzSymW 18) = mzXS 18 := by
  have e : mzSymW 18 =
      [1, 3, 2, 1, 3, 2, 3, 4, 3, 2, 3, 5, 4] ++ [3, 2, 6, 3, 5, 4, 2, 1, 6, 1, 2, 5, 6] := rfl
  unfold WK
  rw [e]
  exact mzFold_split _ _ mz_rec11a mz_rec11b
theorem mz_rec12 : Nat.beq (WK (mzSymW 19)) (mzXS 19) = true := by quickRfl
theorem mz_rec13 : Nat.beq (WK (mzSymW 20)) (mzXS 20) = true := by quickRfl
theorem mz_rec14 : Nat.beq (WK (mzSymW 21)) (mzXS 21) = true := by quickRfl

theorem mzSymW_ok (s : Nat) : lettersOK (mzSymW s) = true := by
  unfold mzSymW
  split_ifs with h0 h6
  · rfl
  · simp only [lettersOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq]
    omega
  · have hw : mzRecW.all lettersOK = true := by quickRfl
    rw [List.getD_eq_getElem?_getD]
    cases h : mzRecW[s - 7]? with
    | none => rfl
    | some wd => exact List.all_eq_true.1 hw wd (List.mem_of_getElem? h)

theorem mzId_cn : canonK 11200 14 (mask 14) (11200 * 14) idK = true :=
  (CFSG.KC.BfsPin.PP.id (by decide)).1

theorem mzL_ok : allN 6 (fun j => canonK 11200 14 (mask 14) (11200 * 14) (HY.F j)) = true := by
  quickRfl

theorem mzL_cn {l : Nat} (h1 : 1 ≤ l) (h6 : l ≤ 6) :
    canonK 11200 14 (mask 14) (11200 * 14) (L l) = true :=
  CFSG.KS.Raw.Orb.allN_iff.1 mzL_ok (l - 1) (by omega)

theorem mzWK_one (l : Nat) (h1 : 1 ≤ l) (h6 : l ≤ 6) : WK [l] = L l := by
  unfold WK
  rw [mzFold_cons]
  exact mzPc_idL (mzL_cn h1 h6)

theorem mzWK_sym : ∀ s, WK (mzSymW s) = mzXS s
  | 0 => rfl
  | 1 => mzWK_one 1 (by omega) (by omega)
  | 2 => mzWK_one 2 (by omega) (by omega)
  | 3 => mzWK_one 3 (by omega) (by omega)
  | 4 => mzWK_one 4 (by omega) (by omega)
  | 5 => mzWK_one 5 (by omega) (by omega)
  | 6 => mzWK_one 6 (by omega) (by omega)
  | 7 => Nat.eq_of_beq_eq_true mz_rec0
  | 8 => Nat.eq_of_beq_eq_true mz_rec1
  | 9 => Nat.eq_of_beq_eq_true mz_rec2
  | 10 => Nat.eq_of_beq_eq_true mz_rec3
  | 11 => mz_rec4
  | 12 => Nat.eq_of_beq_eq_true mz_rec5
  | 13 => Nat.eq_of_beq_eq_true mz_rec6
  | 14 => Nat.eq_of_beq_eq_true mz_rec7
  | 15 => Nat.eq_of_beq_eq_true mz_rec8
  | 16 => Nat.eq_of_beq_eq_true mz_rec9
  | 17 => Nat.eq_of_beq_eq_true mz_rec10
  | 18 => mz_rec11
  | 19 => Nat.eq_of_beq_eq_true mz_rec12
  | 20 => Nat.eq_of_beq_eq_true mz_rec13
  | 21 => Nat.eq_of_beq_eq_true mz_rec14
  | n + 22 => by
    have hl : mzRecW.length = 15 := rfl
    have e1 : mzSymW (n + 22) = [] := by
      rw [mzSymW, ite_eq_right (by omega), ite_eq_right (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega), Option.getD_none]
    have e2 : mzXS (n + 22) = idK := by
      rw [mzXS, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [e1, e2]
    rfl

theorem mz_wEq {u v : List Nat} (su sv : List Nat) (hu : u = su.flatMap mzSymW)
    (hv : v = sv.flatMap mzSymW) :
    wEq u v = Nat.beq (wfoldK 11200 14 (mask 14) mzXS su idK)
      (wfoldK 11200 14 (mask 14) mzXS sv idK) := by
  subst hu hv
  have hl : ∀ t : List Nat, lettersOK (t.flatMap mzSymW) = true := fun t => by
    simp only [lettersOK, List.all_flatMap]
    exact List.all_eq_true.2 fun s _ => mzSymW_ok s
  have hS : ∀ s, ∀ l ∈ mzSymW s, canonK 11200 14 (mask 14) (11200 * 14) (L l) = true :=
    fun s l hl' => by
      have h := List.all_eq_true.1 (mzSymW_ok s) l hl'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact mzL_cn h.1 h.2
  unfold wEq
  rw [ite_eq_left (by simp only [hl, Bool.and_self])]
  unfold WK
  rw [mzFold_flatMap mzId_cn hS mzWK_sym su idK mzId_cn,
    mzFold_flatMap mzId_cn hS mzWK_sym sv idK mzId_cn]

theorem mz_r3 : wEq (mzRW ++ mzRW ++ mzRW) [] = true := by
  rw [mz_wEq [13, 13, 13] [] _ _]
  · quickRfl
  all_goals rfl
theorem mz_rb0 : wEq (mzRW ++ betaW 0) (kapW (colOf mzRData ([0, 1, 3].getD 0 0)) ++ mzRW) = true := by
  rw [mz_wEq [13, 18] (mzKapS (colOf mzRData ([0, 1, 3].getD 0 0)) ++ [13]) _ _]
  · quickRfl
  all_goals rfl
theorem mz_rb1 : wEq (mzRW ++ betaW 1) (kapW (colOf mzRData ([0, 1, 3].getD 1 0)) ++ mzRW) = true := by
  rw [mz_wEq [13, 19] (mzKapS (colOf mzRData ([0, 1, 3].getD 1 0)) ++ [13]) _ _]
  · quickRfl
  all_goals rfl
theorem mz_rb2 : wEq (mzRW ++ betaW 2) (kapW (colOf mzRData ([0, 1, 3].getD 2 0)) ++ mzRW) = true := by
  rw [mz_wEq [13, 20] (mzKapS (colOf mzRData ([0, 1, 3].getD 2 0)) ++ [13]) _ _]
  · quickRfl
  all_goals rfl
theorem mz_as : wEq (mzAW ++ sigWord mzAW) [] = true := by
  rw [mz_wEq (14 :: mzSgS mzAW) [] _ _]
  · quickRfl
  all_goals rfl
theorem mz_ab0a : Nat.beq (wfoldK 11200 14 (mask 14) mzXS
    [14, 7, 9, 8, 7, 9, 8, 9, 10, 9, 8, 9, 11, 10] idK) mzU2 = true := by quickRfl
theorem mz_ab0b : Nat.beq (wfoldK 11200 14 (mask 14) mzXS [9, 8, 12, 9, 11, 10, 8, 7, 12, 7, 8, 11, 12]
    mzU2) (wfoldK 11200 14 (mask 14) mzXS [18, 18, 18, 14] idK) = true := by quickRfl
theorem mz_ab0 : wEq (mzAW ++ sigWord (betaW 0)) (rptW (betaW 0) 3 ++ mzAW) = true := by
  rw [mz_wEq ([14, 7, 9, 8, 7, 9, 8, 9, 10, 9, 8, 9, 11, 10] ++
    [9, 8, 12, 9, 11, 10, 8, 7, 12, 7, 8, 11, 12]) [18, 18, 18, 14] _ _]
  · exact mzBeq_split _ _ mz_ab0a mz_ab0b
  all_goals rfl
theorem mz_ab1 : wEq (mzAW ++ sigWord (betaW 1)) (rptW (betaW 1) 3 ++ mzAW) = true := by
  rw [mz_wEq (14 :: mzSgS (betaW 1)) [19, 19, 19, 14] _ _]
  · quickRfl
  all_goals rfl
theorem mz_ab2a : Nat.beq (wfoldK 11200 14 (mask 14) mzXS [14, 12, 9, 11, 8, 9, 10, 12, 9, 10, 11]
    idK) mzU3 = true := by quickRfl
theorem mz_ab2b : Nat.beq (wfoldK 11200 14 (mask 14) mzXS [12, 9, 10, 8, 9, 8, 11, 9, 8, 10, 9]
    mzU3) (wfoldK 11200 14 (mask 14) mzXS [20, 20, 20, 14] idK) = true := by quickRfl
theorem mz_ab2 : wEq (mzAW ++ sigWord (betaW 2)) (rptW (betaW 2) 3 ++ mzAW) = true := by
  rw [mz_wEq ([14, 12, 9, 11, 8, 9, 10, 12, 9, 10, 11] ++ [12, 9, 10, 8, 9, 8, 11, 9, 8, 10, 9])
    [20, 20, 20, 14] _ _]
  · exact mzBeq_split _ _ mz_ab2a mz_ab2b
  all_goals rfl
theorem mz_ra : wEq (mzRW ++ mzAW) (mzAW ++ sigWord mzRW) = true := by
  rw [mz_wEq [13, 14] (14 :: mzSgS mzRW) _ _]
  · quickRfl
  all_goals rfl
theorem mz_p3 : wEq (mzPW ++ mzPW ++ mzPW) [] = true := by
  rw [mz_wEq [15, 15, 15] [] _ _]
  · quickRfl
  all_goals rfl
theorem mz_pr : wEq (mzPW ++ mzRW) (mzRW ++ mzPW) = true := by
  rw [mz_wEq [15, 13] [13, 15] _ _]
  · quickRfl
  all_goals rfl
theorem mz_pa : wEq (mzPW ++ mzAW) (mzAW ++ sigWord mzPW) = true := by
  rw [mz_wEq [15, 14] (14 :: mzSgS mzPW) _ _]
  · quickRfl
  all_goals rfl
theorem mz_g1 : wEq (gamma1Word ++ mzAW) (kapW mzEps ++ mzAW ++ sigWord gamma1Word) = true := by
  rw [mz_wEq [16, 14] (mzKapS mzEps ++ [14] ++ mzSgS gamma1Word) _ _]
  · quickRfl
  all_goals rfl
theorem mz_g2a : Nat.beq (wfoldK 11200 14 (mask 14) mzXS
    [17, 7, 10, 8, 7, 12, 9, 10, 7, 8, 9, 7, 12, 7, 8] idK) mzU4 = true := by quickRfl
theorem mz_g2b : Nat.beq (wfoldK 11200 14 (mask 14) mzXS
    [19, 19, 20, 20, 14, 12, 11, 7, 10, 9, 8, 9, 10, 7, 8, 7] idK) mzU4 = true := by quickRfl
theorem mz_g2 : wEq (gamma2Word ++ sigWord mzAW) (kapW mzEps ++ mzAW ++ sigWord gamma2Word) =
    true := by
  rw [mz_wEq [17, 7, 10, 8, 7, 12, 9, 10, 7, 8, 9, 7, 12, 7, 8]
    [19, 19, 20, 20, 14, 12, 11, 7, 10, 9, 8, 9, 10, 7, 8, 7] _ _]
  · exact mzBeq_mid mz_g2a mz_g2b
  all_goals rfl

theorem mz_r' : (!wEq mzRW []) = true := by
  rw [mz_wEq [13] [] _ _]
  · quickRfl
  all_goals rfl
theorem mz_p' : (!wEq mzPW []) = true := by
  rw [mz_wEq [15] [] _ _]
  · quickRfl
  all_goals rfl
theorem mz_pR' : (!wEq mzPW mzRW) = true := by
  rw [mz_wEq [15] [13] _ _]
  · quickRfl
  all_goals rfl
theorem mz_prr' : (!wEq mzPW (mzRW ++ mzRW)) = true := by
  rw [mz_wEq [15] [13, 13] _ _]
  · quickRfl
  all_goals rfl

theorem mz_r : wEq mzRW [] = false := by simpa using mz_r'
theorem mz_p : wEq mzPW [] = false := by simpa using mz_p'
theorem mz_pR : wEq mzPW mzRW = false := by simpa using mz_pR'
theorem mz_prr : wEq mzPW (mzRW ++ mzRW) = false := by simpa using mz_prr'

end CFSG.KD.TwoHS

end
