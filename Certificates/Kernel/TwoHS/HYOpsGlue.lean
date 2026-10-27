module

public import Certificates.Kernel.TwoHS.HYGlue
public import Certificates.Kernel.TwoHS.HYOps
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
public import CFSG.Certificates.Kernel.Misc.RuInvCov
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Check

public section

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH
open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native

theorem cPc {p q : Nat} (hp : Cn p) (hq : Cn q) : Cn (pc p q) := CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem comp_eq {p q : Nat} (hp : Cn p) (hq : Cn q) :
    compT 11200 (tabT (unpack 11200 14 p)) (tabT (unpack 11200 14 q)) =
      tabT (unpack 11200 14 (pc p q)) := compT_unpack hp hq

theorem tblEq_eq {p q : Nat} (hp : Cn p) (hq : Cn q) :
    tblEq 11200 (tabT (unpack 11200 14 p)) (tabT (unpack 11200 14 q)) = Nat.beq p q :=
  tblEq_unpack hp hq

theorem commTT_eq {p q : Nat} (hp : Cn p) (hq : Cn q) :
    commTT 11200 (tabT (unpack 11200 14 p)) (tabT (unpack 11200 14 q)) =
      Nat.beq (pc p q) (pc q p) := commTT_unpack hp hq

theorem invT_eq {p r : Nat} (h : invEqK 11200 14 (mask 14) (11200 * 14) p r = true) :
    invT 11200 (tabT (unpack 11200 14 p)) = tabT (unpack 11200 14 r) :=
  invT_unpack (lt_of_canonK cId) h

theorem evalW_foldl {n w : Nat} {G GI : Fin 6 → Nat} {g gi : Fin 6 → Table}
    (hg : ∀ i, g i = tabT (unpack n w (G i)) ∧ canonK n w (mask w) (n * w) (G i) = true)
    (hgi : ∀ i, gi i = tabT (unpack n w (GI i)) ∧ canonK n w (mask w) (n * w) (GI i) = true) :
    ∀ (wd : List (Fin 6 × Bool)) (acc : Nat), canonK n w (mask w) (n * w) acc = true →
      wd.foldl (fun a l => compT n a (if l.2 then g l.1 else gi l.1)) (tabT (unpack n w acc)) =
        tabT (unpack n w (wd.foldl (fun a l => pcomp n w (mask w) a (cond l.2 (G l.1) (GI l.1)))
          acc)) ∧
      canonK n w (mask w) (n * w)
        (wd.foldl (fun a l => pcomp n w (mask w) a (cond l.2 (G l.1) (GI l.1))) acc) = true
  | [], acc, ha => ⟨rfl, ha⟩
  | l :: rest, acc, ha => by
    have hl : (if l.2 then g l.1 else gi l.1) = tabT (unpack n w (cond l.2 (G l.1) (GI l.1))) ∧
        canonK n w (mask w) (n * w) (cond l.2 (G l.1) (GI l.1)) = true := by
      cases l.2
      · exact hgi l.1
      · exact hg l.1
    rw [List.foldl_cons, List.foldl_cons, hl.1, compT_unpack ha hl.2]
    exact evalW_foldl hg hgi rest _ (CFSG.KC.BfsPin.canonK_pcomp ha hl.2)

theorem evalW_eq {G GI : Fin 6 → Nat} {g gi : Fin 6 → Table}
    (hg : ∀ i, g i = tabT (unpack 11200 14 (G i)) ∧ Cn (G i))
    (hgi : ∀ i, gi i = tabT (unpack 11200 14 (GI i)) ∧ Cn (GI i)) (wd : List (Fin 6 × Bool)) :
    evalW 11200 g gi wd = tabT (unpack 11200 14 (EVK G GI wd)) ∧ Cn (EVK G GI wd) := by
  unfold evalW EVK
  rw [idT_eq]
  exact evalW_foldl hg hgi wd idK cId

theorem pows_pw (p : Nat) : Pows 11200 14 p (pw p) :=
  ⟨rfl, fun e => by
    change CFSG.KC.Enum.strictN (pw p e) (fun q => pcomp 11200 14 (mask 14) p q) = _
    cases pw p e <;> rfl⟩

theorem powT_eq {p : Nat} (hp : Cn p) (e : Nat) :
    powT 11200 e (tabT (unpack 11200 14 p)) = tabT (unpack 11200 14 (pw p e)) ∧ Cn (pw p e) :=
  ⟨powT_unpack (pows_pw p) idT_eq cId hp e, pows_canon (pows_pw p) cId hp e⟩

theorem involOK_eq {p : Nat} (hp : Cn p) :
    involOK 11200 (tabT (unpack 11200 14 p)) =
      bAnd(Nat.beq (pc p p) idK, bIf(Nat.beq p idK, false, true)) :=
  involOK_unpack' (by decide) idT_eq cId hp

theorem harYs_all {f : Table → Bool} (h : ∀ i : Fin 6, f (tabT (unpack 11200 14 (HY.F i.val))) = true) :
    harYs.all f = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
  have e := harY_eq i
  rw [e]
  exact h i

theorem fixCnt_unpack {n w p : Nat} (hp : canonK n w (mask w) (n * w) p = true) :
    fixCnt n (tabT (unpack n w p)) = CFSG.KC.PkPow.nfix n w p := by
  unfold fixCnt CFSG.KC.PkPow.nfix
  rw [CFSG.KC.Misc.RuInv.P.foldN_count, ← List.map_coe_finRange_eq_range, List.filter_map,
    List.length_map]
  apply congrArg List.length
  apply List.filter_congr
  intro i _
  have hl := unpack_lt (i := i.val) hp
  rw [Function.comp_apply, ap_tabT _ hl, CFSG.KS.Raw.Orb.unpack_get i.isLt, Bool.eq_iff_iff,
    beq_iff_eq, Nat.beq_eq]

theorem lettersOK_getD {Ls : List (List Nat)} (h : Ls.all lettersOK = true) (j : Nat) :
    lettersOK (Ls.getD j []) = true := by
  rw [List.getD_eq_getElem?_getD]
  cases hj : Ls[j]? with
  | none => rfl
  | some w => exact List.all_eq_true.1 h w (List.mem_of_getElem? hj)

theorem lettersOK_reverse {wd : List Nat} (h : lettersOK wd = true) : lettersOK wd.reverse = true := by
  unfold lettersOK at h ⊢
  rw [List.all_reverse]
  exact h

theorem sigWords_letters : sigWords.all lettersOK = true := by decide

theorem lettersOK_sigWord (wd : List Nat) : lettersOK (sigWord wd) = true := by
  unfold sigWord lettersOK
  rw [List.all_eq_true]
  intro l hl
  simp only [List.mem_flatten, List.mem_map] at hl
  obtain ⟨_, ⟨a, _, rfl⟩, hl⟩ := hl
  exact List.all_eq_true.1 (lettersOK_getD sigWords_letters (a - 1)) l hl

theorem word_inv {wd : List Nat} (h : lettersOK wd = true)
    (hi : invEqK 11200 14 (mask 14) (11200 * 14) (WK wd) (WKI wd) = true) :
    wordTbl 11200 harYs wd = tabT (unpack 11200 14 (WK wd)) ∧ Cn (WK wd) ∧
      invT 11200 (wordTbl 11200 harYs wd) = tabT (unpack 11200 14 (WKI wd)) ∧ Cn (WKI wd) ∧
      permOK 11200 (wordTbl 11200 harYs wd) = true ∧
      invOK 11200 (wordTbl 11200 harYs wd) (invT 11200 (wordTbl 11200 harYs wd)) = true := by
  obtain ⟨e, c⟩ := wordTbl_eq h
  have ci : Cn (WKI wd) := (wordTbl_eq (lettersOK_reverse h)).2
  have ei : invT 11200 (wordTbl 11200 harYs wd) = tabT (unpack 11200 14 (WKI wd)) := by
    rw [e]
    exact invT_eq hi
  refine ⟨e, c, ei, ci, ?_, ?_⟩
  · rw [e]
    exact permOK_unpack c hi
  · rw [ei, e]
    exact invOK_unpack c ci hi

theorem fixCnt_eq {p : Nat} (hp : Cn p) : fixCnt 11200 (tabT (unpack 11200 14 p)) = fx p :=
  fixCnt_unpack hp

end CFSG.KD.TwoHS

end
