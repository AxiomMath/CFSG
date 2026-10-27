module

public import Certificates.Kernel.TwoHS.HYWords
public import Certificates.Kernel.Sporadic.OddCore.MulHGlue
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.PackWord
public import CFSG.Certificates.Kernel.BfsPinAlg

public section

namespace CFSG.KD.TwoHS

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH
open CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native

abbrev Cn (p : Nat) : Prop := canonK 11200 14 (mask 14) (11200 * 14) p = true

theorem hn : szOK 11200 14 = true := by decide

theorem cId : Cn idK := (CFSG.KC.BfsPin.PP.id hn).1

theorem hy {j : Nat} (hj : j < 6) :
    Cn (HY.F j) ∧ invEqK 11200 14 (mask 14) (11200 * 14) (HY.F j) (HY.F j) = true := by
  have h := allN_spec hy_ok j hj
  exact (bAnd_iff _ _).1 h

theorem harY_eq (i : Fin 6) : harY i = tabT (unpack 11200 14 (HY.F i.val)) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound HY.all (by norm_num) i.val i.isLt
  rw [← HY.eq] at h
  rw [← h, tabT_natArr]
  rfl

theorem idT_eq : idT 11200 = tabT (unpack 11200 14 idK) := by
  rw [idT_tabT, CFSG.KC.BfsPin.idA_eq hn]
  rfl

theorem harYs_getD {l : Nat} (h1 : 1 ≤ l) (h6 : l ≤ 6) :
    harYs.getD (l - 1) (idT 11200) = tabT (unpack 11200 14 (L l)) ∧ Cn (L l) := by
  have hl : l - 1 < 6 := by omega
  refine ⟨?_, (hy hl).1⟩
  have e : harYs.getD (l - 1) (idT 11200) = harY ⟨l - 1, hl⟩ := by
    simp [harYs, List.getD_eq_getElem?_getD, hl]
  rw [e, harY_eq]
  rfl

theorem lettersOK_spec {wd : List Nat} (h : lettersOK wd = true) : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 6 := by
  intro l hl
  have := List.all_eq_true.1 h l hl
  simpa using this

theorem wordTbl_eq {wd : List Nat} (h : lettersOK wd = true) :
    wordTbl 11200 harYs wd = tabT (unpack 11200 14 (WK wd)) ∧ Cn (WK wd) :=
  wordTbl_unpack idT_eq cId fun l hl =>
    harYs_getD (lettersOK_spec h l hl).1 (lettersOK_spec h l hl).2

theorem tblEq_wordTbl {u v : List Nat} (hu : lettersOK u = true) (hv : lettersOK v = true) :
    tblEq 11200 (wordTbl 11200 harYs u) (wordTbl 11200 harYs v) = Nat.beq (WK u) (WK v) := by
  rw [(wordTbl_eq hu).1, (wordTbl_eq hv).1]
  exact tblEq_unpack (wordTbl_eq hu).2 (wordTbl_eq hv).2

theorem harUW_letters : ∀ j < 3, lettersOK (harUW.getD j []) = true := by decide

theorem harU_getD {l : Nat} (h1 : 1 ≤ l) (h3 : l ≤ 3) :
    harU.getD (l - 1) (idT 11200) = tabT (unpack 11200 14 (UL l)) ∧ Cn (UL l) := by
  have hl : l - 1 < 3 := by omega
  have e : harU.getD (l - 1) (idT 11200) = wordTbl 11200 harYs (harUW.getD (l - 1) []) := by
    rcases (by omega : l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl <;>
      simp only [harU, harUW, List.map_cons, List.map_nil, Nat.reduceSub, Nat.sub_self,
        List.getD_cons_zero, List.getD_cons_succ]
  rw [e]
  exact wordTbl_eq (harUW_letters _ hl)

theorem tU_eq {wd : List Nat} (h : ∀ l ∈ wd, 1 ≤ l ∧ l ≤ 3) :
    tU wd = tabT (unpack 11200 14 (UK wd)) ∧ Cn (UK wd) :=
  wordTbl_unpack idT_eq cId fun l hl => harU_getD (h l hl).1 (h l hl).2

theorem tblEq_eq_wEq :
    (fun u v => tblEq 11200 (wordTbl 11200 harYs u) (wordTbl 11200 harYs v)) = wEq := by
  funext u v
  unfold wEq
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    exact tblEq_wordTbl h.1 h.2
  · rfl

end CFSG.KD.TwoHS

end
