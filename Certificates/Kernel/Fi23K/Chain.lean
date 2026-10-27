module

public import Certificates.Kernel.Fi23K.Letters
public import CFSG.Certificates.Kernel.Spor.PChainSound
import Certificates.Kernel.Fi23K.Tree0
import Certificates.Kernel.Fi23K.Tree1
import Certificates.Kernel.Fi23K.Tree2
import Certificates.Kernel.Fi23K.Tree3
import Certificates.Kernel.Fi23K.Tree4
import Certificates.Kernel.Fi23K.TreeH
import Certificates.Kernel.Fi23K.Misc
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
public import CFSG.Certificates.Kernel.Spor.RawSound
public import Mathlib.GroupTheory.Perm.Basic

public section

set_option maxRecDepth 400000

#kon_join CFSG.KD.Fi23K.t0All CFSG.KD.Fi23K.t0Sl 16
#kon_join CFSG.KD.Fi23K.t2All CFSG.KD.Fi23K.t2Sl 13
#kon_join CFSG.KD.Fi23K.t6All CFSG.KD.Fi23K.t6Sl 14
#kon_join CFSG.KD.Fi23K.hdAll CFSG.KD.Fi23K.hdAt 7

namespace CFSG.KD.Fi23K

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KC.Fi23K
  CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm.Native

theorem sl_spec {n cnt r lo len : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} (h : tbfsSlK n cnt r L LV PTS POS PAR LAB TI lo len = true) :
    ∀ k, lo ≤ k → k < lo + len → k < cnt → tbfsPtK n cnt r L LV PTS POS PAR LAB TI k = true := by
  intro k h1 h2 h3
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h (k - lo) (by omega)
  rw [CFSG.KS.Raw.Orb.strictB_eq] at h'
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  rw [e, CFSG.KS.Raw.Orb.bIf_eq, if_pos (Nat.blt_eq.mpr h3)] at h'
  exact h'

@[expose] noncomputable def PTSJ (i : Nat) : Nat → Nat := TT i 0
@[expose] noncomputable def POSJ (i : Nat) : Nat → Nat := TT i 1
@[expose] noncomputable def PARJ (i : Nat) : Nat → Nat := TT i 2
@[expose] noncomputable def LABJ (i : Nat) : Nat → Nat := TT i 3
@[expose] noncomputable def TIJ (i : Nat) : Nat → Nat := TT i 4

theorem pt_of {i c : Nat} (h : treeSl i c = true) : ∀ k, 2048 * c ≤ k → k < 2048 * c + 2048 →
    k < CNT i → tbfsPtK 31671 (CNT i) (lvK LL BB 24 (lvOf i)).length LL (lvAt LL BB 24 (lvOf i))
      (PTSJ i) (POSJ i) (PARJ i) (LABJ i) (TIJ i) k = true := by
  intro k h1 h2 h3
  unfold treeSl treeK at h
  exact sl_spec h k (by change c * 2048 ≤ k; omega) (by change k < c * 2048 + 2048; omega) h3

theorem small : treeSl 1 0 = true ∧ treeSl 1 1 = true ∧ treeSl 3 0 = true ∧ treeSl 4 0 = true ∧
    treeSl 5 0 = true := by
  have h := small_ok
  unfold tSmall at h
  simp only [CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  exact h

theorem tree_pts {i : Nat} (hi : i < 7) : ∀ k < CNT i, tbfsPtK 31671 (CNT i)
    (lvK LL BB 24 (lvOf i)).length LL (lvAt LL BB 24 (lvOf i)) (PTSJ i) (POSJ i) (PARJ i)
      (LABJ i) (TIJ i) k = true := by
  intro k hk
  obtain ⟨s10, s11, s30, s40, s50⟩ := small
  interval_cases i
  · exact pt_of (t0All (k / 2048) (by change k / 2048 < 16; change k < 31671 at hk; omega)) k
      (by omega) (by omega) hk
  · change k < 3510 at hk
    rcases (by omega : k < 2048 ∨ 2048 ≤ k) with h | h
    · exact pt_of s10 k (by omega) (by omega) (by change k < 3510; omega)
    · exact pt_of s11 k (by omega) (by omega) (by change k < 3510; omega)
  · exact pt_of (t2All (k / 2048) (by change k / 2048 < 13; change k < 25344 at hk; omega)) k
      (by omega) (by omega) hk
  · exact pt_of s30 k (by omega) (by change k < 288 at hk; omega) hk
  · exact pt_of s40 k (by omega) (by change k < 1260 at hk; omega) hk
  · exact pt_of s50 k (by omega) (by change k < 4 at hk; omega) hk
  · exact pt_of (t6All (k / 2048) (by change k / 2048 < 14; change k < 28160 at hk; omega)) k
      (by omega) (by omega) hk

theorem tree_spec {i : Nat} (hi : i < 6) :
    tbfsHdK 31671 (BB i) (CNT i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i) = true ∧
      ∀ k < CNT i, tbfsPtK 31671 (CNT i) (lvK LL BB 24 i).length LL (lvAt LL BB 24 i) (PTSJ i)
        (POSJ i) (PARJ i) (LABJ i) (TIJ i) k = true := by
  have hl : lvOf i = i := by interval_cases i <;> rfl
  have hr : rootOf i = BB i := by interval_cases i <;> rfl
  have hh := hdAll i (by change i < 7; omega)
  unfold hdAt at hh
  rw [hr] at hh
  refine ⟨hh, fun k hk => ?_⟩
  have := tree_pts (i := i) (by omega) k hk
  rw [hl] at this
  exact this

theorem inv_ok : invK LL 31671 24 = true := by
  unfold invK
  rw [CFSG.KS.Raw.Orb.allN_iff]
  intro j hj
  change j < 12 at hj
  rw [CFSG.KS.Raw.Orb.allN_iff]
  intro x hx
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.bAnd_eq,
    Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq, Nat.beq_eq]
  have e0 : Nat.mul 2 j = 2 * j := rfl
  have e1 : Nat.succ (Nat.mul 2 j) = 2 * j + 1 := rfl
  rw [e1, e0]
  exact ⟨LL_lt (by omega) hx, LL_lt (by omega) hx, letter_inv hj hx⟩

theorem chain_hyp : ChainHyp 31671 24 6 (chainLetters orbLit) chainBase chainQ (chainQb ()) LL BB
    [0, 1, 2, 3, 4, 5] BB CNT PTSJ POSJ PARJ LABJ TIJ where
  letters := ⟨letters_TR.1, fun l hl x hx => ((letters_TR.2 l hl).2 x hx).1⟩
  inv := ⟨rfl, inv_ok⟩
  base := ⟨rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide⟩⟩
  chk := ⟨rfl, by decide, rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide, rfl⟩⟩
  tree := fun i hi => tree_spec hi

theorem prod_cnt : ((List.range 6).map CNT).prod = 4089470473293004800 := by
  decide +kernel

abbrev Hcard : Prop :=
  Nat.card (Subgroup.closure (Set.range fun l : Fin 24 =>
    permOfT 31671 (chainLetters orbLit)[l.val]!)) ≤ 4089470473293004800

theorem chain_eq (hcard : Hcard) : chainTrees 31671 (chainLetters orbLit) chainBase =
      Array.ofFn (n := 6) (fun i => tbfsRec 31671 (CNT i.val) (PTSJ i.val) (POSJ i.val)
        (PARJ i.val) (LABJ i.val)) ∧
    ∀ chunks, chainOK 31671 (chainLetters orbLit) chainBase chainQ (chainQb ())
      (chainTrees 31671 (chainLetters orbLit) chainBase) chunks = true :=
  pchain_of_card chain_hyp (hcard.trans (le_of_eq prod_cnt.symm))

theorem lv1_eq : levelLetters (chainLetters orbLit) chainBase 1 = (lvK LL BB 24 1).toArray :=
  levelLetters_eq chain_hyp 1 (by norm_num)

theorem t2_eq : treeBFS 31671 (subRoot ()) (chainLetters orbLit)
      (levelLetters (chainLetters orbLit) chainBase 1) =
        tbfsRec 31671 (CNT 6) (PTSJ 6) (POSJ 6) (PARJ 6) (LABJ 6) ∧
    treeOK 31671 (subRoot ()) (tbfsRec 31671 (CNT 6) (PTSJ 6) (POSJ 6) (PARJ 6) (LABJ 6))
      (chainLetters orbLit) (levelLetters (chainLetters orbLit) chainBase 1) = true := by
  rw [lv1_eq]
  have hh := hdAll 6 (by change 6 < 7; omega)
  unfold hdAt at hh
  have hp := tree_pts (i := 6) (by omega)
  have hl6 : lvOf 6 = 1 := rfl
  rw [hl6] at hp
  refine tbfsK_sound (L := LL) (LV := lvAt LL BB 24 1) (TI := TIJ 6) ⟨by simp, fun t ht => ?_⟩ hh hp
  have ht' : t < (lvK LL BB 24 1).length := by simpa using ht
  have hm := List.getElem_mem ht'
  have hlt : (lvK LL BB 24 1)[t] < 24 := by
    unfold lvK at hm
    exact List.mem_range.1 (List.mem_filter.1 hm).1
  have e : (lvK LL BB 24 1).toArray[t]! = lvAt LL BB 24 1 t := by
    rw [getElem!_pos _ t (by simpa using ht')]
    simp [lvAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
  rw [e]
  have e2 : lvAt LL BB 24 1 t = (lvK LL BB 24 1)[t] := by
    simp [lvAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht']
  rw [e2]
  exact ⟨rfl, by rw [letters_TR.1]; exact hlt, fun x hx => ((letters_TR.2 _ hlt).2 x hx).1⟩

end CFSG.KD.Fi23K

end
