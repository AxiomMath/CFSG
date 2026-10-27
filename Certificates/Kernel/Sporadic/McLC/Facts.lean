module

public import Certificates.Kernel.Sporadic.McLC.Checks
public import Certificates.Kernel.Sporadic.McLC.CoverA
public import Certificates.Kernel.Sporadic.McLC.CoverB
public import Certificates.Kernel.Sporadic.McLC.CoverC
public import Certificates.Kernel.Sporadic.McLC.CoverD
public import Certificates.Kernel.Sporadic.McLC.Gen
public import CFSG.Certificates.Kernel.Spor.PChainSound
public import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.LocalCompSPCode
import Certificates.Kernel.Sporadic.ON.Gen
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
public import Mathlib.GroupTheory.Perm.Basic
import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
import CFSG.RankThree.Native.PermEnumeration

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.McLC.sch0All CertificateChecks.KernelSpor.McLC.sch0 5
#kon_join CertificateChecks.KernelSpor.McLC.coverSlAll CertificateChecks.KernelSpor.McLC.coverSl 20

namespace CertificateChecks.KernelSpor.McLC

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC
open CFSG.Sporadic.Th.Native CFSG.Perm.Native

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

@[expose] noncomputable def lettersK : Array Table :=
  Array.ofFn (n := 10) fun l => Array.ofFn (n := 275) fun x => UInt32.ofNat (LJ l.val x.val)

@[expose] noncomputable def baseK : Array Nat := #[0, 14, 2]

@[expose] noncomputable def QK : Array Nat := (List.range 275).toArray

theorem inv_spec {j x : Nat} (hj : j < 5) (hx : x < 275) : LJ (2 * j) x < 275 ∧
    LJ (2 * j + 1) x < 275 ∧ LJ (2 * j + 1) (LJ (2 * j) x) = x := by
  have h0 : invK LJ 275 NL = true := invL_ok
  unfold invK at h0
  have hj' : j < Nat.div NL 2 := by change j < 10 / 2; omega
  have h := allN_spec (allN_spec h0 j hj') x hx
  rw [strictB_eq] at h
  simp only [bAnd_iff, Nat.blt_eq, Nat.beq_eq] at h
  exact h

theorem LJ_lt {l x : Nat} (hl : l < 10) (hx : x < 275) : LJ l x < 275 := by
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · exact (inv_spec (by omega) hx).1
  · exact (inv_spec (by omega) hx).2.1

theorem letters_get : lettersK.size = 10 ∧ ∀ l < 10, ∀ x < 275, ap lettersK[l]! x = LJ l x := by
  refine ⟨by simp [lettersK], fun l hl x hx => ?_⟩
  unfold ap lettersK
  rw [getElem!_pos _ l (by simpa using hl), Array.getElem_ofFn,
    getElem!_pos _ x (by simpa using hx), Array.getElem_ofFn, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le (LJ_lt hl hx) (by norm_num))

theorem tree_spec {i : Nat} (hi : i < 3) :
    tbfsHdK 275 (BJ i) (CNTJ i) (PTSJ i) (POSJ i) (PARJ i) (LABJ i) = true ∧
      ∀ k < CNTJ i, tbfsPtK 275 (CNTJ i) (lvK LJ BJ NL i).length LJ (lvAt LJ BJ NL i) (PTSJ i)
        (POSJ i) (PARJ i) (LABJ i) (TIJ i) k = true := by
  have h := allN_spec tree_ok i hi
  unfold tree at h
  rw [bAnd_iff] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, allN_spec h2⟩

theorem schSl_spec {i lo len : Nat}
    (h : schSlK LJ BJ NL PTSJ POSJ PARJ LABJ CNTJ QB QL 3 i lo len = true) :
    ∀ k, lo ≤ k → k < lo + len → k < CNTJ i → ∀ t < (lvK LJ BJ NL i).length,
      schK LJ PTSJ POSJ PARJ LABJ CNTJ QB QL 3 i (lvAt LJ BJ NL i t) k = true := by
  intro k h1 h2 h3 t ht
  unfold schSlK at h
  rw [strictB_eq] at h
  have h' := allN_spec h (k - lo) (by omega)
  rw [strictB_eq] at h'
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  rw [e, Eq.mpr Nat.blt_eq h3] at h'
  exact allN_spec h' t ht

theorem cnt0 : CNTJ 0 = 240 := rfl

theorem sch_spec : ∀ i < 3, ∀ k < CNTJ i, ∀ t < (lvK LJ BJ NL i).length,
    schK LJ PTSJ POSJ PARJ LABJ CNTJ QB QL 3 i (lvAt LJ BJ NL i t) k = true := by
  intro i hi k hk
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have hs : k / 48 < 5 := by rw [cnt0] at hk; omega
    exact schSl_spec (sch0All (k / 48) hs) k (by simp only [Nat.mul_eq]; omega)
      (by simp only [Nat.mul_eq]; omega) hk
  · obtain ⟨j, rfl⟩ : ∃ j, i = Nat.succ j := ⟨i - 1, by omega⟩
    have h := allN_spec schR_ok j (by omega)
    unfold schR at h
    exact schSl_spec h k (Nat.zero_le _) (by omega) hk

theorem chain_hyp : ChainHyp 275 10 3 lettersK baseK QK baseK LJ BJ QL QB
    CNTJ PTSJ POSJ PARJ LABJ TIJ where
  letters := letters_get
  inv := ⟨rfl, invL_ok⟩
  base := ⟨rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide⟩⟩
  chk := ⟨by simp [QK, QL], fun t ht => by
      simp only [QL, List.length_range] at ht
      simp [QL, List.getD_eq_getElem?_getD, ht], rfl,
    fun i hi => by interval_cases i <;> exact ⟨rfl, by decide, by decide⟩⟩
  tree := fun i hi => tree_spec hi

theorem chain_eq : chainTrees 275 lettersK baseK =
      Array.ofFn (n := 3) (fun i => tbfsRec 275 (CNTJ i.val) (PTSJ i.val) (POSJ i.val) (PARJ i.val)
        (LABJ i.val)) ∧
    ∀ chunks, chainOK 275 lettersK baseK QK baseK (chainTrees 275 lettersK baseK) chunks = true :=
  pchainK_sound chain_hyp sch_spec term_ok

theorem cover_all : ∀ t < 40320, coverW t (r32 WT t) = true := by
  intro t ht
  have hs : t / 2016 < 20 := by omega
  have h := coverSlAll (t / 2016) hs
  unfold coverSl at h
  have h' := allN_spec h (t % 2016) (Nat.mod_lt _ (by norm_num))
  rw [strictB_eq] at h'
  have e : Nat.add (Nat.mul (t / 2016) 2016) (t % 2016) = t := by
    change t / 2016 * 2016 + t % 2016 = t
    omega
  rwa [e] at h'

end CertificateChecks.KernelSpor.McLC

end
