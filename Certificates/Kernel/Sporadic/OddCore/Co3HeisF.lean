module

public import Certificates.Kernel.Sporadic.OddCore.Co3FusF
public import Certificates.Kernel.Sporadic.OddCore.Co3Heis
public import Certificates.Kernel.Sporadic.OddCore.CentGlue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co3Fus

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier.Co3 CFSG.KC.Enum CFSG.KS CFSG.KS.Raw
open CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KC.BfsPin CFSG.Monster.B.Co2.Native
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

theorem heis_tab {k : Nat} (hk : k < 4) : co3HeisTbl k = tabT (unpack 276 9 (Co3HT.F k)) := by
  have h := CFSG.KC.Misc.HexFlat.hexT_sound Co3HT.all (by norm_num) k hk
  rw [← Co3HT.eq] at h
  rw [← h, tabT_natArr]
  rfl

theorem hTab_facts {k : Nat} (h : hTabK k = true) :
    canonK 276 9 (mask 9) (276 * 9) (Co3HT.F k) = true ∧
      invEqK 276 9 (mask 9) (276 * 9) (Co3HT.F k) (Co3HI k) = true ∧
      canonK 276 9 (mask 9) (276 * 9) (Co3HI k) = true ∧ Co3Text.hiOK (Co3HT.F k) = true ∧
      Co3C.sift (Co3HT.F k) = true ∧ Nat.beq (pw (Co3HT.F k) 5) idK = true := by
  simpa only [hTabK, bAnd_iff] using h

theorem pows (X : Nat) : Pows 276 9 X (pw X) := ⟨rfl, fun _ => rfl⟩

theorem sift_tab {k : Nat} (h : hTabK k = true) : co3Sift (tabT (unpack 276 9 (Co3HT.F k))) = true := by
  obtain ⟨h1, -, -, h4, h5, -⟩ := hTab_facts h
  unfold co3Sift
  rw [natArr_tabT h1]
  exact siftK_soundR Co3C.binds Co3C.perm Co3C.hl rfl (Nat.eq_of_beq_eq_true h4)
    (range_of_canonK h1) h5

theorem tau_tab {c : Nat} (hc : c < 2) :
    co3HeisTau c = tabT (unpack 276 9 (hTau c)) ∧ canonK 276 9 (mask 9) (276 * 9) (hTau c) = true := by
  rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
  · refine ⟨?_, base.2.2.2.1⟩
    unfold co3HeisTau co3ZTbl
    rw [if_pos rfl, CertificateChecks.KernelSpor.Co3Single.z_eq]
    rfl
  · refine ⟨?_, base.2.2.2.2.1⟩
    unfold co3HeisTau co3TtTbl
    rw [if_neg (by decide), CertificateChecks.KernelSpor.Co3Single.tt_eq]
    rfl

theorem heis_class {c : Nat} (hc : c < 2) (h : heisK c = true) : co3HeisOK c = true := by
  unfold heisK at h
  simp only [bAnd_iff] at h
  obtain ⟨hx, hy, hw5, hw1, hxw, hyw, htau⟩ := h
  obtain ⟨x1, x2, x3, -, -, x6⟩ := hTab_facts hx
  obtain ⟨y1, y2, y3, -, -, y6⟩ := hTab_facts hy
  obtain ⟨ht, htc⟩ := tau_tab hc
  have hX := heis_tab (k := 2 * c) (by omega)
  have hY := heis_tab (k := 2 * c + 1) (by omega)
  have hXi := invT_unpack (by norm_num) x2
  have hYi := invT_unpack (by norm_num) y2
  have hWc : canonK 276 9 (mask 9) (276 * 9) (hW c) = true :=
    canonK_pcomp (canonK_pcomp (canonK_pcomp x3 y3) x1) y1
  have hW' : co3HeisW c = tabT (unpack 276 9 (hW c)) := by
    unfold co3HeisW
    rw [hX, hY, hXi, hYi, compT_unpack x3 y3, compT_unpack (canonK_pcomp x3 y3) x1,
      compT_unpack (canonK_pcomp (canonK_pcomp x3 y3) x1) y1]
    rfl
  unfold co3HeisOK
  simp only []
  rw [hW', hX, hY, hXi, hYi, ht, permOK_unpack x1 x2, permOK_unpack y1 y2,
    invOK_unpack x1 x3 x2, invOK_unpack y1 y3 y2, sift_tab hx, sift_tab hy,
    powT_unpack (pows _) hid hidc x1, powT_unpack (pows _) hid hidc y1,
    powT_unpack (pows _) hid hidc hWc, hid,
    tblEq_unpack (pows_canon (pows _) hidc x1 5) hidc,
    tblEq_unpack (pows_canon (pows _) hidc y1 5) hidc,
    tblEq_unpack (pows_canon (pows _) hidc hWc 5) hidc, tblEq_unpack hWc hidc,
    commTT_unpack x1 hWc, commTT_unpack y1 hWc, compT_unpack htc x1,
    compT_unpack (canonK_pcomp htc x1) htc, tblEq_unpack (canonK_pcomp (canonK_pcomp htc x1) htc) x3]
  have e6 : Nat.beq (pw (Co3HT.F (2 * c)) 5) (pidn 276 9) = true := x6
  have e7 : Nat.beq (pw (Co3HT.F (2 * c + 1)) 5) (pidn 276 9) = true := y6
  have e8 : Nat.beq (pw (hW c) 5) (pidn 276 9) = true := hw5
  have e9 : Nat.beq (hW c) (pidn 276 9) = false := by
    revert hw1
    unfold idK
    cases Nat.beq (hW c) (pidn 276 9) <;> decide
  unfold pc at hxw hyw htau
  rw [e6, e7, e8, e9, hxw, hyw, htau]
  rfl

theorem facts129004 : co3HeisCheck () = true := by
  have h := heis_ok
  simp only [bAnd_iff] at h
  unfold co3HeisCheck
  rw [heis_class (by norm_num) h.1, heis_class (by norm_num) h.2]
  rfl

@[expose] noncomputable def fE (i : Nat) : Table := tabT (unpack 276 9 (Co3E.T i))

theorem aEnt_eq {i : Nat} (hi : i < Co3E.cnt) : co3AEnt (fE i) = aEntK i := by
  unfold co3AEnt aEntK fE
  rw [involOK_unpack (e_canon i hi)]
  cases h : involK (Co3E.T i)
  · rfl
  · rw [anyZ hi h]
    rfl

theorem ER_toList : ER.1.toList = (List.range 1024).map fE := by
  simp only [ER, hRec, Array.toList_ofFn]
  rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map, hcnt]
  rfl

theorem aList_eq : (ER.1.filter co3AEnt).toList = aIdx.map fE := by
  rw [Array.toList_filter, ER_toList, List.filter_map, aIdx]
  congr 1
  apply List.filter_congr
  intro i hi
  exact aEnt_eq (by rw [hcnt]; exact List.mem_range.1 hi)

theorem comm_eq {i j : Nat} (hi : i < 1024) (hj : j < 1024) :
    commTT 276 (fE i) (fE j) = commK i j := by
  unfold fE commK
  rw [commTT_unpack (e_canon i (by rw [hcnt]; exact hi)) (e_canon j (by rw [hcnt]; exact hj))]
  rfl

theorem size_filter_toArray {α : Type} (L : List α) (f : α → Bool) :
    (L.toArray.filter f).size = L.countP f := by
  rw [← Array.length_toList, Array.toList_filter, List.countP_eq_length_filter]

theorem mem_aIdx {i : Nat} (h : i ∈ aIdx) : i < 1024 :=
  List.mem_range.1 (List.mem_filter.1 h).1

theorem facts129005 : co3RankCheck () = true := by
  unfold co3RankCheck
  simp only []
  rw [e_sound.1, decide_eq_true_eq]
  have hA : ER.1.filter co3AEnt = (aIdx.map fE).toArray := by
    rw [← aList_eq, Array.toArray_toList]
  rw [hA, List.filter_toArray, List.size_toArray, ← List.countP_eq_length_filter,
    List.countP_map]
  have h := rank_ok
  unfold rankK at h
  rw [decide_eq_true_eq] at h
  refine le_of_eq_of_le ?_ h
  apply List.countP_congr
  intro i hi
  simp only [Function.comp]
  rw [size_filter_toArray, List.countP_map,
    List.countP_congr (q := fun j => commK i j) fun j hj => by
      simp only [Function.comp, comm_eq (mem_aIdx hi) (mem_aIdx hj)]]

end CertificateChecks.KernelSpor.Co3Fus

end
