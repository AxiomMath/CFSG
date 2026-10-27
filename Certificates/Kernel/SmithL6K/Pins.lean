module

public import Certificates.Kernel.SmithL6K.PinsA
public import Certificates.Kernel.SmithL6K.PinsW
public import Certificates.Kernel.SmithL6K.PinsC
public import CFSG.Certificates.Kernel.SmithL6KSound

public section

namespace CertificateChecks.KernelSmithL6K

open CFSG.SmithL6 CFSG.SmithL6.K CFSG.SmithL6.Kernel

theorem tvc_eq : tvList.toList.map codeOf = tvc := by
  have h := pin_tv
  unfold pinTv at h
  exact beq_iff_eq.mp h

theorem tvc_length : tvc.length = 1953 := by
  rw [← tvc_eq, List.length_map, Array.length_toList, tvList_size]

theorem tvPair_code {k : Nat} (hk : k < 1953) : codeOf (tvPair k) = tvc.getD k 0 := by
  rw [getD_of_lt (by rw [tvc_length]; exact hk)]
  simp only [← tvc_eq, List.getElem_map]
  rw [tvPair_get hk]

theorem fld_tcP {k : Nat} (hk : k < 1953) : fldW 12 tcP k = codeOf (tvPair k) := by
  have e := pinF_get pin_tcP (s := k) (by rw [tvc_length]; exact hk)
  rw [Nat.zero_add] at e
  rw [e, tvPair_code hk, getD_of_lt (by rw [tvc_length]; exact hk)]

theorem fld_idxP {n : Nat} (hn : n < 4096) : fldW 11 idxP n = tvIdxTab[n]! :=
  idx_of_pinIdx (fun _ hk => fld_tcP hk) pin_idx hn

theorem tvImgP_tvImg {j a : Nat} (hj : j < 1953) (ha : a < 1953) :
    tvImgP tcP idxP j a = tvImg j a :=
  tvImgP_eq (fun _ hk => fld_tcP hk) (fun _ hn => fld_idxP hn) hj ha

theorem wData_length : wData.toList.length = 1395 := by decide +kernel

theorem wData_get {i : Nat} (hi : i < 1395) :
    wData[i]! = wData.toList[i]'(by rw [wData_length]; exact hi) := by
  rw [getElem!_pos wData i (by rw [← Array.length_toList, wData_length]; exact hi),
    Array.getElem_toList]

theorem wt_eq {i : Nat} (hi : i < 1395) : wt i = wtd.getD i 0 := by
  have hl : i < wData.toList.length := by rw [wData_length]; exact hi
  have e : wt i = wtC wData.toList[i] := by
    rw [← wData_get hi]
    rfl
  rw [e]
  rcases Nat.lt_or_ge i 349 with h0 | h0
  · exact pinMapR_get pin_wt0 (by omega) (by omega) hl
  rcases Nat.lt_or_ge i 698 with h1 | h1
  · exact pinMapR_get pin_wt1 (by omega) (by omega) hl
  rcases Nat.lt_or_ge i 1047 with h2 | h2
  · exact pinMapR_get pin_wt2 (by omega) (by omega) hl
  · exact pinMapR_get pin_wt3 (by omega) (by omega) hl

theorem wMask_eq {i : Nat} (hi : i < 1395) : wMask i = wmk.getD i 0 := by
  have hl : i < wData.toList.length := by rw [wData_length]; exact hi
  have e : wMask i = maskC wData.toList[i] := by
    rw [← wData_get hi]
    rfl
  rw [e]
  exact pinMapR_get pin_mask (by omega) (by omega) hl

theorem annK_eq {i : Nat} (hi : i < 1395) : annK i = anm.getD i 0 := by
  have hl : i < wData.toList.length := by rw [wData_length]; exact hi
  have e : annK i = annC wData.toList[i] := by
    rw [← wData_get hi]
    rfl
  rw [e]
  exact pinMapR_get pin_ann (by omega) (by omega) hl

theorem annArr_eq {i : Nat} (hi : i < 1395) : annArr[i]! = anm.getD i 0 := by
  rw [annArr_get hi, annK_eq hi]

theorem wtd_length : wtd.length = 1395 := by decide +kernel

theorem rwt_eq {i : Nat} (hi : i < 1395) : rev20 (wtd.getD i 0) = rwt.getD i 0 := by
  have hl : i < wtd.length := by rw [wtd_length]; exact hi
  rw [getD_of_lt hl]
  exact pinMapR_get pin_rev (by omega) (by omega) hl

theorem tvApply_eq (k x : Nat) : tvApply k x = tvA (tvPair k) x := by
  unfold tvApply tvA
  obtain ⟨v, φ⟩ := tvPair k
  rfl

theorem tvCols_toList (k : Nat) : (tvCols k).toList = colsL (tvPair k) := by
  unfold tvCols colsL
  rw [Array.toList_ofFn]
  refine List.ext_getElem (by simp) fun t h1 h2 => ?_
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  rw [tvApply_eq, tvApply_eq, tvApply_eq]

theorem tvCols_eq {k : Nat} (hk : k < 1953) : (tvCols k).toList = tcl.getD k [] := by
  have hl : k < tvList.toList.length := by rw [Array.length_toList, tvList_size]; exact hk
  rw [tvCols_toList, tvPair_get hk]
  rcases Nat.lt_or_ge k 489 with h0 | h0
  · exact pinMapR_get pin_cols0 (by omega) (by omega) hl
  rcases Nat.lt_or_ge k 978 with h1 | h1
  · exact pinMapR_get pin_cols1 (by omega) (by omega) hl
  rcases Nat.lt_or_ge k 1467 with h2 | h2
  · exact pinMapR_get pin_cols2 (by omega) (by omega) hl
  · exact pinMapR_get pin_cols3 (by omega) (by omega) hl

end CertificateChecks.KernelSmithL6K
