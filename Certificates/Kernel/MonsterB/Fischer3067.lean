module

public import Certificates.Kernel.MonsterB.Fischer3067E0
public import Certificates.Kernel.MonsterB.Fischer3067E1
public import Certificates.Kernel.MonsterB.Fischer3067Orbit
public import Certificates.Kernel.MonsterB.FischerLabels
public import CFSG.Certificates.Kernel.MonsterB.FischerElimSound

public section

namespace CertificateChecks.KernelMonB.F3067

open CFSG.Monster.B.TwoA.Fischer CFSG.Monster.B.TwoA.Fischer.Cert CFSG.Monster.B.Fischer
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SmallF2.Native
  CFSG.Monster.B.Binary.Native CFSG.KC.FischerK CFSG.KC.FischerE CFSG.KLie.CT
  CertificateChecks.KernelMonB.IndCand CertificateChecks.KernelMonB.FischerTabs

theorem tableCol_toList {c : Nat} (hc : c < 78) :
    (tableCol c).toList = FD.ROWS.map fun r => fget r c 78 := by
  have h := kRows
  unfold rowsChk at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨hlen, hrows⟩ := h
  apply List.ext_getElem
  · simp [tableCol, hlen]
  · intro i h1 h2
    have hi : i < 78 := by simpa [tableCol] using h1
    obtain ⟨hs, hp⟩ := hrows i hi
    rw [List.getElem_map, ← getElem!_pos FD.ROWS i (by rw [hlen]; exact hi)]
    have := packW_get hp (k := c) (by rw [Array.length_toList, hs]; exact hc)
    rw [Array.toArray_toList] at this
    rw [← this, Array.getElem_toList]
    simp only [tableCol, Array.getElem_ofFn]
    rfl

theorem adCols_eq (m : Nat) : (adCols m).toList = adL m := by
  apply List.ext_getElem
  · simp [adCols, adL]
  · intro c h1 h2
    have hc : c < 78 := by simpa [adCols] using h1
    simp only [adCols, adL, Array.getElem_toList, Array.getElem_ofFn, List.getElem_map,
      List.getElem_range]
    rw [vecMulN_eq (by simp [tableCol]) m, fget_vecMulL, tableCol_toList hc]

theorem spanRankIs_78 (L : List Nat) (r : Nat) : spanRankIs 78 L r = spanT L r :=
  spanRankIs_eq 78 L r

theorem orbitEntryOK_eq (m : Nat) : orbitEntryOK m = orbitEntryT m := by
  unfold orbitEntryOK orbitEntryT
  simp only [orbIdx_eq, orbDist_eq, orbPar_eq, orbGen_eq, vecMulN_fCol, adCols_eq, spanRankIs_78]

theorem entryT_all : ∀ m < 2048, orbitEntryT m = true := by
  intro m hm
  have key : ∀ s < 8, 256 * s ≤ m → m < 256 * s + 256 → orbitEntryT m = true := by
    intro s hs h1 h2
    have hmem : m ∈ List.range' (256 * s) 256 := List.mem_range'_1.2 ⟨h1, h2⟩
    interval_cases s
    · exact List.all_eq_true.1 kE0 m hmem
    · exact List.all_eq_true.1 kE1 m hmem
    · exact List.all_eq_true.1 kE2 m hmem
    · exact List.all_eq_true.1 kE3 m hmem
    · exact List.all_eq_true.1 kE4 m hmem
    · exact List.all_eq_true.1 kE5 m hmem
    · exact List.all_eq_true.1 kE6 m hmem
    · exact List.all_eq_true.1 kE7 m hmem
  exact key (m / 256) (by omega) (by omega) (by omega)

theorem orbitCheck_true : orbitCheck = true := by
  have hE : (List.range 2048).all orbitEntryOK = true := by
    rw [List.all_eq_true]
    intro m hm
    rw [orbitEntryOK_eq]
    exact entryT_all m (List.mem_range.1 hm)
  unfold orbitCheck
  rw [hE, Bool.true_and]
  simp only [orbIdx_eq]
  exact kRest

theorem orbit_card_true : ∀ t < 8,
    ((Finset.range 2048).filter fun m => orbIdx m = t).card = orbLen t := by
  intro t ht
  rw [Finset.card_filter, ← sum_map_range]
  simp only [orbIdx_eq]
  exact kCard t ht

theorem tableRowOK_true {i : Nat} (hi : i < 78) : tableRowOK i = true := by
  have h := List.all_eq_true.1 kTable i (List.mem_range.2 hi)
  unfold tableRowT at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hw, hrow⟩ := h
  have hw' : ∀ j ∈ labelWord i, j < 13 := by
    intro j hj
    have := List.all_eq_true.1 hw j hj
    simpa using this
  unfold tableRowOK
  simp only
  rw [← hrow]
  apply CFSG.KC.FischerK.all_range_congr
  intro j hj
  unfold tableEntryOK tableEntryT
  rw [jLabelArr_get hw' (CertificateChecks.KernelMonB.Fischer3066.basisPt_lt j hj)]
  simp only [labelCoord_eq]

theorem tableCheck_true : tableCheck = true := by
  unfold tableCheck
  rw [kTShape, Bool.true_and, List.all_eq_true]
  intro i hi
  exact tableRowOK_true (List.mem_range.1 hi)

theorem radicalCheck_true : radicalCheck = true := by
  unfold radicalCheck
  simp only [vecMulN_fCol]
  exact kRad

theorem subOneRows_tr : subOneRows transIdx = subOneTr := by
  rw [subOneRows, subOneTr, List.flatMap_def, List.flatMap_def]
  refine congrArg List.flatten (List.map_congr_left fun k hk => ?_)
  have hk12 : k < 12 := by
    simp only [transIdx, List.mem_map, List.mem_range] at hk
    omega
  have h := CertificateChecks.KernelMonB.Fischer3066.kTr k hk12
  have h' : transposeRows 78 (fColArr[k]!) = (fTrsL[k]!).toArray := by
    rw [← Array.toArray_toList (xs := transposeRows 78 (fColArr[k]!)), h]
    rfl
  rw [h']

theorem rRank_true : spanRankIs 78 (subOneRows transIdx) 67 = true := by
  rw [subOneRows_tr, spanRankIs_78]
  exact kRank

theorem rFree_true : freeIs 78 (subOneRows transIdx) (List.range 11) = true := by
  rw [subOneRows_tr, freeIs_eq]
  exact kFree

theorem zeroSetOK_eq {u : Nat} {A : List Nat} (hA : adL u = A) : zeroSetOK u = zeroT A := by
  have hl : A.length = 78 := by rw [← hA]; simp [adL]
  have hC : adCols u = A.toArray := by
    rw [← Array.toArray_toList (xs := adCols u), adCols_eq, hA]
  have hs : A.toArray.size = 78 := by rw [List.size_toArray, hl]
  unfold zeroSetOK zeroT
  rw [hC, ← CertificateChecks.KernelMonB.Fischer3066.kLen]
  simp only [vecMulN_eq hs, List.toList_toArray]
  exact range_all_eq_allIdx (fun q c => decide (vecMulL A c < 2 ^ 78) &&
    (vecMulL A c == 0) == decide (q < 22)) GramLit.rowCoords

theorem zeroSetCheck_true : zeroSetCheck = true := by
  unfold zeroSetCheck
  rw [zeroSetOK_eq kAd, kZ, Bool.true_and, List.all_eq_true]
  intro c hc
  have hc' := List.mem_range.1 hc
  rw [zeroSetOK_eq (kAdc c hc')]
  exact kZc c hc'

theorem facts : (tableCheck = true)
    ∧ (radicalCheck = true)
    ∧ (spanRankIs 78 (subOneRows transIdx) 67 = true)
    ∧ (freeIs 78 (subOneRows transIdx) (List.range 11) = true)
    ∧ (orbitCheck = true)
    ∧ (∀ t < 8,
       ((Finset.range 2048).filter fun m => orbIdx m = t).card = orbLen t)
    ∧ (zeroSetCheck = true) :=
  ⟨tableCheck_true, radicalCheck_true, rRank_true, rFree_true, orbitCheck_true, orbit_card_true,
    zeroSetCheck_true⟩

end CertificateChecks.KernelMonB.F3067

end
