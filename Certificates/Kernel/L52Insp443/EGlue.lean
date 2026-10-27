module

public import Certificates.Kernel.L52Insp443.SubChk
public import Certificates.Kernel.L52Insp443.SGlue
public import CFSG.Certificates.Kernel.L52Insp443.SubSound
public import CFSG.Certificates.Kernel.L52Insp443.Norm

public section

set_option maxRecDepth 20000

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I CFSG.SectionRank.QTK.Insp443.L52
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Literature.GL52 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

theorem f2_wB {w : ℕ} (hu : ch725109u w = true) :
    List.Forall₂ (Rep 31) (wB w) ((wC w).map fun c => glPerm (gD c)) ∧ ∀ c ∈ wC w, unitK c = true :=
  forall₂_of_tabsK (tabs_wB hu)

theorem e16_ok_of {z : ℕ} (ht : ch725109t z = true) (hs : ch725109sz z = true)
    (hl : (e16.getD z []).length = 4) : e16OK z = true := by
  obtain ⟨hT, hu⟩ := forall₂_of_tabsK (ht : tabsK (D.zB.getD z []) (e16.getD z []) = true)
  unfold e16OK
  rw [Bool.and_eq_true, beq_iff_eq]
  exact ⟨hl, subOK_of hT hu hT hu hs⟩

theorem e16_ok : (List.range 7).all e16OK = true := by
  rw [List.all_eq_true]
  intro z hz
  rw [List.mem_range] at hz
  interval_cases z
  · exact e16_ok_of ch725109t0 ch725109sz0 rfl
  · exact e16_ok_of ch725109t1 ch725109sz1 rfl
  · exact e16_ok_of ch725109t2 ch725109sz2 rfl
  · exact e16_ok_of ch725109t3 ch725109sz3 rfl
  · exact e16_ok_of ch725109t4 ch725109sz4 rfl
  · exact e16_ok_of ch725109t5 ch725109sz5 rfl
  · exact e16_ok_of ch725109t6 ch725109sz6 rfl

theorem e64_ok_of {w : ℕ} (hu : ch725109u w = true) (hs : ch725109sw w = true)
    (hl0 : (e64a0.getD w []).length = 3) (hl1 : (e64a1.getD w []).length = 3) :
    e64OK w = true := by
  obtain ⟨hW, hWu⟩ := f2_wB hu
  obtain ⟨u0, u1⟩ := and2 hu
  obtain ⟨h0, h0u⟩ := forall₂_of_tabsK u0
  obtain ⟨h1, h1u⟩ := forall₂_of_tabsK u1
  obtain ⟨hd, hdu⟩ := forall₂_zip h0 h0u h1 h1u
  obtain ⟨s1, s2⟩ := and2 hs
  obtain ⟨s2, s3⟩ := and2 s2
  obtain ⟨s3, s4⟩ := and2 s3
  unfold e64OK
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨hl0, hl1⟩, subOK_of hW hWu hW hWu s1⟩, ?_⟩
  rw [aB.eq_1, List.all_cons, List.all_cons, List.all_cons, List.all_nil]
  simp only [Bool.and_eq_true, and_true]
  exact ⟨subOK_of h0 h0u hW hWu s2, subOK_of h1 h1u hW hWu s3, subOK_of hd hdu hW hWu s4⟩

theorem e64_ok : (List.range 2).all e64OK = true := by
  rw [List.all_eq_true]
  intro w hw
  rw [List.mem_range] at hw
  interval_cases w
  · exact e64_ok_of ch725109u0 ch725109sw0 rfl rfl
  · exact e64_ok_of ch725109u1 ch725109sw1 rfl rfl

theorem rep_x7i : Rep 31 (invT 31 x7T) (glPerm x7G⁻¹) := by
  rw [map_inv]
  exact rep_invT_of_rep hn31 rep_x7

theorem irr_of {us ws : List ℕ} {R : List (List ℕ)} {Us Ws : List Table}
    (hU : List.Forall₂ (Rep 31) Us (us.map fun c => glPerm (gD c))) (huu : ∀ c ∈ us, unitK c = true)
    (hW : List.Forall₂ (Rep 31) Ws (ws.map fun c => glPerm (gD c))) (hwu : ∀ c ∈ ws, unitK c = true)
    (h : irrK D.x7p D.x7q us ws R = true) : irrOK 31 7 x7T (invT 31 x7T) Us Ws = true :=
  irrOK_of hU huu hW hwu rep_x7 rep_x7i x7_lengths.1 x7_lengths.2
    (fun j hj => (x7_codes (by omega)).1) (fun j hj => (x7_codes (by omega)).2) h

theorem cand0 {us : List Table} {v w : ℕ} (hv : v < 7) (hw : w < 2) (h : us = e16.getD v []) :
    candOK (invT 31 x7T) us (0, v, w) = true := by
  subst h
  simp [candOK, hv, hw]

theorem cand1 {us : List Table} {z w : ℕ} (hz : z < 7) (hw : w < 2) (hl : us.length = 3)
    (h1 : subOK 31 us (e16.getD z []) = true) (h2 : subOK 31 us (wB w) = true)
    (h3 : irrOK 31 7 x7T (invT 31 x7T) us (wB w) = true) :
    candOK (invT 31 x7T) us (1, z, w) = true := by
  rw [candOK.eq_1]
  simp only [hz, hw, hl, h1, h2, h3, decide_true, Bool.true_and, Bool.and_true, beq_self_eq_true,
    Bool.or_true, Bool.true_or]

theorem cand2 {us : List Table} {w : ℕ} (hw : w < 2) (hl : us.length = 3)
    (h2 : subOK 31 us (wB w) = true) (h3 : irrOK 31 7 x7T (invT 31 x7T) us (wB w) = true) :
    candOK (invT 31 x7T) us (2, 0, w) = true := by
  simp [candOK, hw, hl, h2, h3]

theorem k1_ok {k z w : ℕ} (hzw : D.k1zw.getD k (0, 0) = (z, w)) (hs : ch725109sk k = true)
    (hq : ch725109q k = true) (ht : ch725109t z = true) (hu : ch725109u w = true) (hz : z < 7)
    (hw : w < 2) (hl : (cands7.getD (k1idx k) []).length = 3) :
    candOK (invT 31 x7T) (cands7.getD (k1idx k) []) (1, z, w) = true := by
  unfold ch725109sk at hs
  rw [hzw] at hs
  obtain ⟨s1, s2⟩ := and2 hs
  obtain ⟨s2, s3⟩ := and2 s2
  obtain ⟨hQ, hQu⟩ := forall₂_of_tabsK (hq : tabsK (D.k1B.getD k []) (cands7.getD (k1idx k) []) = true)
  obtain ⟨hZ, hZu⟩ := forall₂_of_tabsK (ht : tabsK (D.zB.getD z []) (e16.getD z []) = true)
  obtain ⟨hW, hWu⟩ := f2_wB hu
  exact cand1 hz hw hl (subOK_of hQ hQu hZ hZu s1) (subOK_of hQ hQu hW hWu s2)
    (irr_of hQ hQu hW hWu s3)

theorem k2_ok {k w : ℕ} (hkw : D.k2w.getD k 0 = w) (hs : ch725109sc k = true)
    (hr : ch725109r k = true) (hu : ch725109u w = true) (hw : w < 2)
    (hl : (cands7.getD (k + 12) []).length = 3) :
    candOK (invT 31 x7T) (cands7.getD (k + 12) []) (2, 0, w) = true := by
  unfold ch725109sc at hs
  rw [hkw] at hs
  obtain ⟨s1, s2⟩ := and2 hs
  obtain ⟨hQ, hQu⟩ := forall₂_of_tabsK (hr : tabsK (D.k2B.getD k []) (cands7.getD (k + 12) []) = true)
  obtain ⟨hW, hWu⟩ := f2_wB hu
  exact cand2 hw hl (subOK_of hQ hQu hW hWu s1) (irr_of hQ hQu hW hWu s2)

theorem cand_ok : (List.range 24).all (fun k =>
    candOK (invT 31 x7T) (cands7.getD k []) (kind7.getD k (3, 0, 0))) = true := by
  rw [List.all_eq_true]
  intro k hk
  rw [List.mem_range] at hk
  interval_cases k <;> simp only [kind7, List.getD_cons_zero, List.getD_cons_succ]
  · exact cand0 (by norm_num) (by norm_num) rfl
  · exact k1_ok (k := 0) (by decide +kernel) ch725109sk0 ch725109q0 ch725109t2 ch725109u0
      (by norm_num) (by norm_num) (by decide +kernel)
  · exact k1_ok (k := 1) (by decide +kernel) ch725109sk1 ch725109q1 ch725109t3 ch725109u0
      (by norm_num) (by norm_num) (by decide +kernel)
  · exact k1_ok (k := 2) (by decide +kernel) ch725109sk2 ch725109q2 ch725109t4 ch725109u0
      (by norm_num) (by norm_num) (by decide +kernel)
  · exact k1_ok (k := 3) (by decide +kernel) ch725109sk3 ch725109q3 ch725109t5 ch725109u1
      (by norm_num) (by norm_num) (by decide +kernel)
  · exact cand0 (by norm_num) (by norm_num) rfl
  · exact cand0 (by norm_num) (by norm_num) rfl
  · exact k1_ok (k := 4) (by decide +kernel) ch725109sk4 ch725109q4 ch725109t6 ch725109u1
      (by norm_num) (by norm_num) (by decide +kernel)
  · exact k1_ok (k := 5) (by decide +kernel) ch725109sk5 ch725109q5 ch725109t1 ch725109u1
      (by norm_num) (by norm_num) (by decide +kernel)
  · exact cand0 (by norm_num) (by norm_num) rfl
  · exact cand0 (by norm_num) (by norm_num) rfl
  · exact cand0 (by norm_num) (by norm_num) rfl
  · exact k2_ok (k := 0) (by decide +kernel) ch725109sc0 ch725109r0 ch725109u0 (by norm_num)
      (by decide +kernel)
  · exact k2_ok (k := 1) (by decide +kernel) ch725109sc1 ch725109r1 ch725109u0 (by norm_num)
      (by decide +kernel)
  · exact k2_ok (k := 2) (by decide +kernel) ch725109sc2 ch725109r2 ch725109u0 (by norm_num)
      (by decide +kernel)
  · exact k2_ok (k := 3) (by decide +kernel) ch725109sc3 ch725109r3 ch725109u0 (by norm_num)
      (by decide +kernel)
  · exact k2_ok (k := 4) (by decide +kernel) ch725109sc4 ch725109r4 ch725109u0 (by norm_num)
      (by decide +kernel)
  · exact k2_ok (k := 5) (by decide +kernel) ch725109sc5 ch725109r5 ch725109u0 (by norm_num)
      (by decide +kernel)
  · exact k2_ok (k := 6) (by decide +kernel) ch725109sc6 ch725109r6 ch725109u1 (by norm_num)
      (by decide +kernel)
  · exact k2_ok (k := 7) (by decide +kernel) ch725109sc7 ch725109r7 ch725109u1 (by norm_num)
      (by decide +kernel)
  · exact k2_ok (k := 8) (by decide +kernel) ch725109sc8 ch725109r8 ch725109u1 (by norm_num)
      (by decide +kernel)
  · exact k2_ok (k := 9) (by decide +kernel) ch725109sc9 ch725109r9 ch725109u1 (by norm_num)
      (by decide +kernel)
  · exact k2_ok (k := 10) (by decide +kernel) ch725109sc10 ch725109r10 ch725109u1 (by norm_num)
      (by decide +kernel)
  · exact k2_ok (k := 11) (by decide +kernel) ch725109sc11 ch725109r11 ch725109u1 (by norm_num)
      (by decide +kernel)

end CertificateChecks.KernelL52I

end
