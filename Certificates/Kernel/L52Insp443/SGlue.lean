module

public import Certificates.Kernel.L52Insp443.CentGlue
public import Certificates.Kernel.L52Insp443.UChk
public import CFSG.Sporadic.Recognition.LyonsAmalgamInv

public section

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I CFSG.SectionRank.QTK.Insp443.L52
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Literature.GL52 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native

@[expose] noncomputable def x7G : G := gD (D.x7p.getD 1 0)

theorem x7_unit : unitK (D.x7p.getD 1 0) = true := (and2 ch725109y0).1

theorem mcode_x7 : mcode ((x7G : G) : Mat) = D.x7p.getD 1 0 := mcode_gD x7_unit

theorem rep_x7 : Rep 31 x7T (glPerm x7G) := by
  have h := (and2 ch725109y0).2
  rw [← mcode_x7] at h
  exact rep_of_tabK h

theorem x7Pairs_rep {j : ℕ} (hj : j < 7) : ∃ ab ∈ x7Pairs (invT 31 x7T),
    Rep 31 ab.1 (glPerm (x7G ^ j)) ∧ Rep 31 ab.2 (glPerm (x7G⁻¹ ^ j)) := by
  refine ⟨(powT 31 j x7T, powT 31 j (invT 31 x7T)),
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, ?_, ?_⟩
  · rw [map_pow]
    exact Rep.powT hn31 rep_x7 j
  · rw [map_pow, map_inv]
    exact Rep.powT hn31 (rep_invT_of_rep hn31 rep_x7) j

theorem x7_codes {j : ℕ} (hj : j ≤ 6) : D.x7p.getD j 0 = mcode ((x7G ^ j : G) : Mat) ∧
    D.x7q.getD j 0 = mcode ((x7G⁻¹ ^ j : G) : Mat) := by
  obtain ⟨h1, h2⟩ := and2 ch725109x0
  obtain ⟨h2, h3⟩ := and2 h2
  obtain ⟨-, h4⟩ := and2 h3
  obtain ⟨hq7, h5⟩ := and2 h4
  obtain ⟨h5, -⟩ := and2 h5
  have hq7' : D.x7q.length = 7 := Nat.eq_of_beq_eq_true hq7
  refine pow_codes (m := 6) (Nat.eq_of_beq_eq_true h1) (fun j hj => Nat.eq_of_beq_eq_true
    ((allK_iff _ _).mp h2 j (List.mem_range.mpr hj))) mcode_x7
    (fun j hj => Nat.eq_of_beq_eq_true ((allK_iff _ _).mp h5 j (List.mem_range.mpr (by omega))))
    (fun j hj => ?_) j hj
  have hjl : j < D.x7q.length := by rw [hq7']; omega
  have hi := (allK_iff _ _).mp ch725109i0 (D.x7q.getD j 0)
    (by rw [List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl)
  exact hi

theorem sOf {k z w : ℕ} (hzw : D.k1zw.getD k (0, 0) = (z, w)) (hv : ch725109v k = true)
    (hk : ch725109k k = true) (hq : ch725109q k = true) (hz : ch725109z z = true)
    (ht : ch725109t z = true) (hw : ch725109w w = true) (hu : ch725109u w = true)
    (hl : D.x7p.length = 7 ∧ D.x7q.length = 7) (h : G) {T : Table}
    (hT : Rep 31 T (glPerm h)) :
    sTestS 31 (cands7.getD (k1idx k) []) (spanTabs 31 (e16.getD z [])) (spanTabs 31 (wB w))
      (x7Pairs (invT 31 x7T)) T = false := by
  unfold ch725109v at hv
  rw [hzw] at hv
  obtain ⟨v1, v2⟩ := and2 hv
  obtain ⟨v2, v3⟩ := and2 v2
  obtain ⟨-, k2⟩ := and2 hk
  obtain ⟨-, k3⟩ := and2 k2
  obtain ⟨k3, -⟩ := and2 k3
  obtain ⟨z1, -⟩ := and2 hz
  obtain ⟨w1, -⟩ := and2 hw
  rw [listBeq_iff] at z1 w1
  have ht' : tabsK (D.zB.getD z []) (e16.getD z []) = true := ht
  refine sTestS_false (zc := D.zB.getD z []) (wc := List.append (D.a0B.getD w []) (D.a1B.getD w []))
    (ps := D.x7p) (qs := D.x7q) hq ht' (tabs_wB hu) ((nodupK_iff _).mp v1)
    (by rw [Nat.eq_of_beq_eq_true k3, Nat.eq_of_beq_eq_true v2]) (fun c hc => ?_) x7G
    (by rw [hl.1, hl.2]) (fun j hj => ?_) h hT
  · have hc' := (allK_iff _ _).mp v3 c hc
    obtain ⟨c1, c2⟩ := and2 hc'
    obtain ⟨c2, c3⟩ := and2 c2
    refine ⟨c1, fun b hb => (commK_iff c b).mp ((allK_iff _ _).mp c2 b hb), ?_⟩
    rw [z1, w1]
    rcases orB_true.mp c3 with c3 | c3
    · exact Or.inl (notB_true.mp c3)
    · rcases orB_true.mp c3 with c3 | c3
      · exact Or.inr (Or.inl ((memK_iff _ _).mp c3))
      · exact Or.inr (Or.inr ((memK_iff _ _).mp c3))
  · rw [hl.1] at hj
    obtain ⟨hp, hq'⟩ := x7_codes (j := j) (by omega)
    exact ⟨hp, hq', x7Pairs_rep hj⟩

theorem x7_lengths : D.x7p.length = 7 ∧ D.x7q.length = 7 := by
  obtain ⟨-, h2⟩ := and2 ch725109x0
  obtain ⟨-, h3⟩ := and2 h2
  obtain ⟨hp, h4⟩ := and2 h3
  obtain ⟨hq, -⟩ := and2 h4
  exact ⟨Nat.eq_of_beq_eq_true hp, Nat.eq_of_beq_eq_true hq⟩

theorem k1_sTest (h : G) {T : Table} (hT : Rep 31 T (glPerm h)) :
    sTestS 31 (cands7.getD 1 []) (spanTabs 31 (e16.getD 2 [])) (spanTabs 31 (wB 0))
        (x7Pairs (invT 31 x7T)) T = false ∧
      sTestS 31 (cands7.getD 2 []) (spanTabs 31 (e16.getD 3 [])) (spanTabs 31 (wB 0))
        (x7Pairs (invT 31 x7T)) T = false ∧
      sTestS 31 (cands7.getD 3 []) (spanTabs 31 (e16.getD 4 [])) (spanTabs 31 (wB 0))
        (x7Pairs (invT 31 x7T)) T = false ∧
      sTestS 31 (cands7.getD 4 []) (spanTabs 31 (e16.getD 5 [])) (spanTabs 31 (wB 1))
        (x7Pairs (invT 31 x7T)) T = false ∧
      sTestS 31 (cands7.getD 7 []) (spanTabs 31 (e16.getD 6 [])) (spanTabs 31 (wB 1))
        (x7Pairs (invT 31 x7T)) T = false ∧
      sTestS 31 (cands7.getD 8 []) (spanTabs 31 (e16.getD 1 [])) (spanTabs 31 (wB 1))
        (x7Pairs (invT 31 x7T)) T = false :=
  ⟨sOf (k := 0) (by decide +kernel) ch725109v0 ch725109k0 ch725109q0 ch725109z2 ch725109t2
      ch725109w0 ch725109u0 x7_lengths h hT,
    sOf (k := 1) (by decide +kernel) ch725109v1 ch725109k1 ch725109q1 ch725109z3 ch725109t3
      ch725109w0 ch725109u0 x7_lengths h hT,
    sOf (k := 2) (by decide +kernel) ch725109v2 ch725109k2 ch725109q2 ch725109z4 ch725109t4
      ch725109w0 ch725109u0 x7_lengths h hT,
    sOf (k := 3) (by decide +kernel) ch725109v3 ch725109k3 ch725109q3 ch725109z5 ch725109t5
      ch725109w1 ch725109u1 x7_lengths h hT,
    sOf (k := 4) (by decide +kernel) ch725109v4 ch725109k4 ch725109q4 ch725109z6 ch725109t6
      ch725109w1 ch725109u1 x7_lengths h hT,
    sOf (k := 5) (by decide +kernel) ch725109v5 ch725109k5 ch725109q5 ch725109z1 ch725109t1
      ch725109w1 ch725109u1 x7_lengths h hT⟩

end CertificateChecks.KernelL52I

end
