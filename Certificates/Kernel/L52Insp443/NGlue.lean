module

public import Certificates.Kernel.L52Insp443.Checks
public import Certificates.Kernel.L52Insp443.TabChk
public import Certificates.Kernel.L52Insp443.Orb
public import Certificates.Kernel.L52Insp443.RChk
public import Certificates.Kernel.L52Insp443.ClChk
public import CFSG.Certificates.Kernel.L52Insp443.Norm

public section

set_option maxRecDepth 20000

namespace CertificateChecks.KernelL52I

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.GLM CFSG.KC.L52I CFSG.SectionRank.QTK.Insp443.L52
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Literature.GL52 CFSG.Quasithin.KGC31.Native
  CFSG.SectionRank.QTK.Insp443.PermKit.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier

theorem gsA : mcode ((glA : G) : Mat) = D.gs.getD 0 0 := by decide +kernel

theorem gsB : mcode ((glB : G) : Mat) = D.gs.getD 1 0 := by decide +kernel

theorem gis_code {i : ℕ} (hi : i < 2) {x : G} (hx : mcode (x : Mat) = D.gs.getD i 0) :
    mcode ((x⁻¹ : G) : Mat) = D.gis.getD i 0 := by
  obtain ⟨g1, g2⟩ := and2 ch725109g0
  obtain ⟨g2, g3⟩ := and2 g2
  obtain ⟨g3, g4⟩ := and2 g3
  have hl : D.gis.length = 2 := Nat.eq_of_beq_eq_true g2
  have hil : i < D.gis.length := by rw [hl]; exact hi
  have hu : unitK (D.gis.getD i 0) = true := by
    have := (allK_iff _ _).mp g4 (D.gis.getD i 0)
      (by rw [List.getD_eq_getElem _ _ hil]; exact List.getElem_mem hil)
    exact this
  have hx' := ch725109x0
  obtain ⟨-, r⟩ := and2 hx'
  obtain ⟨-, r⟩ := and2 r
  obtain ⟨-, r⟩ := and2 r
  obtain ⟨-, r⟩ := and2 r
  obtain ⟨-, r⟩ := and2 r
  obtain ⟨-, r⟩ := and2 r
  have hm := Nat.eq_of_beq_eq_true ((allK_iff _ _).mp r i (List.mem_range.mpr hi))
  have e : x * gD (D.gis.getD i 0) = 1 := by
    apply kG_inj
    change mcode (((x * gD (D.gis.getD i 0)) : G) : Mat) = mcode (((1 : G)) : Mat)
    rw [kG_mul, kG_one, mcode_gD hu, hx, hm]
  rw [← eq_inv_of_mul_eq_one_right e, mcode_gD hu]

theorem zS_eq {z : ℕ} (hz : ch725109z z = true) : D.zS.getD z [] = spanK (D.zB.getD z []) :=
  ((listBeq_iff _ _).mp (and2 hz).1).symm

theorem cl_facts {bs S : List ℕ} (h : clK bs S = true) :
    (∀ b ∈ bs, ∀ s ∈ S, mmulK b s ∈ S) ∧ ∀ b ∈ bs, mmulK b b = idK := by
  refine ⟨fun b hb s hs => ?_, fun b hb => ?_⟩
  · obtain ⟨-, h2⟩ := and2 ((allK_iff _ _).mp h b hb)
    exact (memK_iff _ _).mp ((allK_iff _ _).mp h2 s hs)
  · exact Nat.eq_of_beq_eq_true (and2 ((allK_iff _ _).mp h b hb)).1

theorem recU {L : List Rec} (h : recUnits L = true) :
    ∀ r ∈ L, unitK r.2.1 = true ∧ unitK r.2.2.1 = true := fun r hr =>
  and2 ((allK_iff _ _).mp h r hr)

theorem normZ_of {z : ℕ} (ho : ch725109o z = true)
    (he : ch725109e z = true) (hz : ch725109z z = true) (ht : ch725109t z = true)
    (hc : ch725109zc z = true) (hm : 0 < (D.oZ.getD z []).length) :
    Subgroup.normalizer (subK (D.zB.getD z []) : Set G) =
        stabK (fixK (D.zB.getD z [])) (fixK_lt _) ∧
      Nat.card G = (D.oZ.getD z []).length * Nat.card (stabK (fixK (D.zB.getD z [])) (fixK_lt _)) := by
  have hu := (forall₂_of_tabsK (ht : tabsK (D.zB.getD z []) (e16.getD z []) = true)).2
  have hS := zS_eq hz
  obtain ⟨hcl, hsq⟩ := cl_facts (hc : clK (D.zB.getD z []) (D.zS.getD z []) = true)
  rw [hS] at hcl
  have ho' : orbOK (D.zB.getD z []) (D.oZ.getD z []) (normP (spanK (D.zB.getD z [])) (D.zB.getD z []))
      (mcode ((glA : G) : Mat)) (mcode ((glA⁻¹ : G) : Mat)) (mcode ((glB : G) : Mat))
      (mcode ((glB⁻¹ : G) : Mat)) = true := by
    rw [gis_code (by norm_num) gsA, gis_code (by norm_num) gsB, gsA, gsB, ← hS]
    exact ho
  exact normalizer_eq_stabK hu hcl hsq closure_glAB hm ho' (recU he)

theorem normZ {z : ℕ} (hz : z < 7) :
    Subgroup.normalizer (subK (D.zB.getD z []) : Set G) =
        stabK (fixK (D.zB.getD z [])) (fixK_lt _) ∧
      Nat.card G = 31 * Nat.card (stabK (fixK (D.zB.getD z [])) (fixK_lt _)) := by
  have hl : (D.oZ.getD z []).length = 31 := by
    interval_cases z <;> decide +kernel
  rw [← hl]
  interval_cases z
  · exact normZ_of ch725109o0 ch725109e0 ch725109z0 ch725109t0 ch725109zc0 (by rw [hl]; norm_num)
  · exact normZ_of ch725109o1 ch725109e1 ch725109z1 ch725109t1 ch725109zc1 (by rw [hl]; norm_num)
  · exact normZ_of ch725109o2 ch725109e2 ch725109z2 ch725109t2 ch725109zc2 (by rw [hl]; norm_num)
  · exact normZ_of ch725109o3 ch725109e3 ch725109z3 ch725109t3 ch725109zc3 (by rw [hl]; norm_num)
  · exact normZ_of ch725109o4 ch725109e4 ch725109z4 ch725109t4 ch725109zc4 (by rw [hl]; norm_num)
  · exact normZ_of ch725109o5 ch725109e5 ch725109z5 ch725109t5 ch725109zc5 (by rw [hl]; norm_num)
  · exact normZ_of ch725109o6 ch725109e6 ch725109z6 ch725109t6 ch725109zc6 (by rw [hl]; norm_num)

theorem card_normZ {z : ℕ} (hz : z < 7) :
    Nat.card (Subgroup.normalizer (subK (D.zB.getD z []) : Set G)) = 322560 := by
  obtain ⟨h1, h2⟩ := normZ hz
  rw [h1]
  rw [card_GL52] at h2
  omega

theorem e16_count {z : ℕ} (hz : z < 7) (ht : ch725109t z = true)
    (hzz : ch725109z z = true) (hc : ch725109zc z = true) :
    countProducts 31 (conjIn 31 (e16.getD z []) (spanTabs 31 (e16.getD z [])))
      (levelTables glCert) (idT 31) = 322560 := by
  classical
  obtain ⟨hT, hu⟩ := forall₂_of_tabsK (ht : tabsK (D.zB.getD z []) (e16.getD z []) = true)
  obtain ⟨hcl, hsq⟩ := cl_facts (hc : clK (D.zB.getD z []) (D.zS.getD z []) = true)
  rw [zS_eq hzz] at hcl
  rw [← card_subtype_glPerm (fun π => ∀ u ∈ D.zB.getD z [], ∃ y : G,
      mcode (y : Mat) ∈ spanK (D.zB.getD z []) ∧ π * glPerm (gD u) = glPerm y * π) _
      (fun T π hR => conjIn_iff_codes hT hT hu hR)]
  rw [← card_normZ hz]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => conj_glPerm_iff hu hcl hsq g)

end CertificateChecks.KernelL52I

end
