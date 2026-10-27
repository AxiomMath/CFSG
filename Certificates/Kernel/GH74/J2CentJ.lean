module

public import Certificates.Kernel.GH74.J2CentI

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.J2CentE

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH CFSG.KS.GH74
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore.Native
open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native
open CFSG.GH74.Generic.S45.EvSpor CertificateChecks.KernelGH74
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.J2Cn

theorem orb_list {r : List Nat} {L : List (List Nat)} {m : Nat} {GI : Nat → Nat}
    (hm : L.length = m) (h : TabsOK 315 9 (m + 1) GI (j2TA :: conjOrbit r L).toArray) :
    conjOrbit r L = ((List.range m).map fun k => GI (k + 1)).map fun y => tabT (unpack 315 9 y) := by
  apply List.ext_getElem (by simp [conjOrbit, hm])
  intro k h1 h2
  have hk : k < m := by simpa [conjOrbit, hm] using h1
  have e := (h.2 (k + 1) (by omega)).1
  rw [getElem!_pos _ (k + 1) (by simp [conjOrbit, hm]; omega)] at e
  simp only [List.getElem_toArray, List.getElem_cons_succ] at e
  rw [e]
  simp

theorem orbit_ok : j2OrbitOK = true := by
  have l1 := orb_list (m := 10) rfl o1_tabs
  have l2 := orb_list (m := 20) rfl o2_tabs
  have c1 : ∀ y ∈ (List.range 10).map (fun k => J2O1.GI (k + 1)),
      canonK 315 9 (mask 9) (315 * 9) y = true := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
    exact (o1_tabs.2 (k + 1) (by simp at hk; omega)).2
  have c2 : ∀ y ∈ (List.range 20).map (fun k => J2O2.GI (k + 1)),
      canonK 315 9 (mask 9) (315 * 9) y = true := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
    exact (o2_tabs.2 (k + 1) (by simp at hk; omega)).2
  unfold j2OrbitOK
  rw [o1_enum, o2_enum, l1, l2, e_arr]
  simp only [Bool.true_and]
  rw [all_hRec_iff]
  intro i hi
  have h := allN_spec cover_ok i (by rw [e_cnt] at hi; exact hi)
  rw [hid, tA_tab, tblEq_unpack (eT hi) hidc, tblEq_unpack (eT hi) tK_canon,
    memT_list c1 (eT hi), memT_list c2 (eT hi)]
  simp only [bOr_eq] at h
  simp only [Bool.or_assoc]
  exact h

theorem perfect_ok : j2PerfectOK = true := pf_enum

theorem sylow_ok : j2SylowOK = true := by
  unfold j2SylowOK
  rw [s1_enum, s2_enum, s1_arr, s2_arr, e_arr]
  simp only [Bool.true_and]
  rw [all_hRec_iff]
  intro i hi
  have h := allN_spec syl_ok i hi
  rw [memT_hRec (fun j hj => s2T hj) (s1T hi), memT_hRec (fun j hj => eT hj) (s1T hi)]
  rw [bIf_true_right'] at h
  exact h

theorem band_eq' (a b : Bool) : (a && b) = bAnd(a, b) := by cases a <;> rfl

theorem bAnd_eq_and (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem nc_list : j2NCInvs.toList = J2NCI.map fun i => tabT (unpack 315 9 (J2E.T i)) := by
  unfold j2NCInvs
  rw [e_arr, Array.toList_filter]
  simp only [hRec, Array.toList_ofFn]
  rw [CFSG.KS.PEnum.ofFn_range J2E.cnt (fun i => tabT (unpack 315 9 (J2E.T i))), List.filter_map,
    e_cnt, ← nc_ok.1]
  congr 1
  apply List.filter_congr
  intro i hi
  have hi' : i < 32 := List.mem_range.1 hi
  simp only [Function.comp]
  rw [involF (eT32 hi'), tA_tab, tblEq_unpack (eT32 hi') tK_canon, bIf_not', band_eq']

theorem nci_len : J2NCI.length = 10 := rfl

theorem nc_size : j2NCInvs.size = 10 := by
  rw [Array.size_eq_length_toList, nc_list, List.length_map, nci_len]

theorem nc_get {k : Nat} (hk : k < 10) :
    j2NCInvs[k]! = tabT (unpack 315 9 (J2E.T (getL J2NCI k))) := by
  have hs : k < j2NCInvs.size := by rw [nc_size]; exact hk
  rw [getElem!_pos _ k hs, ← Array.getElem_toList]
  have e : j2NCInvs.toList[k]? = (J2NCI.map fun i => tabT (unpack 315 9 (J2E.T i)))[k]? := by
    rw [nc_list]
  rw [List.getElem?_eq_getElem (by rw [Array.length_toList]; exact hs), List.getElem?_map,
    List.getElem?_eq_getElem (by rw [nci_len]; exact hk)] at e
  have e' := Option.some.inj e
  rw [e']
  unfold getL
  rw [List.getD_eq_getElem _ _ (by rw [nci_len]; exact hk)]

theorem nci_lt {k : Nat} (hk : k < 10) : getL J2NCI k < 32 := by
  interval_cases k <;> decide

theorem beq_bool (a b : Bool) : (a == b) = Nat.beq (bN a) (bN b) := by cases a <;> cases b <;> rfl

theorem commTT_bN {a b : Nat} (ha : a < 10) (hb : b < 10) :
    bN (commTT 315 j2NCInvs[a]! j2NCInvs[b]!) = getL J2CM (Nat.add (Nat.mul 10 a) b) := by
  have h := allN_spec (allN_spec nc_ok.2.1 a ha) b hb
  rw [Nat.eq_of_beq_eq_true h, nc_get ha, nc_get hb, commF (eT32 (nci_lt ha)) (eT32 (nci_lt hb))]

theorem gp_bN {a b : Nat} (ha : a < 4) (hb : b < 4) :
    bN (commTT 315 j2EGens.toArray[a]! j2EGens.toArray[b]!) = getL J2GP (Nat.add (Nat.mul 4 a) b) := by
  have h := allN_spec (allN_spec nc_ok.2.2.1 a ha) b hb
  rw [Nat.eq_of_beq_eq_true h, (e_tabs.2 a ha).1, (e_tabs.2 b hb).1, commF (eg_canon ha) (eg_canon hb)]

theorem mem_quadIdx {k : Nat} {t : Nat × Nat × Nat × Nat} (ht : t ∈ quadIdx k) :
    t.1 < k ∧ t.2.1 < k ∧ t.2.2.1 < k ∧ t.2.2.2 < k := by
  unfold quadIdx at ht
  simp only [List.mem_flatMap, List.mem_map, List.mem_range] at ht
  obtain ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩ := ht
  exact ⟨ha, hb, hc, hd⟩

theorem autPat_eq {t : Nat × Nat × Nat × Nat} (ht : t ∈ quadIdx 10) :
    autPatOK t = patK t.1 t.2.1 t.2.2.1 t.2.2.2 := by
  obtain ⟨h1, h2, h3, h4⟩ := mem_quadIdx ht
  unfold autPatOK patK
  simp only [beq_bool]
  rw [commTT_bN h1 h2, commTT_bN h1 h3, commTT_bN h1 h4, commTT_bN h2 h3, commTT_bN h2 h4,
    commTT_bN h3 h4, gp_bN (a := 0) (b := 1) (by norm_num) (by norm_num),
    gp_bN (a := 0) (b := 2) (by norm_num) (by norm_num), gp_bN (a := 0) (b := 3) (by norm_num) (by norm_num),
    gp_bN (a := 1) (b := 2) (by norm_num) (by norm_num), gp_bN (a := 1) (b := 3) (by norm_num) (by norm_num),
    gp_bN (a := 2) (b := 3) (by norm_num) (by norm_num)]
  simp only [bAnd_eq_and, Bool.and_assoc]

theorem autCount_le : j2AutCount ≤ 1920 := by
  unfold j2AutCount
  rw [nc_size, List.filter_congr (fun t ht => autPat_eq ht)]
  exact Nat.le_of_ble_eq_true nc_ok.2.2.2

end CertificateChecks.KernelGH74.J2CentE

end
