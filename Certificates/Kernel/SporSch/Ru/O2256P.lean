
module

public import Certificates.Kernel.SporSch.Ru.O2256
public import Certificates.Kernel.SporSch.Ru.C2253P
public import CFSG.Certificates.Kernel.SporSch.RuOrbSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuOr

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG

theorem ptlist_eq {f s l P : Nat} (hs : ruPtsOffsets.getD f (0, 0) = (s, l)) (hr : s + l ≤ 10120)
    (h : hexPackK 3 4060 10120 s l 12 P RuPts.chars = true) : ruPtList f = unpack l 12 P := by
  have h := hexPackK_sound (by norm_num) hr h
  rw [← RuPts.eq] at h
  have h1 : (ruPtsOffsets.getD f (0, 0)).1 = s := by rw [hs]
  have h2 : (ruPtsOffsets.getD f (0, 0)).2 = l := by rw [hs]
  apply Array.ext
  · rw [ruPtList, unpack, Array.size_ofFn, Array.size_ofFn, h2]
  · intro i _ hi2
    have hi : i < l := by simpa [unpack] using hi2
    simp only [ruPtList, unpack, Array.getElem_ofFn]
    have e := h i hi
    rw [← h1] at e
    exact e

theorem oc_eq {k : Nat} (hk : k < 4) : ruCOrbit k = unpack (szC k) 12 (OC k) := by
  have hs : ruPtsOffsets.getD k (0, 0) = (stC k, szC k) := by
    interval_cases k <;> rfl
  have hr : stC k + szC k ≤ 10120 := by
    interval_cases k <;> decide
  exact ptlist_eq hs hr (allN_spec ocK k hk)

theorem on_eq {k : Nat} (hk : k < 3) : ruNOrbit k = unpack (szN k) 12 (ON k) := by
  have hs : ruPtsOffsets.getD (4 + k) (0, 0) = (stN k, szN k) := by
    interval_cases k <;> rfl
  have hr : stN k + szN k ≤ 10120 := by
    interval_cases k <;> decide
  exact ptlist_eq hs hr (allN_spec onK k hk)

theorem ocs_eq : ruCOrbits = (List.range 4).map fun k => unpack (szC k) 12 (OC k) := by
  rw [ruCOrbits]
  exact List.map_congr_left fun k hk => oc_eq (List.mem_range.1 hk)

theorem ons_eq : ruNOrbits = (List.range 3).map fun k => unpack (szN k) 12 (ON k) := by
  rw [ruNOrbits]
  exact List.map_congr_left fun k hk => on_eq (List.mem_range.1 hk)

theorem ocps_eq : ruCOrbitPos = (List.range 4).map fun k => unpack 4060 12 (OCP k) := by
  rw [ruCOrbitPos, ocs_eq, List.map_map]
  exact List.map_congr_left fun k hk => posK_sound (allN_spec ocpK k (List.mem_range.1 hk))

theorem onps_eq : ruNOrbitPos = (List.range 3).map fun k => unpack 4060 12 (ONP k) := by
  rw [ruNOrbitPos, ons_eq, List.map_map]
  exact List.map_congr_left fun k hk => posK_sound (allN_spec onpK k (List.mem_range.1 hk))

theorem labC : ruLabTab 4060 ruCOrbits = unpack 4060 12 LABC ∧
    labListsOK 4060 ruCOrbits (unpack 4060 12 LABC) ruCOrbitPos = true :=
  labK_sound ocs_eq ocps_eq labCK

theorem labN : ruLabTab 4060 ruNOrbits = unpack 4060 12 LABN ∧
    labListsOK 4060 ruNOrbits (unpack 4060 12 LABN) ruNOrbitPos = true :=
  labK_sound ons_eq onps_eq labNK

theorem getD_range {α : Type} {m k : Nat} (hk : k < m) (g : Nat → α) (d : α) :
    ((List.range m).map g).getD k d = g k := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

theorem rootsC_bind : ruCRoots.size = 4 ∧ ∀ t < 4, ruCRoots[t]! = pg 12 (mask 12) QC t := by
  refine ⟨by simp [ruCRoots, ruCOrbits], fun t ht => ?_⟩
  have e : ruCRoots[t]! = (ruCOrbit t)[0]! := by
    rw [ruCRoots, getElem!_pos _ t (by simp [ruCOrbits]; omega)]
    simp [ruCOrbits]
  have hp : 0 < szC t := by
    interval_cases t <;> decide
  rw [e, oc_eq ht, unpack_getPg hp]
  exact (Nat.eq_of_beq_eq_true (allN_spec rootsC t ht)).symm

theorem rootsN_bind : ruNRoots.size = 3 ∧ ∀ t < 3, ruNRoots[t]! = pg 12 (mask 12) QN t := by
  refine ⟨by simp [ruNRoots, ruNOrbits], fun t ht => ?_⟩
  have e : ruNRoots[t]! = (ruNOrbit t)[0]! := by
    rw [ruNRoots, getElem!_pos _ t (by simp [ruNOrbits]; omega)]
    simp [ruNOrbits]
  have hp : 0 < szN t := by
    interval_cases t <;> decide
  rw [e, on_eq ht, unpack_getPg hp]
  exact (Nat.eq_of_beq_eq_true (allN_spec rootsN t ht)).symm

theorem forest_eqC : ruCForest = (unpack 4060 12 DEPC, unpack 4060 12 PARC, unpack 4060 12 GLC) :=
  forestK_sound c0_eq c1_eq rootsC_bind (by norm_num) (allN_spec fC) (allN_spec eC)

theorem forest_eqN : ruNForest = (unpack 4060 12 DEPN, unpack 4060 12 PARN, unpack 4060 12 GLN) :=
  forestK_sound ns0_eq ns1_eq rootsN_bind (by norm_num) (allN_spec fN) (allN_spec eN)

theorem facts : ptPosOK 4060 ruF ruFPos = true ∧ ptPosOK 4060 ruY ruYPos = true ∧
    ruF = ruCOrbit 0 ∧ ruY = ruCOrbit 2 ∧
    (∀ k < 4, ptPosOK 4060 (ruCOrbit k) (ruCOrbitPos.getD k #[]) = true) ∧
    (∀ k < 3, ptPosOK 4060 (ruNOrbit k) (ruNOrbitPos.getD k #[]) = true) ∧
    labListsOK 4060 ruCOrbits ruCLab ruCOrbitPos = true ∧
    labListsOK 4060 ruNOrbits ruNLab ruNOrbitPos = true ∧
    orbitPartOK 4060 #[ruC0A, ruC1A] ruCLab ruCRoots ruCForest.1 ruCForest.2.1
      ruCForest.2.2 = true ∧
    orbitPartOK 4060 #[ruNs0A, ruNs1A] ruNLab ruNRoots ruNForest.1 ruNForest.2.1
      ruNForest.2.2 = true := by
  have hlC : ruCLab = unpack 4060 12 LABC := labC.1
  have hlN : ruNLab = unpack 4060 12 LABN := labN.1
  refine ⟨?_, ?_, ?_, ?_, fun k hk => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_⟩
  · rw [RuF.f_eq, RuF.fpos_eq]
    exact posK_ptPos RuF.posF
  · rw [RuCe.y_eq, RuCe.ypos_eq]
    exact posK_ptPos RuCe.posY
  · have e : szC 0 = 1920 := rfl
    rw [RuF.f_eq, oc_eq (by omega), Nat.eq_of_beq_eq_true fOC, e]
  · have e : szC 2 = 80 := rfl
    rw [RuCe.y_eq, oc_eq (by omega), Nat.eq_of_beq_eq_true yOC, e]
  · rw [ocps_eq, getD_range hk, oc_eq hk]
    exact posK_ptPos (allN_spec ocpK k hk)
  · rw [onps_eq, getD_range hk, on_eq hk]
    exact posK_ptPos (allN_spec onpK k hk)
  · rw [hlC]
    exact labC.2
  · rw [hlN]
    exact labN.2
  · rw [hlC, forest_eqC]
    dsimp only
    exact partK_sound c0_eq c1_eq rootsC_bind (allN_spec pC) (allN_spec rC)
  · rw [hlN, forest_eqN]
    dsimp only
    exact partK_sound ns0_eq ns1_eq rootsN_bind (allN_spec pN) (allN_spec rN)

end CertificateChecks.KernelSporSch.RuOr

end
