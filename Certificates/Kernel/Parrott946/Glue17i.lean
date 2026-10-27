
module

public import Certificates.Kernel.Parrott946.Glue17h

set_option maxRecDepth 400000

public section

namespace CertificateChecks.Parrott946

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw.Orb CFSG.KC.OrbGroup CFSG.KC.A45Cls CFSG.KC.OrbFind
  CFSG.KC.Parrott946 CFSG.Certificates.Kernel.PkCV CFSG.ComponentClassification.CatFactsSmall.PSp43
  CFSG.RankThree.GF2n.Parrott CFSG.GH74.KGroups CertificateChecks.KernelA45 Subgroup
  CFSG.Sporadic.Schreier

local notation "P45" => Equiv.Perm (Fin 45)

theorem Ms_lt : ∀ c ∈ Ms, c < 2 ^ 64 := by
  intro c hc
  simp only [Ms, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem meet_one {js : List ℕ} {m : ℕ} (hjs : ∀ j ∈ js, j < 43)
    (hspan : spanOK js m = true) (hm : m < 2 ^ 43) {j k : ℕ} (hj : j < 43) (hk : k < 49)
    (h0 : bitB D17.M0 j = true) (h1 : bitB m j = true)
    (h2 : eq22 45 6 (mask 6) (wE k) (iE j) (pc (wE 1) (wE 0)) (wE k) = true) {X : List P45}
    (hX : X = prodSpan (js.map xI)) :
    meetUtB (elemsT QA45) (Slist ()) X = true := by
  unfold meetUtB
  rw [tab_eq, hX]
  refine List.any_eq_true.2 ⟨xI j, (span_set hjs hspan hm _).2 (Or.inr ⟨j, hj, h1, rfl⟩), ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hS : xI j ∈ Slist () := by
    rw [Slist, tabList_eq, tabList_eq, gens_eq.1]
    exact (span_set (mem43 (by decide)) c17_spans.1 masks_lt.1 _).2 (Or.inr ⟨j, hj, h0, rfl⟩)
  have hw := prep_wE hk
  have e := mul_eq_of_eq22 hw.1 (xI_spec hj).1 prep_ut hw.1 h2
  refine ⟨⟨(xI_spec hj).2.2.2, hS⟩, List.any_eq_true.2 ⟨wv17 k,
    (mem_elemsT QA45 QA45_ok _).2 hw.2, decide_eq_true ?_⟩⟩
  rw [e, mul_inv_cancel_right]

theorem e16_meet_s : e16MeetCheck () = true := by
  have l0 : lane 64 (packL 64 Ms) 0 = D17.M0 := lane_packL Ms_lt (by decide)
  have l1 : lane 64 (packL 64 Ms) 1 = D17.M1 := lane_packL Ms_lt (by decide)
  have l2 : lane 64 (packL 64 Ms) 2 = D17.M2 := lane_packL Ms_lt (by decide)
  have l3 : lane 64 (packL 64 Ms) 3 = D17.M3 := lane_packL Ms_lt (by decide)
  have h := c17_meet.1
  have r0 := allL_spec h 0 (by decide)
  have r1 := allL_spec h 1 (by decide)
  have r2 := allL_spec h 2 (by decide)
  have r3 := allL_spec h 3 (by decide)
  rw [strictB_eq', strictB_eq', Bool.and_eq_true, Bool.and_eq_true] at r0 r1 r2 r3
  rw [l0] at r0
  rw [l1] at r1
  rw [l2] at r2
  rw [l3] at r3
  have eS : Slist () = prodSpan ([6, 21, 31, 41].map xI) := by
    rw [Slist, tabList_eq, tabList_eq, gens_eq.1]
  have e3 : E3list () = prodSpan ([25, 21, 38, 41].map xI) := by
    rw [E3list, tabList_eq, tabList_eq, gens_eq.2.1]
  have e1 : E1list () = prodSpan ([11, 6, 41, 21].map xI) := by
    rw [E1list, tabList_eq, tabList_eq, gens_eq.2.2.1]
  have e2 : E2list () = prodSpan ([12, 14, 41, 21].map xI) := by
    rw [E2list, tabList_eq, tabList_eq, gens_eq.2.2.2]
  unfold e16MeetCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact meet_one (mem43 (by decide)) c17_spans.1 masks_lt.1 (j := 0) (k := 45) (by decide)
      (by decide) r0.1.1 r0.1.2 r0.2 eS
  · exact meet_one (mem43 (by decide)) c17_spans.2.1 masks_lt.2.1 (j := 20) (k := 46) (by decide)
      (by decide) r1.1.1 r1.1.2 r1.2 e3
  · exact meet_one (mem43 (by decide)) c17_spans.2.2.1 masks_lt.2.2.1 (j := 7) (k := 47)
      (by decide) (by decide) r2.1.1 r2.1.2 r2.2 e1
  · exact meet_one (mem43 (by decide)) c17_spans.2.2.2 masks_lt.2.2.2 (j := 0) (k := 48)
      (by decide) (by decide) r3.1.1 r3.1.2 r3.2 e2

end CertificateChecks.Parrott946

end
