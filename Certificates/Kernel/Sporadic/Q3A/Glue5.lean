
module

public import Certificates.Kernel.Sporadic.Q3A.Glue4

public section

namespace CertificateChecks.KernelSpor.Q3AG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.Q3A.Check
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.Q3AK

section Checks

variable (hv : ∀ i < 22880, vtOK i = true) (hf : ∀ i < 22880, frOK i = true)
  (hds : ∀ k < 3, dsChk k = true) (hci : ∀ k < 3, ∀ a < dlK k, ciSl k a = true)
include hv hf hds hci

omit hci in
theorem cr_mem {k a : Nat} (hk : k < 2) (ha : a < dlK k) :
    (dsK k a, cArrInv (dsK k a)) ∈ ((nbrsOf (rtK k)).filter isNbr0).map fun c => (c, cArrInv c) := by
  obtain ⟨h1, h2, h3⟩ := (ds_parts (hds k (by omega))).2.2 a ha
  refine Array.mem_map.2 ⟨dsK k a, Array.mem_filter.2 ⟨?_, ?_⟩, rfl⟩
  · rw [nbrsOf_eq hv hf (rt_lt (by omega)), List.mem_toArray, h2]
    exact List.mem_map.2 ⟨_, List.mem_range.2 h1, rfl⟩
  · rw [isNbr0_vd hv hf]
    have hr : rdK k = 2 := by obtain rfl | rfl : k = 0 ∨ k = 1 := (by omega) <;> rfl
    omega

theorem adjWith_ds {k a v : Nat} (hk : k < 2) (ha : a < dlK k) (hv' : v < 22880) :
    adjWith (cArrInv (dsK k a)) v = adjK (ciK k a) v := by
  unfold adjWith
  rw [actIdx_eq hv (p_cArrInv hv (ds_lt hds (by omega) ha)) hv',
    ci_eq (hci k (by omega) a ha) (Or.inl hk), Bool.eq_iff_iff, isNbr0_iff hv hf, adjK_iff]

theorem q2_ok {k : Nat} (hk : k < 2) (hq : ∀ t < 486, q2Sl k t = true) :
    q2At (rtK k) = true := by
  have hr := rt_lt (k := k) (by omega)
  simp only [q2At]
  rw [all_nbrs hv hf hr]
  intro t ht
  have h := hq t ht
  unfold q2Sl at h
  rw [sB, sB, sB, sB] at h
  generalize actK (cA (rtK k)) (n0K t) = g at h ⊢
  generalize Q3AQ (Nat.add (Nat.mul 512 k) t) = w at h
  rw [Bool.or_eq_true, Bool.or_eq_true, vDist_eq hv hf hds]
  by_cases hg2 : vdK g = 2
  swap
  · exact Or.inl (Or.inl (by simpa using hg2))
  have hg := (vdK_two hg2).1
  rw [bIf_eq] at h
  split_ifs at h with hw
  · rw [hg2] at h
    exact absurd h (by decide)
  rw [band] at h
  obtain ⟨ha, h⟩ := h
  have ha' := nblt.1 ha
  rw [bIf_eq] at h
  split_ifs at h with hty
  · refine Or.inl (Or.inr (Array.any_eq_true'.2 ⟨_, cr_mem hv hf hds hk ha', ?_⟩))
    rw [adjWith_ds hv hf hds hci hk ha' hg]
    exact h
  · rw [band, sB, band, sB, band] at h
    obtain ⟨-, hu, hc1, hc2⟩ := h
    refine Or.inr (Array.any_eq_true'.2 ⟨_, cr_mem hv hf hds hk ha', ?_⟩)
    have hc' := vdK_one.1 (nbeq.1 hc1)
    have hmem : actK (cA g) (n0K (Nat.div w 128)) ∈ nbrsOf g := by
      rw [nbrsOf_eq hv hf hg, List.mem_toArray]
      exact List.mem_map.2 ⟨Nat.div w 128, List.mem_range.2 (nblt.1 hu), rfl⟩
    refine Array.any_eq_true'.2 ⟨_, Array.mem_filter.2 ⟨hmem, (isNbr0_iff hv hf _).2 hc'⟩, ?_⟩
    rw [adjWith_ds hv hf hds hci hk ha' hc'.1]
    exact hc2

theorem q2OK_true (hq : ∀ k < 2, ∀ t < 486, q2Sl k t = true) : q2OK = true := by
  obtain ⟨e0, -, -, e10, e202⟩ := rootDist_vals hv hf hds
  unfold q2OK
  refine roots_all ?_ ?_ ?_ ?_ ?_
  · rw [e0]; rfl
  · rw [Bool.or_eq_true]
    exact Or.inr (q2_ok hv hf hds hci (k := 0) (by norm_num) (hq 0 (by norm_num)))
  · rw [Bool.or_eq_true]
    exact Or.inr (q2_ok hv hf hds hci (k := 1) (by norm_num) (hq 1 (by norm_num)))
  · rw [e10]; rfl
  · rw [e202]; rfl

theorem q3aOK_of (hsp : ∀ k < 3, ∀ a < dlK k, spSl k a = true)
    (hq : ∀ k < 2, ∀ t < 486, q2Sl k t = true) : q3aOK = true := by
  unfold q3aOK
  rw [vertOK_true hv, forestOK_true hv hf, nbrOrbOK_true hv hf, distOK_true hv hf hds,
    spanOK_true hv hf hds hci hsp, q2OK_true hv hf hds hci hq, layer3OK_true hv hf hds]
  rfl

end Checks

end CertificateChecks.KernelSpor.Q3AG

end
