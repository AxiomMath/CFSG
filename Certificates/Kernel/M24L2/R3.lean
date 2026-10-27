module

public import Certificates.Kernel.M24L2.Ctx
public import Certificates.Kernel.M24L2.R3Check
public import CFSG.Certificates.Kernel.M24L2.R3Sound

public section

namespace CertificateChecks.KernelM24L2

open CFSG.KC.M24L2 CFSG.CGT.L5R.R3 CFSG.CGT.M24R

theorem centK_all : ∀ k < 20, centK k = true := by
  intro k hk
  interval_cases k
  exacts [centK0, centK1, centK2, centK3, centK4, centK5, centK6, centK7, centK8, centK9, centK10,
    centK11, centK12, centK13, centK14, centK15, centK16, centK17, centK18, centK19]

theorem centE_spec {E : List (Nat × Nat × Nat)} (h : centE E = true) :
    centM (cwK (yW 0)) (cwK (yW 1)) 33825 = true ∧
      ∀ e ∈ E, centM (cwK (yW 0)) (cwK (yW 1)) e.1 = true := by
  unfold centE at h
  rw [letN_eq, letN_eq, Bool.and_eq_true, allL_eq, List.all_eq_true] at h
  exact ⟨h.1, fun e he => by have := h.2 e he; rwa [letN_eq] at this⟩

theorem glES_length : glES.length = 20 := rfl

theorem centM_glL : ∀ m ∈ glL, centM (cwK (yW 0)) (cwK (yW 1)) m = true := by
  intro m hm
  unfold glL at hm
  rcases List.mem_cons.1 hm with rfl | hm
  · exact (centE_spec (centK_all 0 (by norm_num))).1
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hm
    obtain ⟨E, hE, heE⟩ := List.mem_flatten.1 he
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hE
    have h := centK_all k (by rw [glES_length] at hk; exact hk)
    unfold centK at h
    rw [List.getD_eq_getElem _ _ hk] at h
    exact (centE_spec h).2 e heE

theorem r3_facts : identCheck = true ∧ centCheck (mkCtx ()) = true :=
  ⟨identCheck_eq ▸ ident_ok, centCheck_of reach.1 reach.2.2.1 centM_glL⟩

end CertificateChecks.KernelM24L2
