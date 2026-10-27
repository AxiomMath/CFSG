
module

public import Certificates.Kernel.PermCent.KG5124
public import CFSG.Certificates.Kernel.PermCent.KGrpCSound
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ClassCard

@[expose] public section

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5124

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkEnum CFSG.Certificates
  CFSG.Sporadic.Schreier CFSG.GH74.GLS.Stage1.Thm6.Sec13

theorem cOf_ev' (c : CV 42) : cOf (ev c) = c := ev_injective (ev_cOf (ev c))

theorem mem_of_siftC (Q : RawSchreierDatum 42) (hQ : ValidSchreier Q) (g : Equiv.Perm (Fin 42))
    (h : siftC Q (cOf g) 0 = true) : g ∈ Q.originalSubgroup := by
  rw [mem_iff_sift Q hQ, ← ev_cOf g, sift_ev]
  exact h

theorem comm_of_eq22C {a b : Equiv.Perm (Fin 42)}
    (h : eq22C (cOf a) (cOf b) (cOf b) (cOf a) = true) : a * b = b * a := by
  rw [eq22C_eq, decide_eq_true_iff] at h
  have := congrArg ev h
  rwa [← ev_mul', ← ev_mul', ev_cOf, ev_cOf] at this

theorem x0_order : orderOf x0 = 2 := by
  rw [← orderIs_iff x0 (by norm_num), ← ev_cOf x0, orderIs_C]
  exact kX0.2

theorem P_le_A' : QP.originalSubgroup ≤ QA.originalSubgroup := by
  rw [QP_closure, Subgroup.closure_le, QA, certificate_originalSubgroup]
  intro g hg
  apply Subgroup.subset_closure
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl <;> simp

theorem QH_ok : ValidSchreier QH := check_certificate_of _ _ _ _ _ kQH.1

end CFSG.Certificates.Kernel.PkCV.KGrp.K5124
