module

public import Certificates.Data.Kernel.PermCent.Sz8CentH

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5115

open CFSG.GH74.KGroups.Sz8

theorem kH : (centH && (elemsC QS).contains q0) = true := by decide +kernel

theorem q0_mem : q0 ∈ elemsC QS := by
  have h := (Bool.and_eq_true _ _).mp kH
  have h2 := h.2
  rw [contains_cv] at h2
  exact of_decide_eq_true h2

theorem centH_eq : centH = (elemsC QA).all (centF (elemsC QS)) :=
  centH_gen (levelsC QA) (elemsC QS) q0 q0_mem

theorem k5115 : centInC (elemsC QA) (elemsC QS) = true :=
  centH_eq.symm.trans ((Bool.and_eq_true _ _).mp kH).1

end CFSG.Certificates.Kernel.PkCV.KGrp.K5115
