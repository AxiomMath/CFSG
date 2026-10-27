
module

public import Certificates.Kernel.U43Rho.Checks
public import Certificates.Kernel.CU43Aut.ModelFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3UExtBase
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUCheck

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Rho

open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.LieType.Multipliers.U43
  CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.U16
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut

theorem rep_RH : Rep 820 (unpack 820 10 (RH 0)) rhoPerm := fun i => by
  rw [CFSG.KS.Raw.Orb.unpack_get i.2, rhoPerm_apply]
  exact Nat.eq_of_beq_eq_true (allN_spec kRhoPt i i.2)

theorem kRho_facts : Nat.beq (pc (RH 0) (RH 0)) (pidn 820 10) = true ∧
    inPK (pc (RH 0) (TKI 5)) = true :=
  (bAnd_iff _ _).1 kRho

theorem rho_sq_K : rhoPerm * rhoPerm = 1 :=
  eq_of_pk (rep_pc rep_RH rep_RH) rep_pid kRho_facts.1

theorem rho_coset_K : rhoPerm * (tP 5)⁻¹ ∈ P :=
  mem_of_inPK (rep_pc rep_RH (rep_TKI (by norm_num))) kRho_facts.2

theorem mulTab_eq_mulD : ∀ j < 8, ∀ k < 8, mulTab j k = mulD j k := by decide

theorem d8C : d8Check = true := by
  unfold d8Check
  simp only [List.all_eq_true, List.mem_range]
  intro j hj k hk
  rw [mulTab_eq_mulD j hj k hk]
  exact (eqA_iff (rep_compA (rep_tA j) (rep_tA k)) (rep_tA _)).2 (tP_mul_eq hj hk)

theorem rhoCosetC : rhoCosetCheck = true := by
  unfold rhoCosetCheck
  rw [Bool.and_eq_true]
  exact ⟨(eqA_iff (rep_compA rep_rhoArr rep_rhoArr) rep_idA).2 rho_sq_K,
    (inP_iff (rep_compA rep_rhoArr (CFSG.KC.Misc.RuInv.P.rep_invCand (rep_tA 5)))).2 rho_coset_K⟩

theorem facts27826 : d8Check = true ∧ rhoCosetCheck = true := ⟨d8C, rhoCosetC⟩

end CertificateChecks.KernelU43Rho

end
