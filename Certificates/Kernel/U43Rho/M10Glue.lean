module

public import Certificates.Kernel.U43Rho.M10Checks
public import Certificates.Kernel.U43Rho.Glue
import CFSG.Certificates.Kernel.U43Mod.ArrSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CU43Model

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Rho

open CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.LieType.Multipliers.U43
  CFSG.EvenSporadicStandard.Fin76b
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut


theorem fP_inv : fP⁻¹ = fP :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact f_pow2)

theorem rep_f_inv : Rep 820 (unpack 820 10 (CU43T 1)) fP⁻¹ := by
  rw [fP_inv]
  exact rep_f

theorem ne_one_of_moved {p : ℕ} {g : Equiv.Perm (Fin 820)} (hp : Rep 820 (unpack 820 10 p) g)
    (h : bIf(Nat.beq (pg 10 (mask 10) p 0) 0, false, true) = true) : g ≠ 1 := by
  intro hg
  have h0 := hp ⟨0, by norm_num⟩
  rw [CFSG.KS.Raw.Orb.unpack_get (by norm_num : (0 : ℕ) < 820), hg, Equiv.Perm.one_apply] at h0
  have hb : Nat.beq (pg 10 (mask 10) p 0) 0 = true := by
    rw [h0]
    rfl
  rw [hb] at h
  exact absurd h (by decide)

theorem rhoCheck_K : rhoCheck = true := by
  unfold rhoCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact CFSG.KS.U43Mod.isInvA_of_rep rep_rhoArr (CFSG.KC.Misc.RuInv.P.rep_invCand rep_rhoArr)
  · exact (eqA_iff (rep_compA rep_rhoArr rep_rhoArr) rep_idA).2 rho_sq_K
  · exact (inP_iff (rep_compA rep_rhoArr (CFSG.KC.Misc.RuInv.P.rep_invCand (rep_tA 5)))).2
      rho_coset_K
  · exact (inP_iff (rep_compA rep_fA (rep_compA (rep_tA 5)
      (rep_compA (CFSG.KC.Misc.RuInv.P.rep_invCand rep_fA)
        (CFSG.KC.Misc.RuInv.P.rep_invCand (rep_tA 7)))))).2
      (mem_of_inPK (rep_pc rep_f (rep_pc (rep_TK 5) (rep_pc rep_f_inv
        (rep_TKI (by norm_num))))) kPhi57)
  · exact (inP_iff (rep_compA rep_fA (rep_compA (rep_tA 7)
      (rep_compA (CFSG.KC.Misc.RuInv.P.rep_invCand rep_fA)
        (CFSG.KC.Misc.RuInv.P.rep_invCand (rep_tA 5)))))).2
      (mem_of_inPK (rep_pc rep_f (rep_pc (rep_TK 7) (rep_pc rep_f_inv
        (rep_TKI (by norm_num))))) kPhi75)

theorem order6Check_K : order6Check = true := by
  have e : order6W = unpack 820 10 (O6 0) := arr_of_bind kO6b
  obtain ⟨e1, e2⟩ := invEqK_sound kO6i
  have hinv : isInvA 820 order6W (invCand 820 order6W) = true := by
    rw [e, e1]
    exact e2
  have hrep := (rep_permOfArr hinv).1
  have hrepU : Rep 820 (unpack 820 10 (O6 0)) (permOfArr 820 order6W) := by
    rw [← e]
    exact hrep
  have hr8 : Rep 820 reps[8]! (rP 8) := rep_rP (by norm_num)
  have hr8U : Rep 820 (unpack 820 10 (CU43T 10)) (rP 8) := by
    rw [← reps_T 8 (by norm_num)]
    exact hr8
  have hn2 := ne_one_of_moved (rep_ppow hrepU 2) kO6m2
  have hn3 := ne_one_of_moved (rep_ppow hrepU 3) kO6m3
  unfold order6Check
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨hinv, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · exact (inP_iff hrep).2 (mem_of_inPK hrepU kO6p)
  · exact (eqA_iff (rep_compA hrep hr8) (rep_compA hr8 hrep)).2
      (eq_of_pk (rep_pc hrepU hr8U) (rep_pc hr8U hrepU) kO6c)
  · exact (eqA_iff (CFSG.EvenSporadicStandard.M24Std.CU43.rep_powA hrep 6) rep_idA).2
      (eq_of_pk (rep_ppow hrepU 6) rep_pid kO6e)
  · cases h : eqA 820 (powA 820 order6W 2) (idA 820)
    · rfl
    · exact absurd ((eqA_iff (CFSG.EvenSporadicStandard.M24Std.CU43.rep_powA hrep 2) rep_idA).1 h)
        hn2
  · cases h : eqA 820 (powA 820 order6W 3) (idA 820)
    · rfl
    · exact absurd ((eqA_iff (CFSG.EvenSporadicStandard.M24Std.CU43.rep_powA hrep 3) rep_idA).1 h)
        hn3

end CertificateChecks.KernelU43Rho
