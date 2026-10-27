
module

public import Certificates.Kernel.U43Rho.Glue
public import Certificates.Kernel.U43Rho.TExp
public import Certificates.Kernel.CU43Aut.SylGlue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelU43Rho

open Subgroup CFSG.EvenSporadicStandard.M24Std.CU43 CFSG.LieType.Multipliers.U43
  CFSG.EvenSporadicStandard.Fin76b
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative
open CertificateChecks.KernelU43B CertificateChecks.KernelCU43Aut
  CertificateChecks.KernelCU43Aut.CentG CertificateChecks.KernelCU43Aut.SylG

theorem slX_all : ∀ s < 8, slX s = true := by
  intro s hs
  interval_cases s
  exacts [tX0, tX1, tX2, tX3, tX4, tX5, tX6, tX7]

theorem pr_e8 {p : Nat} {g : Equiv.Perm (Fin 820)} (h : PR p g) : PR (e8K p) (g ^ 8) := by
  have h2 : PR (sqK p) (g * g) := pr_pc h h
  have h4 : PR (sqK (sqK p)) (g * g * (g * g)) := pr_pc h2 h2
  have h8 : PR (sqK (sqK (sqK p))) (g * g * (g * g) * (g * g * (g * g))) := pr_pc h4 h4
  have e : g ^ 8 = g * g * (g * g) * (g * g * (g * g)) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e]
  exact h8

theorem e8_T {i : Nat} (hi : i < 1024) : xT i ^ 8 = 1 := by
  have hs := slX_all (i / 128) (by omega)
  rw [slX.eq_1] at hs
  have h := allN_spec hs (i % 128) (Nat.mod_lt _ (by norm_num))
  rw [show Nat.add (Nat.mul 128 (i / 128)) (i % 128) = i by
    change 128 * (i / 128) + i % 128 = i; omega] at h
  exact pr_eq (pr_e8 (pr_xT hi)) pr_pidn (Nat.eq_of_beq_eq_true h)

theorem exp8_R {x : Equiv.Perm (Fin 820)} (hx : x ∈ R) (h16 : x ^ 16 = 1) : x ^ 8 = 1 := by
  have hcard : Nat.card (Tg.subgroupOf R) = 2 ^ (Nat.card R).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Tg_le_R).toEquiv, card_Tg, card_R', fact2]
    norm_num
  let S : Sylow 2 R := Sylow.ofCard (Tg.subgroupOf R) hcard
  let X : R := ⟨x, hx⟩
  have hX : X ^ (2 ^ 4) = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h16)
  have hZ : IsPGroup 2 (zpowers X) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hX)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hZ
  obtain ⟨g, hg⟩ := exists_conj_sylow S Q
  have hm := (hg X).1 (hQ (mem_zpowers X))
  have hS : ((S : Subgroup R)) = Tg.subgroupOf R := rfl
  rw [hS, mem_subgroupOf] at hm
  obtain ⟨i, hi, hxi⟩ := (mem_Tg _).1 hm
  have h8 := e8_T hi
  rw [hxi] at h8
  have e1 : (g⁻¹ * X * g) ^ 8 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h8)
  rw [show g⁻¹ * X * g = g⁻¹ * X * g⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv] at e1
  have e3 : X ^ 8 = 1 := by
    have := congrArg (fun y => g * y * g⁻¹) e1
    simpa [mul_assoc] using this
  have := congrArg Subtype.val e3
  rwa [Subgroup.coe_pow] at this

theorem rho_inv_K : rhoPerm⁻¹ = rhoPerm := inv_eq_of_mul_eq_one_right rho_sq_K

theorem rho_gen_K {g : Nat} (hg : g < 2) {G : Equiv.Perm (Fin 820)}
    (hG : Rep 820 (unpack 820 10 (C.S g)) G) : rhoPerm * G * rhoPerm⁻¹ ∈ P := by
  rw [rho_inv_K]
  exact mem_of_inPK (rep_pc (rep_pc rep_RH hG) rep_RH) (allN_spec kRhoNorm g hg)

theorem rep_S0 : Rep 820 (unpack 820 10 (C.S 0)) (psi xElt) := by
  rw [← binds.2.2.2.2.1 0 (by omega)]
  exact rep_tabA

theorem rep_S1 : Rep 820 (unpack 820 10 (C.S 1)) (psi yElt) := by
  rw [← binds.2.2.2.2.1 1 (by omega)]
  exact rep_tabB

theorem rho_normalizer_K : rhoPerm ∈ normalizer (P : Set (Equiv.Perm (Fin 820))) :=
  mem_normalizer_P_of_gens (rho_gen_K (by omega) rep_S0) (rho_gen_K (by omega) rep_S1)

theorem rho_norm_K (g : Equiv.Perm (Fin 820)) (hg : g ∈ P) : rhoPerm * g * rhoPerm⁻¹ ∈ P :=
  (mem_normalizer_iff.1 rho_normalizer_K g).1 hg

theorem rhoOK_K : rhoOK = true := by
  unfold rhoOK
  simp only [Bool.and_eq_true]
  have hρi := CFSG.KC.Misc.RuInv.P.rep_invCand rep_rhoArr
  refine ⟨⟨⟨CFSG.KC.Misc.RuInv.P.isInvA_invCand rep_rhoArr, ?_⟩, ?_⟩, ?_⟩
  · refine (inP_iff (rep_compA rep_rhoArr (rep_compA rep_tabA hρi))).2 ?_
    rw [← mul_assoc]
    exact rho_gen_K (by omega) rep_S0
  · refine (inP_iff (rep_compA rep_rhoArr (rep_compA rep_tabB hρi))).2 ?_
    rw [← mul_assoc]
    exact rho_gen_K (by omega) rep_S1
  · refine (inP_iff (rep_compA rep_rhoArr rep_rhoArr)).2 ?_
    rw [rho_sq_K]
    exact P.one_mem

theorem rho_mem_R_K : rhoPerm ∈ R := by
  have h := R.mul_mem (P_le_R rho_coset_K) (tP_mem_R (by norm_num : 5 < 8))
  rwa [inv_mul_cancel_right] at h

theorem countBadP_K : countBadP = 0 := by
  classical
  have hc : Nat.card {x : P // (x : Equiv.Perm (Fin 820)) ^ 16 = 1 ∧
      (x : Equiv.Perm (Fin 820)) ^ 8 ≠ 1} = countW bad16 blocks [] :=
    card_eq_countW_P (Pr := fun g => g ^ 16 = 1 ∧ g ^ 8 ≠ 1)
      (fun w g hw hgP => bad16_iff hw (P.pow_mem hgP _) (P.pow_mem hgP _))
  rw [countBadP, ← hc, Nat.card_eq_zero]
  exact Or.inl ⟨fun x => x.2.2 (exp8_R (P_le_R x.1.2) x.2.1)⟩

theorem countBadRho_K : countBadRho = 0 := by
  classical
  have hc : Nat.card {x : P // ((x : Equiv.Perm (Fin 820)) * rhoPerm) ^ 16 = 1 ∧
      ((x : Equiv.Perm (Fin 820)) * rhoPerm) ^ 8 ≠ 1} =
      countW (fun w => bad16 (rhoArr :: w)) blocks [] := by
    refine card_eq_countW_P (Pr := fun g => (g * rhoPerm) ^ 16 = 1 ∧ (g * rhoPerm) ^ 8 ≠ 1) ?_
    intro w g hw hgP
    have hsq : (g * rhoPerm) ^ 2 ∈ P := by
      have e : (g * rhoPerm) ^ 2 = g * (rhoPerm * g * rhoPerm⁻¹) * (rhoPerm * rhoPerm) := by
        rw [pow_two]
        simp only [mul_assoc, inv_mul_cancel_left]
      rw [e, rho_sq_K, mul_one]
      exact P.mul_mem hgP (rho_norm_K g hgP)
    exact bad16_iff (RepW.cons rep_rhoArr hw)
      (by rw [show (g * rhoPerm) ^ 16 = ((g * rhoPerm) ^ 2) ^ 8 by rw [← pow_mul]]
          exact P.pow_mem hsq _)
      (by rw [show (g * rhoPerm) ^ 8 = ((g * rhoPerm) ^ 2) ^ 4 by rw [← pow_mul]]
          exact P.pow_mem hsq _)
  rw [countBadRho, ← hc, Nat.card_eq_zero]
  exact Or.inl ⟨fun x => x.2.2 (exp8_R (R.mul_mem (P_le_R x.1.2) rho_mem_R_K) x.2.1)⟩

theorem facts26080 : rhoOK = true ∧ countBadP = 0 ∧ countBadRho = 0 :=
  ⟨rhoOK_K, countBadP_K, countBadRho_K⟩

end CertificateChecks.KernelU43Rho

end
