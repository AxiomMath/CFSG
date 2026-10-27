module

public import Certificates.Kernel.SporSch.PairJ3.C81Rows
public import Certificates.Kernel.SporSch.PairJ3.C81Five

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 200000

namespace CertificateChecks.KernelSporSch.PJ3C81

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CFSG.Certificates CFSG.Certificates.Native
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.PairNative CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.PJ3Count CFSG.Sporadic.SmallOddCore Subgroup

theorem orderOf_six {M : Type*} [Monoid M] {y : M} (h6 : y ^ 6 = 1) (h2 : y ^ 2 ≠ 1)
    (h3 : y ^ 3 ≠ 1) : orderOf y = 6 := by
  have hd : orderOf y ∣ 6 := orderOf_dvd_of_pow_eq_one h6
  have n2 : ¬ orderOf y ∣ 2 := fun h => h2 (orderOf_dvd_iff_pow_eq_one.1 h)
  have n3 : ¬ orderOf y ∣ 3 := fun h => h3 (orderOf_dvd_iff_pow_eq_one.1 h)
  have hle : orderOf y ≤ 6 := Nat.le_of_dvd (by norm_num) hd
  generalize orderOf y = o at hd n2 n3 hle ⊢
  interval_cases o <;> omega

section J3


theorem toJ {x : Equiv.Perm (Fin 6156)} (h : x ∈ P3) : x ∈ j3P := by
  rw [P_eq3]
  exact h

theorem ofJ {x : Equiv.Perm (Fin 6156)} (h : x ∈ j3P) : x ∈ P3 := by
  rw [← P_eq3]
  exact h

theorem stab : j3StabFact := by
  intro x hx
  have hst := (ptF x.2).2.2.2.2
  unfold stAt at hst
  have hx0 : Nat.beq (x : Nat) 0 = false := by
    cases h : Nat.beq (x : Nat) 0
    · rfl
    · exact absurd (Fin.ext (Nat.eq_of_beq_eq_true h)) hx
  rw [hx0] at hst
  obtain ⟨F, hF, hne⟩ := listRec_exists (x := x) stNFs hst
  have hall := listRec_all stNFs smF.2.1 F hF
  refine ⟨E F, toJ (E_mem hall.1), Fin.ext ((nfp_rep hall.1 0 (by norm_num)).symm.trans hall.2),
    fun e => hne ((nfp_rep hall.1 x x.2).trans (congrArg Fin.val e))⟩

theorem T21inv : (Tb 21)⁻¹ = Tb 21 := inv_eq_of_mul_eq_one_right T21_2

theorem UU (y : Equiv.Perm (Fin 6156)) : U * (U * y) = y := by rw [← mul_assoc, U2, one_mul]

theorem TT (y : Equiv.Perm (Fin 6156)) : Tb 21 * (Tb 21 * y) = y := by
  rw [← mul_assoc, T21_2, one_mul]

theorem cover : ∀ t ∈ j3P ⊔ zpowers U, orderOf t = 2 →
    ∃ r ∈ j3Rows, ∃ g ∈ j3P, t = g * tp 6156 r.rep * g⁻¹ := by
  intro t ht ht2
  by_cases htP : t ∈ P3
  · obtain ⟨c, hc⟩ := isConj_iff.1 (invol_conj (x := ⟨t, htP⟩) (by rw [Subgroup.orderOf_mk]; exact ht2))
    obtain ⟨d, hd⟩ := isConj_iff.1 (invol_conj (x := ⟨Tb 9, t9_mem⟩)
      (by rw [Subgroup.orderOf_mk]; exact t9_ord))
    have hc' : (c : Equiv.Perm (Fin 6156)) * tE * (c : Equiv.Perm (Fin 6156))⁻¹ = t :=
      congrArg Subtype.val hc
    have hd' : (d : Equiv.Perm (Fin 6156)) * tE * (d : Equiv.Perm (Fin 6156))⁻¹ = Tb 9 :=
      congrArg Subtype.val hd
    refine ⟨_, List.mem_cons_self, (c : Equiv.Perm (Fin 6156)) * (d : Equiv.Perm (Fin 6156))⁻¹,
      toJ (P3.mul_mem c.2 (P3.inv_mem d.2)), ?_⟩
    change t = (c : Equiv.Perm (Fin 6156)) * (d : Equiv.Perm (Fin 6156))⁻¹ * Tb 9 *
      ((c : Equiv.Perm (Fin 6156)) * (d : Equiv.Perm (Fin 6156))⁻¹)⁻¹
    rw [← hc', ← hd']
    group
  · have hS : Nat.card Ssub = 2 ^ (Nat.card ↥(j3P ⊔ zpowers U)).factorization 2 := by
      rw [card_S, card_R, PJ3Group.factorization_eq Nat.prime_two (m := 392445) (k := 8)
        (by norm_num) (by norm_num)]
      norm_num
    obtain ⟨x, hxR, hxS⟩ := exists_conj_mem_of_card S_le hS ht ht2
    have hs2 : x⁻¹ * t * x * (x⁻¹ * t * x) = 1 := by
      have : t * t = 1 := by rw [← sq, ← ht2, pow_orderOf_eq_one]
      calc x⁻¹ * t * x * (x⁻¹ * t * x) = x⁻¹ * (t * t) * x := by group
        _ = 1 := by rw [this]; group
    have hsP : x⁻¹ * t * x ∉ P3 := by
      intro hs
      apply htP
      rcases (R_mem x).1 hxR with hxP | hxU
      · rw [P_eq3] at hxP
        have := P3.mul_mem (P3.mul_mem hxP hs) (P3.inv_mem hxP)
        rwa [show x * (x⁻¹ * t * x) * x⁻¹ = t by group] at this
      · rw [P_eq3] at hxU
        have h1 := P3.mul_mem (P3.mul_mem hxU (conjU_mem hs)) (P3.inv_mem hxU)
        have e : x * U * (U * (x⁻¹ * t * x) * U) * (x * U)⁻¹ = t := by
          simp only [mul_assoc, mul_inv_rev, Uinv, UU, mul_inv_cancel, mul_one]
          group
        rwa [e] at h1
    obtain ⟨c, hc, hsc⟩ := outer_conj hxS hsP hs2
    refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
    change ∃ g ∈ j3P, t = g * Tb 21 * g⁻¹
    have ht' : t = x * (c * Tb 21 * c⁻¹) * x⁻¹ := by
      rw [← hsc]
      group
    rcases (R_mem x).1 hxR with hxP | hxU
    · refine ⟨x * c, toJ (P3.mul_mem (ofJ hxP) hc), ?_⟩
      rw [ht']
      group
    · have hxU' : x * U ∈ P3 := ofJ hxU
      have hUt : U * Tb 21 ∈ P3 := by
        have := P3.inv_mem T21U
        rwa [mul_inv_rev, Uinv, T21inv] at this
      refine ⟨x * U * (U * c * U) * (U * Tb 21),
        toJ (P3.mul_mem (P3.mul_mem hxU' (conjU_mem hc)) hUt), ?_⟩
      rw [ht']
      simp only [mul_assoc, mul_inv_rev, Uinv, T21inv, UU, TT]

theorem rows : ∀ r ∈ j3Rows, tp 6156 r.rep ∈ j3P ⊔ zpowers U ∧
    orderOf (tp 6156 r.rep) = 2 ∧ (r.outer = true ↔ tp 6156 r.rep ∉ j3P) ∧
    closure (tp 6156 '' {x | x ∈ r.centGens.toArray}) =
      j3P ⊓ centralizer ({tp 6156 r.rep} : Set _) ∧
    Nat.card ↥(j3P ⊓ centralizer ({tp 6156 r.rep} : Set (Equiv.Perm (Fin 6156)))) =
      r.centOrder ∧
    (conjClass j3P (tp 6156 r.rep)).ncard = r.classSize ∧
    CFSG.oddCore ↥(j3P ⊓ centralizer ({tp 6156 r.rep} : Set (Equiv.Perm (Fin 6156)))) = ⊥ := by
  intro r hr
  simp only [j3Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact row1
  · exact row2

theorem oddAll : ∀ t ∈ j3P ⊔ zpowers U, orderOf t = 2 →
    CFSG.oddCore ↥(j3P ⊓ centralizer ({t} : Set (Equiv.Perm (Fin 6156)))) = ⊥ := by
  intro t ht ht2
  obtain ⟨r, hr, g, hg, rfl⟩ := cover t ht ht2
  exact oddCore_inf_centralizer_conj j3P hg (rows r hr).2.2.2.2.2.2

theorem concl : j3CentConcl := by
  unfold j3CentConcl
  rw [U_def]
  exact ⟨Usq, U_ne, U_notP, map_eq, R_mem, card_R, S_le, card_S, rows, cover, oddAll⟩

theorem five : j3FiveWit := by
  obtain ⟨-, o2, -, -⟩ := oddFacts
  obtain ⟨a2, b2, c2, d2, e2, f2, g2⟩ := oddParts (q := 5) rfl o2
  have hy := y_rep (e := 1) a2 b2
  have hm := y_mem (e := 1) a2 b2
  have h6 : (E 281475052077923 ^ 1 * (E 281474999390686 * E 281475052077923 ^ 1 *
      (E 281474999390686)⁻¹)) ^ 6 = 1 :=
    (fixL_iff hH hbs (hy.powF 6) (P3.pow_mem hm _)).1 f2
  have h3 : (E 281475052077923 ^ 1 * (E 281474999390686 * E 281475052077923 ^ 1 *
      (E 281474999390686)⁻¹)) ^ 3 ≠ 1 := fun he =>
    (bNot_iff _).1 g2 ((fixL_iff hH hbs (hy.powF 3) (P3.pow_mem hm _)).2 he)
  have h2 : (E 281475052077923 ^ 1 * (E 281474999390686 * E 281475052077923 ^ 1 *
      (E 281474999390686)⁻¹)) ^ 2 ≠ 1 := fun he =>
    (bNot_iff _).1 five_sq ((fixL_iff hH hbs (hy.powF 2) (P3.pow_mem hm _)).2 he)
  have h66 := orderOf_six h6 h2 h3
  rw [pow_one] at h66
  refine ⟨E 281475052077923, mem_cent (E_mem a2) (comm0 (nfp_rep a2) (E_mem a2) d2),
    (ordPL_iff hH hbs (nfp_rep a2) (E_mem a2) (by norm_num)).1 c2, E 281474999390686,
    mem_cent (E_mem b2) (comm0 (nfp_rep b2) (E_mem b2) e2), h66⟩

theorem facts : j3CentFacts := ⟨stab, concl, five⟩

end J3

end CertificateChecks.KernelSporSch.PJ3C81

end
