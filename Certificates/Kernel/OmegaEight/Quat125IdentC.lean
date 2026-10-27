module

public import Certificates.Kernel.OmegaEight.Quat125IdentB
public import CFSG.ClassicalInvolution.Q3.Q3TLTO8
import CFSG.Certificates.Kernel.PackSetSound
public import Certificates.Kernel.OmegaEight.Quat125Glue

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.Q125

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
open CertificateChecks.KernelO8 CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.KC.PCent CFSG.KC.Misc.ArrEnum

section Ident


theorem q125_u0_mem : toPerm 360 9 e4U ∈ omegaT := by
  rw [E4C.e4c_u0]
  exact (omegaW_spec (w := CFSG.ClassicalInvolution.Q3.TL4.E4O8.cw 0
    CFSG.ClassicalInvolution.Q3.TL4.E4O8Data.u0Word) (by decide +kernel)).2

theorem q125_v0_mem : toPerm 360 9 om0V ∈ omegaT := by
  rw [E4C.e4c_v0]
  exact (omegaW_spec (w := CFSG.ClassicalInvolution.Q3.TL4.E4O8.cw 0
    CFSG.ClassicalInvolution.Q3.TL4.E4O8Data.v0Word) (by decide +kernel)).2

theorem q125K0_le : q125K0 ≤ omegaT := by
  rw [q125K0, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact q125_u0_mem
  · exact q125_v0_mem

theorem q125_conj_K0 (g : Equiv.Perm (Fin 360)) : conjSub g q125K0 =
    Subgroup.closure {g * toPerm 360 9 e4U * g⁻¹, g * toPerm 360 9 om0V * g⁻¹} := by
  unfold conjSub q125K0
  rw [MonoidHom.map_closure, Set.image_pair]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem q125_list_gen {j : Nat} (hj : j < 4) {g : Equiv.Perm (Fin 360)} (hg : g ∈ omegaT)
    (hPP : ∀ P ∈ q125PL.getD j [], CFSG.KC.BfsPin.PP 360 9 P)
    (hmem : ∀ P ∈ q125PL.getD j [], toPerm 360 9 P ∈ conjSub g q125K0)
    (hu : toPerm 360 9 ((q125PL.getD j []).getD 2 0) = g * toPerm 360 9 e4U * g⁻¹)
    (hv : toPerm 360 9 ((q125PL.getD j []).getD 4 0) = g * toPerm 360 9 om0V * g⁻¹)
    (hlen : (q125PL.getD j []).length = 8) {K' : Subgroup (Equiv.Perm (Fin 360))}
    (hK' : ∀ x, x ∈ K' ↔ x ∈ (lists.getD j []).map saElt) (hK'Ω : K' ≤ omegaT) :
    K' = conjSub g q125K0 := by
  have h := kLists125
  simp only [q125bAnd] at h
  have h' := CFSG.KC.Pack.allN_spec h.2.2.1 j hj
  obtain ⟨hl, ha⟩ := q125bAnd.1 h'
  have hl' : (lists.getD j []).length = 8 := Nat.eq_of_beq_eq_true hl
  have hgK : conjSub g q125K0 ≤ omegaT := fun x hx => by
    rw [mem_conjSub_iff] at hx
    rw [show x = g * (g⁻¹ * x * g) * g⁻¹ by group]
    exact omegaT.mul_mem (omegaT.mul_mem hg (q125K0_le hx)) (omegaT.inv_mem hg)
  have key : ∀ e < 8, saElt ((lists.getD j []).getD e 0) =
      toPerm 360 9 ((q125PL.getD j []).getD e 0) := by
    intro e he
    have hb := CFSG.KC.Pack.allN_spec ha e he
    beta_reduce at hb
    rw [q125sB] at hb
    obtain ⟨h8, hacts⟩ := q125bAnd.1 hb
    have hP : (q125PL.getD j []).getD e 0 ∈ q125PL.getD j [] := by
      rw [List.getD_eq_getElem (q125PL.getD j []) 0 (by rw [hlen]; exact he)]
      exact List.getElem_mem _
    have hA : (lists.getD j []).getD e 0 ∈ lists.getD j [] := by
      rw [List.getD_eq_getElem (lists.getD j []) 0 (by rw [hl']; exact he)]
      exact List.getElem_mem _
    have hx : saElt ((lists.getD j []).getD e 0) ∈ K' := (hK' _).2 (List.mem_map_of_mem hA)
    exact q125_eqΩ (hK'Ω hx) (hgK (hmem _ hP)) (q125_acts_elt (q125blt.1 h8))
      (q125_acts_pk (hPP _ hP) hacts)
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨a, haL, rfl⟩ := List.mem_map.1 ((hK' x).1 hx)
    obtain ⟨e, he, rfl⟩ := List.getElem_of_mem haL
    have he8 : e < 8 := hl' ▸ he
    have k := key e he8
    rw [List.getD_eq_getElem (lists.getD j []) 0 he] at k
    rw [k]
    refine hmem _ ?_
    rw [List.getD_eq_getElem (q125PL.getD j []) 0 (by rw [hlen]; exact he8)]
    exact List.getElem_mem _
  · rw [q125_conj_K0, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [← hu, ← key 2 (by norm_num)]
      exact (hK' _).2 (List.mem_map_of_mem (by
        rw [List.getD_eq_getElem (lists.getD j []) 0 (by rw [hl']; norm_num)]
        exact List.getElem_mem _))
    · rw [← hv, ← key 4 (by norm_num)]
      exact (hK' _).2 (List.mem_map_of_mem (by
        rw [List.getD_eq_getElem (lists.getD j []) 0 (by rw [hl']; norm_num)]
        exact List.getElem_mem _))

theorem q125_list_K0 {j : Nat} (hj : j < 4) {K' : Subgroup (Equiv.Perm (Fin 360))}
    (hK' : ∀ x, x ∈ K' ↔ x ∈ (lists.getD j []).map saElt) (hK'Ω : K' ≤ omegaT) :
    ∃ g ∈ omegaT, K' = conjSub g q125K0 := by
  obtain ⟨-, -, -, -, -, hpx, hpu, hpv⟩ := E4C.e4c_pm
  have hL : ∀ P ∈ e4L, CFSG.KC.BfsPin.PP 360 9 P ∧ toPerm 360 9 P ∈ q125K0 := by
    intro P hP
    refine ⟨?_, q125_mem_K0 (List.any_eq_true.2 ⟨P, hP, Nat.beq_refl P⟩)⟩
    simp only [e4L, e4Q, List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact CFSG.KC.BfsPin.PP.id E4C.ch550106sz
    · exact hpx
    · exact hpu
    · exact hpu.mul hpx
    · exact hpv
    · exact hpv.mul hpx
    · exact hpu.mul hpv
    · exact (hpu.mul hpv).mul hpx
  have hconj : ∀ {w : List Int}, lettersK 17 w = true → lettersOK 17 w = true →
      permB 360 9 (wO w) = true → q125PL.getD j [] = e4L.map (cjI (wO w) (pinv (wO w))) →
      ∃ g ∈ omegaT, K' = conjSub g q125K0 := by
    intro w hk ho hp he
    have hw := E4C.e4c_pp hp
    have hgm := E4C.e4c_word_mem hk ho hp
    refine ⟨toPerm 360 9 (wO w), hgm, q125_list_gen hj hgm ?_ ?_ ?_ ?_ ?_ hK' hK'Ω⟩
    · rw [he]
      intro P hP
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hP
      exact q125_PP_cj hw (hL x hx).1
    · rw [he]
      intro P hP
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hP
      change toPerm 360 9 (cj (wO w) x) ∈ _
      rw [q125_toPerm_cj hw (hL x hx).1]
      exact conj_mem_conjSub (hL x hx).2
    · rw [he]
      change toPerm 360 9 (cj (wO w) e4U) = _
      exact q125_toPerm_cj hw hpu
    · rw [he]
      change toPerm 360 9 (cj (wO w) om0V) = _
      exact q125_toPerm_cj hw hpv
    · rw [he, List.length_map]
      rfl
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · refine ⟨1, omegaT.one_mem, q125_list_gen (j := 0) (by norm_num) omegaT.one_mem
      (fun P hP => (hL P hP).1) (fun P hP => by rw [conjSub_one]; exact (hL P hP).2) ?_ ?_ rfl
      hK' hK'Ω⟩
    · change toPerm 360 9 e4U = _
      group
    · change toPerm 360 9 om0V = _
      group
  · exact hconj (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
  · exact hconj (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl
  · exact hconj (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl

theorem q125_gen_comm {i : Nat} (hi : i = 8 ∨ i = 9) : gen i * mainPerm 0 = mainPerm 0 * gen i := by
  have hC := kStrC
  simp only [q125bAnd] at hC
  have hc : cn (AP.S i) = true := CFSG.KC.Pack.allN_spec hC.1 i (by omega)
  have hm := (main_ok (i := 0) (by norm_num)).2.1
  have hl := kLink125
  simp only [q125bAnd] at hl
  have e : pc (AP.S i) (mainK 0) = pc (mainK 0) (AP.S i) := by
    rcases hi with rfl | rfl
    · exact Nat.eq_of_beq_eq_true hl.1
    · exact Nat.eq_of_beq_eq_true hl.2
  have rg : Rep 360 (unpack 360 9 (AP.S i)) (gen i) := by
    rw [← gen_get (by omega : i < 10)]
    exact rep_gen (by omega)
  have r1 := q125_rep_pc hc hm rg (q125_rep_main (t := 0) (by norm_num))
  rw [e] at r1
  exact r1.unique (q125_rep_pc hm hc (q125_rep_main (t := 0) (by norm_num)) rg)

theorem q125_omega_mul {a : Equiv.Perm (Fin 360)} (ha : a ∈ autT) :
    ∃ ω ∈ omegaT, ∃ c ∈ autT, c * mainPerm 0 = mainPerm 0 * c ∧ a = ω * c := by
  rw [autT_eq] at ha
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    by_cases h8' : i < 8
    · exact ⟨gen i, gen_mem_omegaT h8', 1, autT.one_mem, by group, by group⟩
    · exact ⟨1, omegaT.one_mem, gen i, gen_mem_autT hi, q125_gen_comm (by omega), by group⟩
  | one => exact ⟨1, omegaT.one_mem, 1, autT.one_mem, by group, by group⟩
  | mul x y _ _ hx hy =>
    obtain ⟨ω, hω, c, hc, hcx, rfl⟩ := hx
    obtain ⟨ω', hω', c', hc', hcx', rfl⟩ := hy
    refine ⟨ω * (c * ω' * c⁻¹), omegaT.mul_mem hω ((conj_mem_omegaT hc).1 hω'), c * c',
      autT.mul_mem hc hc', ?_, by group⟩
    calc c * c' * mainPerm 0 = c * (c' * mainPerm 0) := by group
      _ = c * (mainPerm 0 * c') := by rw [hcx']
      _ = c * mainPerm 0 * c' := by group
      _ = mainPerm 0 * c * c' := by rw [hcx]
      _ = mainPerm 0 * (c * c') := by group
  | inv x _ hx =>
    obtain ⟨ω, hω, c, hc, hcx, rfl⟩ := hx
    refine ⟨c⁻¹ * ω⁻¹ * c⁻¹⁻¹, (conj_mem_omegaT (autT.inv_mem hc)).1 (omegaT.inv_mem hω), c⁻¹,
      autT.inv_mem hc, ?_, by group⟩
    calc c⁻¹ * mainPerm 0 = c⁻¹ * (mainPerm 0 * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * mainPerm 0) * c⁻¹ := by rw [hcx]
      _ = mainPerm 0 * c⁻¹ := by group

theorem q125_ident {K : Subgroup (Equiv.Perm (Fin 360))} {s : Equiv.Perm (Fin 360)}
    (hd : Vtx.AmbientQuatDatum omegaT K s) : ∃ g ∈ omegaT, conjSub g K = q125K0 := by
  have hs : s ∈ omegaT := hd.le hd.inv.mem
  have hs2 : orderOf s = 2 := orderOf_eq_prime (by rw [sq]; exact hd.inv.sq) hd.inv.ne_one
  obtain ⟨i, hi, a, ha, rfl⟩ := CFSG.ClassicalInvolution.Q3.O8.exists_conj_main hs hs2
  have hd' := CFSG.KC.O8Quat.datum_conj_of_normalizes hd (g := a⁻¹)
    (fun _ => conj_mem_omegaT (autT.inv_mem ha))
  rw [show a⁻¹ * (a * mainPerm i * a⁻¹) * a⁻¹⁻¹ = mainPerm i by group] at hd'
  interval_cases i
  · obtain ⟨ω, hω, c, -, hcx, rfl⟩ := q125_omega_mul ha
    have hd0 := hd.conj (omegaT.inv_mem hω)
    rw [show ω⁻¹ * (ω * c * mainPerm 0 * (ω * c)⁻¹) * ω⁻¹⁻¹ = c * mainPerm 0 * c⁻¹ by group,
      hcx, mul_inv_cancel_right] at hd0
    obtain ⟨γ, hγ, j, hj, hK'⟩ := q125_ident0 hd0
    have hd1 := hd0.conj hγ
    obtain ⟨g, hg, hKg⟩ := q125_list_K0 hj hK' hd1.le
    refine ⟨g⁻¹ * γ * ω⁻¹, omegaT.mul_mem (omegaT.mul_mem (omegaT.inv_mem hg) hγ)
      (omegaT.inv_mem hω), ?_⟩
    rw [conjSub_mul, conjSub_mul, hKg, conjSub_inv_conjSub]
  · exact (q125_ident12 (Or.inl rfl) hd').elim
  · exact (q125_ident12 (Or.inr rfl) hd').elim

end Ident

end CertificateChecks.KernelO8.Q125

end
