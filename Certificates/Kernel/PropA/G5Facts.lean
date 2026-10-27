module

import CFSG.Certificates.Kernel.OrbRow.PRepFacts
public import Certificates.Kernel.PropA.JFacts

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelPropA

open Equiv Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.Raw.Orb
  CFSG.KS.PRec CFSG.KS.PMem CFSG.EvenSporadicStandard.M12Std CFSG.EvenSporadicStandard.M12Std.PropA

theorem pa450010_wordEq {kS R : ℕ} {S SI : ℕ → ℕ} {gs : ℕ → Perm (Fin 28)} {wd : List Int}
    (hS : ∀ h < kS, PRep 28 5 (S h) (gs h)) (hSI : ∀ h < kS, PRep 28 5 (SI h) (gs h)⁻¹)
    (h : wordEqK 28 5 (mask 5) (pidn 28 5) S SI kS wd R = true) :
    PRep 28 5 R (Quiver.SchreierGraph.evalWord (fun h : Fin kS => gs h)
      (CFSG.Monster.B.Co2.toLetters kS wd)) := by
  unfold wordEqK at h
  rw [bAnd_eq, bAnd_eq, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨-, hl, he⟩ := h
  rw [← Nat.eq_of_beq_eq_true he]
  exact (prep_wordK (by norm_num) (by norm_num) hS hSI _ hl).1

@[expose] noncomputable def pa450010k0 : Perm (Fin 28) := pa450010wv false 2 pa450010wG5k

@[expose] noncomputable def pa450010z0 : Perm (Fin 28) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 2 => pa450010j h)
    (CFSG.Monster.B.Co2.toLetters 2 pa450010wG5z)

@[expose] noncomputable def pa450010g5 (i : ℕ) : Perm (Fin 28) :=
  [pa450010j 0, pa450010j 1, pa450010k0 * pa450010j 0 * pa450010k0⁻¹,
    pa450010k0 * pa450010j 1 * pa450010k0⁻¹].getD i 1

theorem pa450010_prepJ : (∀ j < 2, PRep 28 5 (pa450010J.G j) (pa450010j j)) ∧
    ∀ j < 2, PRep 28 5 (pa450010J.GI j) (pa450010j j)⁻¹ := by
  obtain ⟨-, -, -, -, -, -, hg, hgi⟩ := pa450010_J_rec
  exact ⟨hg, hgi⟩

theorem pa450010_prepZ : PRep 28 5 pa450010ZJ.R pa450010z0 :=
  pa450010_wordEq pa450010_prepJ.1 pa450010_prepJ.2 pa450010_G5_z

theorem pa450010_prepK : PRep 28 5 (pa450010G5K 0) pa450010k0 ∧
    PRep 28 5 (pa450010G5K 1) pa450010k0⁻¹ := by
  have h := pa450010_G5_k
  rw [bAnd_eq, Bool.and_eq_true] at h
  have hk : PRep 28 5 (pa450010G5K 0) pa450010k0 := pa450010_root (b := false) (by norm_num) h.1
  exact ⟨hk, CFSG.KC.OrbGroup.prep_inv hk h.2⟩

theorem pa450010_k0x : pa450010k0 * pa450010x * pa450010k0⁻¹ = pa450010x * pa450010z0 := by
  have hl := prep_pcomp (by norm_num) (prep_pcomp (by norm_num) pa450010_prepK.1 pa450010_prepX)
    pa450010_prepK.2
  have hr := prep_pcomp (by norm_num) pa450010_prepX pa450010_prepZ
  rw [Nat.eq_of_beq_eq_true pa450010_G5_kx] at hl
  exact CFSG.KC.OrbGroup.prep_eq hl hr

theorem pa450010_prepG5 : (∀ h < 4, PRep 28 5 (pa450010G5S h) (pa450010g5 h)) ∧
    ∀ h < 4, PRep 28 5 (pa450010G5SI h) (pa450010g5 h)⁻¹ := by
  have h := pa450010_G5_S
  simp only [bAnd_eq, Bool.and_eq_true] at h
  obtain ⟨h0, h1, h2, h3, hp⟩ := h
  obtain ⟨hJ, -⟩ := pa450010_prepJ
  have hS : ∀ h < 4, PRep 28 5 (pa450010G5S h) (pa450010g5 h) := by
    intro i hi
    interval_cases i
    · rw [Nat.eq_of_beq_eq_true h0]
      exact hJ 0 (by norm_num)
    · rw [Nat.eq_of_beq_eq_true h1]
      exact hJ 1 (by norm_num)
    · rw [Nat.eq_of_beq_eq_true h2]
      exact prep_pcomp (by norm_num) (prep_pcomp (by norm_num) pa450010_prepK.1
        (hJ 0 (by norm_num))) pa450010_prepK.2
    · rw [Nat.eq_of_beq_eq_true h3]
      exact prep_pcomp (by norm_num) (prep_pcomp (by norm_num) pa450010_prepK.1
        (hJ 1 (by norm_num))) pa450010_prepK.2
  exact ⟨hS, fun i hi => CFSG.KC.OrbGroup.prep_inv (hS i hi) (allN_iff.1 hp i hi)⟩

theorem pa450010_G5_0 : pa450010Jg ⊔ pa450010Jg.map (MulAut.conj pa450010k0).toMonoidHom = D28 := by
  have hk : pa450010k0 ∈ D28 := pa450010wv_memD false _
  have hJD : pa450010Jg ≤ D28 := pa450010_J_le_E.trans inf_le_left
  refine le_antisymm (sup_le hJD ?_) ?_
  · rintro _ ⟨g, hg, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact D28.mul_mem (D28.mul_mem hk (hJD hg)) (D28.inv_mem hk)
  · have hcl : closure (Set.range fun h : Fin 4 => pa450010g5 h) ≤
        pa450010Jg ⊔ pa450010Jg.map (MulAut.conj pa450010k0).toMonoidHom := by
      rw [closure_le]
      rintro _ ⟨⟨i, hi⟩, rfl⟩
      have hm : ∀ j < 2, pa450010k0 * pa450010j j * pa450010k0⁻¹ ∈
          pa450010Jg.map (MulAut.conj pa450010k0).toMonoidHom := fun j hj =>
        ⟨pa450010j j, pa450010_j_mem hj, by simp [MulAut.conj_apply]⟩
      interval_cases i
      · exact le_sup_left (a := pa450010Jg) (pa450010_j_mem (by norm_num))
      · exact le_sup_left (a := pa450010Jg) (pa450010_j_mem (by norm_num))
      · exact le_sup_right (b := pa450010Jg.map (MulAut.conj pa450010k0).toMonoidHom)
          (hm 0 (by norm_num))
      · exact le_sup_right (b := pa450010Jg.map (MulAut.conj pa450010k0).toMonoidHom)
          (hm 1 (by norm_num))
    have hab := pa450010_G5_ab
    rw [bAnd_eq, Bool.and_eq_true] at hab
    have hA := pa450010_wordEq pa450010_prepG5.1 pa450010_prepG5.2 hab.1
    have hB := pa450010_wordEq pa450010_prepG5.1 pa450010_prepG5.2 hab.2
    have hA' : PRep 28 5 (pa450010S1 0) pA := pa450010_prepS false 0 (by norm_num)
    have hB' : PRep 28 5 (pa450010S1 1) pB := pa450010_prepS false 1 (by norm_num)
    change closure ({pA, pB} : Set (Perm (Fin 28))) ≤ _
    rw [closure_le]
    rintro _ (rfl | rfl)
    · rw [CFSG.KC.OrbGroup.prep_eq hA' hA]
      exact hcl (Quiver.SchreierGraph.evalWord_mem_closure _ _)
    · rw [CFSG.KC.OrbGroup.prep_eq hB' hB]
      exact hcl (Quiver.SchreierGraph.evalWord_mem_closure _ _)

theorem pa450010_ZJ_class {z : Perm (Fin 28)} (hz : z ∈ pa450010Jg) (h1 : z ≠ 1)
    (h2 : z * z = 1) : ∃ h ∈ pa450010Jg, h * pa450010z0 * h⁻¹ = z := by
  obtain ⟨xJ, hxJ, hcan, -, hmem, -⟩ := pa450010_left (b := false) (by norm_num) pa450010_J_hd
    pa450010_J_sl
  obtain ⟨c, hc, -, -, hcls⟩ := pa450010_conj (b := false) (by norm_num) pa450010_prepZ
    pa450010_ZJ_hd pa450010_ZJ_sl
  obtain ⟨i, hi, rfl⟩ := (hmem _).1 hz
  have hTi := hxJ i hi
  have hid : PRep 28 5 (pidn 28 5) 1 := prep_pidn (by norm_num) (by norm_num)
  have hpc := prep_pcomp (by norm_num) hTi hTi
  rw [h2] at hpc
  have hshr : pa450010J.T i >>> (28 * 5) = 0 := (PF.canon_facts (hcan i hi)).2.2.1
  have hpshr := PF.pcomp_shr (n := 28) (w := 5) (pa450010J.T i) (pa450010J.T i) (by norm_num)
    (by norm_num)
  have hsq : pcomp 28 5 (mask 5) (pa450010J.T i) (pa450010J.T i) = pidn 28 5 :=
    CFSG.KC.OrbRow.eq_of_prep (by norm_num) hpc hid hpshr pa450010_pidn_shr
  have hne : pa450010J.T i ≠ pidn 28 5 := by
    intro e
    rw [e] at hTi
    exact h1 (CFSG.KC.OrbGroup.prep_eq hTi hid)
  obtain ⟨r, hr, hq, hrT⟩ := sqCoverK_spec pa450010_ZJ_cover i hi (Or.inl hsq) hne hne
  simp only [List.mem_singleton] at hr
  subst hr
  dsimp only at hq hrT
  have hcq := hc _ hq
  rw [hrT] at hcq
  rw [CFSG.KC.OrbGroup.prep_eq hTi hcq]
  exact (hcls _).2 ⟨_, hq, rfl⟩

theorem pa450010_G5 : ∀ z ∈ jOf D28 pa450010x, z ≠ 1 →
    z * z = 1 → ∃ k ∈ D28, k * pa450010x * k⁻¹ = pa450010x * z ∧
      jOf D28 pa450010x ⊔ (jOf D28 pa450010x).map (MulAut.conj k).toMonoidHom = D28 := by
  rw [pa450010_jOf_eq]
  intro z hz h1 h2
  obtain ⟨h, hh, rfl⟩ := pa450010_ZJ_class hz h1 h2
  have hJE := pa450010_J_le_E
  have hhD : h ∈ D28 := (hJE hh).1
  have hhx : h * pa450010x = pa450010x * h := mem_centralizer_singleton_iff.1 (hJE hh).2
  have hk : pa450010k0 ∈ D28 := pa450010wv_memD false _
  have hJn : ∀ j ∈ pa450010Jg, h * j * h⁻¹ ∈ pa450010Jg := fun j hj =>
    pa450010Jg.mul_mem (pa450010Jg.mul_mem hh hj) (pa450010Jg.inv_mem hh)
  refine ⟨h * pa450010k0 * h⁻¹, D28.mul_mem (D28.mul_mem hhD hk) (D28.inv_mem hhD), ?_, ?_⟩
  · have hx' : h⁻¹ * pa450010x * h = pa450010x := by
      rw [mul_assoc, ← hhx]
      group
    calc h * pa450010k0 * h⁻¹ * pa450010x * (h * pa450010k0 * h⁻¹)⁻¹ =
          h * (pa450010k0 * (h⁻¹ * pa450010x * h) * pa450010k0⁻¹) * h⁻¹ := by group
      _ = h * (pa450010x * pa450010z0) * h⁻¹ := by rw [hx', pa450010_k0x]
      _ = h * pa450010x * (pa450010z0 * h⁻¹) := by group
      _ = pa450010x * (h * pa450010z0 * h⁻¹) := by rw [hhx]; group
  · set k := h * pa450010k0 * h⁻¹ with hkdef
    have hkD : k ∈ D28 := D28.mul_mem (D28.mul_mem hhD hk) (D28.inv_mem hhD)
    have hJD : pa450010Jg ≤ D28 := hJE.trans inf_le_left
    refine le_antisymm (sup_le hJD ?_) ?_
    · rintro _ ⟨g, hg, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact D28.mul_mem (D28.mul_mem hkD (hJD hg)) (D28.inv_mem hkD)
    · have hle : pa450010Jg ⊔ pa450010Jg.map (MulAut.conj pa450010k0).toMonoidHom ≤
          (pa450010Jg ⊔ pa450010Jg.map (MulAut.conj k).toMonoidHom).comap
            (MulAut.conj h).toMonoidHom := by
        refine sup_le (fun j hj => ?_) ?_
        · simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact le_sup_left (a := pa450010Jg) (hJn j hj)
        · rintro _ ⟨j, hj, rfl⟩
          simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          refine le_sup_right (b := pa450010Jg.map (MulAut.conj k).toMonoidHom)
            ⟨h * j * h⁻¹, hJn j hj, ?_⟩
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hkdef]
          group
      rw [pa450010_G5_0] at hle
      intro d hd
      have hd' : h⁻¹ * d * h ∈ D28 :=
        D28.mul_mem (D28.mul_mem (D28.inv_mem hhD) hd) hhD
      have e := hle hd'
      simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
      have e2 : h * (h⁻¹ * d * h) * h⁻¹ = d := by group
      rwa [e2] at e

end CertificateChecks.KernelPropA

end
