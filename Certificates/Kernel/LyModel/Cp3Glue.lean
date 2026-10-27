
module

public import Certificates.Kernel.LyModel.Cp3Chk
public import Certificates.Kernel.LyModel.Cp3Inv0
public import Certificates.Kernel.LyModel.Cp3Inv1
public import Certificates.Kernel.LyModel.Cp3Inv2
public import Certificates.Kernel.LyModel.Cp3Inv3
public import Certificates.Kernel.LyModel.EltGlue
public import Certificates.Kernel.LyDce.CoverGlue
public import CFSG.Certificates.Kernel.LyModel.Cp3Sound

public section

namespace CertificateChecks.KernelLyModel

open Equiv Pointwise Subgroup CFSG.KC CFSG.KC.Benes CFSG.KC.YModel.Sem CFSG.KC.LyBenes
  CFSG.KC.LyModel CFSG.KC.LyDce CFSG.KC.LyBase CFSG.KC.LyGlue CFSG.KC.MonsterConv.Perm
  CertificateChecks.KernelLy CertificateChecks.KernelLyB CertificateChecks.KernelLyBase
  CertificateChecks.KernelLyDce CFSG.Sporadic.Recognition.LyonsSims
  CFSG.Sporadic.Recognition.LyonsSims.LyFinal

theorem nrep_Y : NRep 17 Ly0.deg NY0 Ly0.y0G := by
  rw [Ly0.y0G_def]
  exact nrep_word (fun z hz => nrep_z cL_eq_cG dL_eq_dG z (Ly0.decodeWord_mem _ z hz))
    (fun z hz => valid_all _ (zIdx_lt z (Ly0.decodeWord_mem _ z hz)))
    (stagesValid_of_netValid ly6110_cp3validY) ly6110_cp3netY

theorem fix_y0 : {x : Fin Ly0.deg | Ly0.y0G x = x} = O0 := by
  have hf := fixM_sound (stagesValid_of_netValid ly6110_cp3validY) ly6110_cp3fix
  ext x
  rw [Set.mem_setOf_eq, ← isMask_O0.mem x, hf x x.2, nrep_Y x, Fin.ext_iff]

theorem img_smul (g : Perm (Fin Ly0.deg)) (S : Set (Fin Ly0.deg)) : g '' S = g • S := by
  ext x
  simp only [Set.mem_image, Set.mem_smul_set, Perm.smul_def]

theorem img_fix (g : Perm (Fin Ly0.deg)) : g '' {x | Ly0.y0G x = x} = g • O0 := by
  rw [img_smul, fix_y0]

theorem smul_fix_eq {w y : Perm (Fin Ly0.deg)} (h : w * y = y * w) :
    y • {x | w x = x} = {x | w x = x} := by
  have h' : w * y⁻¹ = y⁻¹ * w := (Commute.inv_right (show Commute w y from h)).eq
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem, Perm.smul_def, Set.mem_setOf_eq, Set.mem_setOf_eq]
  have e : w (y⁻¹ x) = y⁻¹ (w x) := by rw [← Perm.mul_apply, h', Perm.mul_apply]
  rw [e]
  exact (y⁻¹).injective.eq_iff

theorem inv_chunks : ∀ i < 16, invChunk i = true := by
  intro i hi
  interval_cases i
  exacts [ly6110inv0, ly6110inv1, ly6110inv2, ly6110inv3, ly6110inv4, ly6110inv5, ly6110inv6,
    ly6110inv7, ly6110inv8, ly6110inv9, ly6110inv10, ly6110inv11, ly6110inv12, ly6110inv13,
    ly6110inv14, ly6110inv15]

theorem inv_label {l : Nat} (hl : l < nL) :
    l = root ∨ cm.testBit l = true ∨ mvC tc td yC l ≠ l := by
  have hl' : l < 15400 := hl
  have hc := inv_chunks (l / 1000) (by omega)
  have hc' : invWith cm (l / 1000) = true := by
    have e : invChunk (l / 1000) = invWith cm (l / 1000) := strictBN_eq _ _
    rw [← e]
    exact hc
  have h := allFrom_sound hc' (l % 1000) (Nat.mod_lt _ (by norm_num))
  have e : Nat.mul 1000 (l / 1000) + l % 1000 = l := Nat.div_add_mod l 1000
  rw [e] at h
  exact invAt_sound h hl

theorem orb_parts : Nat.beq (mvC tc td gC root) l0 = true ∧ orbOK tc td uC ents [l0] = true :=
  cp3_andB ly6110_cp3orb

theorem cdW_u {j : Nat} (hj : j < 4) : CdW (Ly0.uWords.getD j []) := by
  intro z hz
  interval_cases j
  · exact Ly0.decodeWord_mem _ z hz
  · exact Ly0.decodeWord_mem _ z hz
  · exact Ly0.decodeWord_mem _ z hz
  · exact Ly0.decodeWord_mem _ z hz

theorem uC_getD (j : Nat) : uC.getD j [] = (Ly0.uWords.getD j []).map lcode := by
  rw [ly6110_cp3uC, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (Ly0.uWords)[j]? <;> rfl

section

variable (hbc : RB5Bound)
include hbc

theorem mv_word (w : List ℤ) (hw : CdW w) {l : Nat} (hl : l < nL) :
    mvC tc td (w.map lcode) l < nL ∧ Lf (mvC tc td (w.map lcode) l) = Ly0.wG Ly0.gens0 w • Lf l :=
  Lf_mvC cL_eq_cG dL_eq_dG hbc w hw hl

omit hbc in
theorem Lf_inj {l l' : Nat} (hl : l < nL) (hl' : l' < nL) (e : Lf l = Lf l') : l = l' := by
  have h := L_inj cL_eq_cG dL_eq_dG (a₁ := ⟨l, hl⟩) (a₂ := ⟨l', hl'⟩)
    (by rw [L_eq, L_eq]; exact e)
  exact congrArg Fin.val h

theorem orb_lines : ∀ l ∈ l0 :: ents.map Prod.fst,
    l < nL ∧ ∃ u ∈ Ly0.UYperm, Lf l = u • Lf l0 := by
  have hroot : root < nL := cov_parts.2.2.2
  have hl0 : l0 < nL := by
    have e := Nat.eq_of_beq_eq_true orb_parts.1
    rw [← e, ly6110_cp3gC]
    exact (mv_word hbc Ly0.wordConj (cdW_dec _) hroot).1
  have hQ : ∀ j < 4, ∀ p, (p < nL ∧ ∃ u ∈ Ly0.UYperm, Lf p = u • Lf l0) →
      (mvC tc td (uC.getD j []) p < nL ∧
        ∃ u ∈ Ly0.UYperm, Lf (mvC tc td (uC.getD j []) p) = u • Lf l0) := by
    rintro j hj p ⟨hp, u, hu, e⟩
    rw [uC_getD]
    have hm := mv_word hbc _ (cdW_u hj) hp
    refine ⟨hm.1, Ly0.uG j * u, mul_mem (subset_closure ⟨⟨j, hj⟩, rfl⟩) hu, ?_⟩
    rw [hm.2, e, ← Ly0.uG_def, mul_smul]
  have h := orbOK_sound hQ (R := [l0]) (fun p hp => by
    rw [List.mem_singleton.1 hp]
    exact ⟨hl0, 1, one_mem _, by rw [one_smul]⟩) orb_parts.2
  intro l hl
  rcases List.mem_cons.1 hl with rfl | hl
  · exact ⟨hl0, 1, one_mem _, by rw [one_smul]⟩
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hl
    exact h e he

theorem Lf_l0 : Lf l0 = Ly0.gcG • O0 := by
  have e := Nat.eq_of_beq_eq_true orb_parts.1
  rw [← e, ly6110_cp3gC, (mv_word hbc Ly0.wordConj (cdW_dec _) cov_parts.2.2.2).2,
    Lf_root cL_eq_cG dL_eq_dG hbc, ← Ly0.gcG_def]

theorem cp3Fact_true : Ly0.Cp3Fact := by
  unfold Ly0.Cp3Fact
  intro hB hN g hg w hw hcomm hne1 hne2
  have hc := cL_eq_cG
  have hd := dL_eq_dG
  have ht := tabCheck_true
  have hs := structCheck_true hbc
  have hc1 := cp1Check_true hbc
  have hcard : (Set.range L).ncard *
      Nat.card ↥(Ly0.B0 ⊓ normalizer (zpowers Ly0.y0G : Set (Perm (Fin Ly0.deg)))) =
        Nat.card Ly0.B0 := by
    rw [Set.ncard_range_of_injective (L_inj hc hd), Nat.card_eq_fintype_card, Fintype.card_fin,
      hN, hB]
    rfl
  have hcov : ∀ S ∈ Set.range L, ∃ a ∈ Ly0.B0, S = a '' {x | Ly0.y0G x = x} := by
    rintro S ⟨i, rfl⟩
    obtain ⟨a, ha, e⟩ := (Lf_spec hc hd i.2).1
    exact ⟨a, ha, by rw [img_fix, L_eq]; exact e⟩
  have hmem : ∀ a ∈ Ly0.B0, a '' {x | Ly0.y0G x = x} ∈ Set.range L := by
    intro a ha
    obtain ⟨i, hi⟩ := (lines hc hd hbc).1 a ha
    exact ⟨i, by rw [img_fix, hi]⟩
  have conj_eq : ∀ a ∈ Ly0.B0, ∀ b ∈ Ly0.B0, a • O0 = b • O0 →
      b * Ly0.y0G * b⁻¹ = a * Ly0.y0G * a⁻¹ ∨ b * Ly0.y0G * b⁻¹ = (a * Ly0.y0G * a⁻¹)⁻¹ := by
    intro a ha b hb he
    rw [← img_fix, ← img_fix] at he
    have hn := inv_mul_mem_normalizer_of_image_eq Ly0.B0 Ly0.y0G (Set.range L) hcov hmem
      hcard ha hb he
    rcases Ly0.conj_y0G_of_mem_normalizer ht hs hc1 hn with e | e
    · left
      calc b * Ly0.y0G * b⁻¹ = a * ((a⁻¹ * b) * Ly0.y0G * (a⁻¹ * b)⁻¹) * a⁻¹ := by group
        _ = a * Ly0.y0G * a⁻¹ := by rw [e]
    · right
      calc b * Ly0.y0G * b⁻¹ = a * ((a⁻¹ * b) * Ly0.y0G * (a⁻¹ * b)⁻¹) * a⁻¹ := by group
        _ = (a * Ly0.y0G * a⁻¹)⁻¹ := by rw [e]; group
  obtain ⟨i, hi⟩ := (lines hc hd hbc).1 g hg
  rw [L_eq] at hi
  have hfw : {x | w x = x} = g • O0 := by rw [hw, Ly0.fix_conj, img_fix]
  have hinv : Ly0.y0G • Lf i = Lf i := by
    rw [← hi, ← hfw]
    exact smul_fix_eq hcomm
  have hmv : mvC tc td (Ly0.wordY.map lcode) i = i := by
    have hm := mv_word hbc Ly0.wordY (cdW_dec _) i.2
    rw [← Ly0.y0G_def, hinv] at hm
    exact Lf_inj hm.1 i.2 hm.2
  rcases inv_label i.2 with h0 | hC | hY
  · exfalso
    have e : g • O0 = (1 : Perm (Fin Ly0.deg)) • O0 := by
      rw [hi, h0, Lf_root hc hd hbc, one_smul]
    have hwi := conj_eq g hg 1 Ly0.B0.one_mem e
    rw [← hw] at hwi
    simp only [one_mul, inv_one, mul_one] at hwi
    rcases hwi with e | e
    · exact hne1 e.symm
    · exact hne2 (by rw [e, inv_inv])
  · rw [cm, testBit_maskOf, decide_eq_true_iff] at hC
    obtain ⟨-, u, hu, hue⟩ := orb_lines hbc _ hC
    have hie2 : g • O0 = (u * Ly0.gcG) • O0 := by
      rw [hi, hue, Lf_l0 hbc, mul_smul]
    have hugc : u * Ly0.gcG ∈ Ly0.B0 := mul_mem (Ly0.UYperm_le_B0 hu) Ly0.gcG_mem_B0
    have hres := conj_eq g hg _ hugc hie2
    have hw0 : u * Ly0.w0G * u⁻¹ = ((u * Ly0.gcG) * Ly0.y0G * (u * Ly0.gcG)⁻¹)⁻¹ := by
      rw [Ly0.w0G_eq]; group
    refine ⟨u⁻¹, inv_mem hu, ?_⟩
    rw [← hw] at hres
    rcases hres with e | e
    · right
      have this : u * Ly0.w0G * u⁻¹ = w⁻¹ := by rw [hw0, e]
      have hw' : w = (u * Ly0.w0G * u⁻¹)⁻¹ := by rw [this, inv_inv]
      calc u⁻¹ * w * u⁻¹⁻¹ = u⁻¹ * (u * Ly0.w0G * u⁻¹)⁻¹ * u⁻¹⁻¹ := by rw [← hw']
        _ = Ly0.w0G⁻¹ := by group
    · left
      have this : u * Ly0.w0G * u⁻¹ = w := by rw [hw0, e, inv_inv]
      calc u⁻¹ * w * u⁻¹⁻¹ = u⁻¹ * (u * Ly0.w0G * u⁻¹) * u⁻¹⁻¹ := by rw [this]
        _ = Ly0.w0G := by group
  · rw [ly6110_cp3yC] at hY
    exact absurd hmv hY

end

end CertificateChecks.KernelLyModel

end
