
module

public import Certificates.Kernel.Fi23Q.SylowGlue
public import Certificates.Kernel.Fi23Q.FixDefs
import Certificates.Kernel.Fi23Q.FixChk
import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

namespace CertificateChecks.KernelFi23Q

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.KC.Fi23K CFSG.KC.Fi23Q CFSG.KC.Pc3 CFSG.KD.Fi23K
  CFSG.Perm
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance (Fi23ThreeTranspositionFixed D23_conj)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 (zJ t3)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow (qG)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem exists_sylow_le_centralizer_zJ :
    ∃ P : Sylow 3 CFSG.Sporadic.Fi23.J, (P : Subgroup CFSG.Sporadic.Fi23.J) ≤ Subgroup.centralizer {zJ} := by
  obtain ⟨P, hP⟩ := exists_sylow_Q
  refine ⟨P, ?_⟩
  rw [hP, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.2 (z_comm hj).symm

theorem three_classes_J :
    (∀ s : CFSG.Sporadic.Fi23.J, orderOf s = 3 → ∃ c : Fin 4, IsConj s (t3 c)) ∧
      (∃ P : Sylow 3 CFSG.Sporadic.Fi23.J, (P : Subgroup CFSG.Sporadic.Fi23.J) ≤ Subgroup.centralizer {zJ}) ∧
      IsConj d (CFSG.Sporadic.Bridge.Fi23.img 2) :=
  ⟨fun _ hs => orderOf_three_J hs, exists_sylow_le_centralizer_zJ, t2_isConj_d⟩

theorem t3_fixed
    (c : Fin 4) :
    ∃ e ∈ D23, e * t3 c = t3 c * e := by
  have hk := CFSG.KD.Fi23Q.fixK_ok
  unfold CFSG.KD.Fi23Q.fixK at hk
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true] at hk
  obtain ⟨h0, h1, h2, h3⟩ := hk
  obtain ⟨x, hx, hf⟩ : ∃ x, ∃ hx : x < 31671, CFSG.KD.Fi23Q.fixB c.val x = true := by
    fin_cases c
    · exact ⟨106, by norm_num, h0⟩
    · exact ⟨216, by norm_num, h1⟩
    · exact ⟨544, by norm_num, h2⟩
    · exact ⟨8, by norm_num, h3⟩
  unfold CFSG.KD.Fi23Q.fixB at hf
  simp only [CFSG.KS.PK.bAnd_eq, Bool.and_eq_true, Nat.beq_eq_true_eq, Nat.blt_eq] at hf
  have hw := wvG_eq _ (t3R_ok c.isLt) x hx
  rw [t3R_prod c.isLt, Nat.eq_of_beq_eq_true hf.2, idx_of_lt _ hx] at hw
  have hfx : t3 c • (⟨x, hx⟩ : Fin 31671) = ⟨x, hx⟩ := Fin.ext hw.symm
  have hc : t3 c * conjPt x * (t3 c)⁻¹ = conjPt x := (smul_eq_iff _ ⟨x, hx⟩ ⟨x, hx⟩).1 hfx
  refine ⟨conjPt x, (isConj_d_iff _).2 ⟨⟨x, hx⟩, rfl⟩, ?_⟩
  calc conjPt x * t3 c = t3 c * conjPt x * (t3 c)⁻¹ * t3 c := by rw [hc]
    _ = t3 c * conjPt x := by group

theorem three_transposition_fixed :
    Fi23ThreeTranspositionFixed := by
  intro s hs
  obtain ⟨c, hc⟩ := orderOf_three_J hs
  obtain ⟨g, hg⟩ := isConj_iff.1 hc
  obtain ⟨e, he, hec⟩ := t3_fixed c
  refine ⟨g⁻¹ * e * g, by simpa using D23_conj he g⁻¹, ?_⟩
  rw [← hg] at hec
  calc g⁻¹ * e * g * s = g⁻¹ * (e * (g * s * g⁻¹)) * g := by group
    _ = g⁻¹ * (g * s * g⁻¹ * e) * g := by rw [hec]
    _ = s * (g⁻¹ * e * g) := by group

end CertificateChecks.KernelFi23Q

end
