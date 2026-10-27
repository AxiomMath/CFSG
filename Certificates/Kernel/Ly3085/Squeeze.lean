
module

public import Certificates.Kernel.Ly3085.SqueezeBase

public import Certificates.Kernel.Ly3085.O1Count
public import Certificates.Kernel.Ly3085.O2Count
public import Certificates.Kernel.Ly3085.O34Count
public import Certificates.Kernel.Ly3085.Facts

public noncomputable section

namespace CertificateChecks.KernelLy.Omega

open CFSG.Sporadic.Ly CFSG.Sporadic.LySchreier CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.Ly.Omega CFSG.KS.LyOm CFSG.KC.LyOm CFSG.KC.LL
open CertificateChecks.KernelSporSch
open Matrix MulAction

open Classical in
theorem F1_all
    [LySeed] :
    (stabilizer J opE = lyH ∧ Nat.card lyH = 5859000000 ∧ Nat.card (orbit J opE) = 8835156) ∧
      ((Finset.univ.biUnion subO : Finset LyOperator) : Set LyOperator) = orbit J opE ∧
      (Pairwise fun i j => Disjoint (subO i) (subO j)) ∧
      Nat.card (orbit lyH opE) = 1 ∧ Nat.card (orbit lyH (gRep 1 • opE)) = 19530 ∧
      Nat.card (orbit lyH (gRep 2 • opE)) = 968750 ∧
      Nat.card (orbit lyH (gRep 3 • opE)) = 2034375 ∧
      Nat.card (orbit lyH (gRep 4 • opE)) = 5812500 := by
  classical
  obtain ⟨z1, u2, n3, s3, u4, d24⟩ := beta_facts
  have r1 := beta_rep1
  have r2 := beta_rep2
  have r3 := beta_rep3
  have r4 := beta_rep4
  have c1 := card_orbit_o1
  have c2 := card_orbit_o2
  have c3 := card_orbit_o3
  have c4 := card_orbit_o4
  have hne : ∀ c : J, 2 ≤ Nat.card (orbit lyH (c • opE)) → ∀ g : lyH, g • opE ≠ c • opE := by
    intro c hc g e
    rw [orbit_opE] at e
    have h1 : orbit lyH (c • opE) = {opE} := by
      rw [← e]
      ext x
      constructor
      · rintro ⟨g', rfl⟩
        exact orbit_opE g'
      · rintro rfl
        exact mem_orbit_self _
    rw [h1, Nat.card_unique] at hc
    omega
  have hd : Pairwise fun i j => Disjoint (subO i) (subO j) := by
    have key : ∀ i j : Fin 5, i < j → Disjoint (subO i) (subO j) := by
      intro i j hij
      unfold subO
      apply disjoint_orbits
      fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | skip
      all_goals simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, repOp_zero]
      all_goals first
        | rw [repOp_pos (by decide)]
        | skip
      all_goals first
        | rw [repOp_pos (by decide)]
        | skip
      · exact hne _ (by omega)
      · exact hne _ (by omega)
      · exact hne _ (by omega)
      · exact hne _ (by omega)
      · exact sep_of_beta fun g e => by
          rw [r1, z1, form_zero, r2] at e
          have := u2
          rw [← e] at this
          simp at this
      · exact sep_of_beta fun g e => by
          rw [r1, z1, form_zero, r3] at e
          exact n3 e.symm
      · exact sep_of_beta fun g e => by
          rw [r1, z1, form_zero, r4] at e
          have := u4
          rw [← e] at this
          simp at this
      · exact sep_of_beta fun g e => by
          rw [r2, beta2_fixed, r3] at e
          exact s3 (e ▸ u2)
      · exact sep_of_beta fun g e => by
          rw [r2, beta2_fixed, r4] at e
          exact d24 e
      · exact sep_of_beta fun g e => by
          rw [r3, r4] at e
          exact s3 ((form_unit g (fm CFSG.KD.LyOm.BE3)).1 (by rw [e]; exact u4))
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · exact (key j i h).symm
  have hsum : 8835156 ≤ ∑ i, (subO i).card := by
    rw [Fin.sum_univ_five, card_subO, card_subO, card_subO, card_subO, card_subO]
    have : Nonempty (orbit lyH (repOp 0)) := ⟨⟨_, mem_orbit_self _⟩⟩
    have : Finite (orbit lyH (repOp 0)) := Set.finite_coe_iff.2 (Set.toFinite _)
    have h0 : 1 ≤ Nat.card (orbit lyH (repOp 0)) := Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne'
    have e1 : repOp (1 : Fin 5).val = gRep 1 • opE := repOp_pos (by decide)
    have e2 : repOp (2 : Fin 5).val = gRep 2 • opE := repOp_pos (by decide)
    have e3 : repOp (3 : Fin 5).val = gRep 3 • opE := repOp_pos (by decide)
    have e4 : repOp (4 : Fin 5).val = gRep 4 • opE := repOp_pos (by decide)
    rw [e1, e2, e3, e4]
    change 8835156 ≤ Nat.card (orbit lyH (repOp 0)) + _ + _ + _ + _
    omega
  have hO : ∀ i, (subO i : Set LyOperator) ⊆ orbit J opE := by
    intro i x hx
    rw [subO, Set.Finite.coe_toFinset] at hx
    obtain ⟨g, rfl⟩ := hx
    by_cases hi : i.val = 0
    · rw [hi, repOp_zero]
      exact ⟨g, rfl⟩
    · rw [repOp_pos hi]
      refine ⟨(g : J) * gRep i.val, ?_⟩
      change ((g : J) * gRep i.val) • opE = (g : J) • gRep i.val • opE
      rw [mul_smul]
  have hJ : Nat.card J = 8835156 * 5859000000 := by rw [card_J_S]
  obtain ⟨h1, h2, h3, h4, h5⟩ := squeeze opE lyH lyH_le_stab hJ card_lyH_ge (by norm_num) subO hO
    hd hsum
  have h0 : Nat.card (orbit lyH opE) = 1 := by
    rw [orbit_opE_eq, Nat.card_unique]
  have e1 : repOp (1 : Fin 5).val = gRep 1 • opE := repOp_pos (by decide)
  have e2 : repOp (2 : Fin 5).val = gRep 2 • opE := repOp_pos (by decide)
  have e3 : repOp (3 : Fin 5).val = gRep 3 • opE := repOp_pos (by decide)
  have e4 : repOp (4 : Fin 5).val = gRep 4 • opE := repOp_pos (by decide)
  rw [Fin.sum_univ_five, card_subO, card_subO, card_subO, card_subO, card_subO, e1, e2, e3, e4]
    at h4
  change Nat.card (orbit lyH (repOp 0)) + _ + _ + _ + _ = 8835156 at h4
  rw [repOp_zero, h0] at h4
  refine ⟨⟨h1, h2, h3⟩, h5, hd, h0, ?_, ?_, ?_, ?_⟩ <;> omega

theorem F1
    [LySeed] :
    stabilizer J opE = lyH ∧ Nat.card lyH = 5859000000 ∧ Nat.card (orbit J opE) = 8835156 :=
  F1_all.1

end CertificateChecks.KernelLy.Omega

end
