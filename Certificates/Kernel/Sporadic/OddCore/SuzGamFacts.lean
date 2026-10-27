module

public import Certificates.Kernel.Sporadic.OddCore.SuzGam
public import CFSG.Sporadic.SuzOddCore.GammaBase
public import CFSG.Sporadic.SuzOddCore.GammaStab

public noncomputable section

namespace CertificateChecks.KernelSpor.OddCore.SGam

open CFSG.Sporadic.SuzOddCore
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native

theorem gammaAll_facts :
    adjOK 22880 #[certArr 0, certArr 1] gammaNbr (deltaOf zArr) = true ∧
    (∀ s < 4, (gammaMover s)[s]! = 0) ∧
    cellCount 22880 (gammaStage 1) (gammaStage 1)[1]! ≤ 8505 ∧
    cellCount 22880 (gammaStage 2) (gammaStage 2)[2]! ≤ 1152 ∧
    cellCount 22880 (gammaStage 3) (gammaStage 3)[3]! ≤ 4 ∧
    colInj 22880 (gammaStage 4) = true := by
  obtain ⟨h1, h⟩ := facts2294
  simp only [gammaStagesOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hm, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, fun s hs => beq_iff_eq.1 (allLt_spec hm hs), h2, h3, h4, h5⟩

theorem gammaNbr_facts : AdjFacts 22880 #[certArr 0, certArr 1] gammaNbr (deltaOf zArr) :=
  adjFacts_of_adjOK gammaAll_facts.1

theorem gammaNbr_inv
    {σ : Equiv.Perm (Fin 22880)} (hσ : σ ∈ suzP) : NbrInv gammaNbr σ :=
  gammaNbr_facts.inv_of_mem_closure (fun _ hk => rep_certPair hk) (suzP_eq_closure_gens ▸ hσ)

theorem gammaNbr_zero
    (i : Fin 22880) : (i : ℕ) ∈ gammaNbr[((0 : Fin 22880) : ℕ)]! ↔ i ∈ suzDeltaΩ := by
  rw [Fin.val_zero, gammaNbr_facts.root, mem_deltaOf]

theorem gammaNbr_symm
    {x y : Fin 22880} (h : (y : ℕ) ∈ gammaNbr[(x : ℕ)]!) :
    (x : ℕ) ∈ gammaNbr[(y : ℕ)]! := by
  obtain ⟨g, hg, hgx⟩ := suzP_exists_smul x 0
  have hinv := gammaNbr_inv hg
  have h1 := (hinv x y).1 h
  rw [hgx, Fin.val_zero] at h1
  have h2 := gammaNbr_facts.root_symm _ h1
  rw [hinv y x, hgx, Fin.val_zero]
  exact h2

theorem gammaNbr_adj
    (x y : Fin 22880) : (y : ℕ) ∈ gammaNbr[(x : ℕ)]! ↔ suzGamma.Adj x y := by
  rw [suzGamma_adj]
  constructor
  · intro h
    obtain ⟨g, hg, hgx⟩ := suzP_exists_smul 0 x
    have hinv := gammaNbr_inv (suzP.inv_mem hg)
    have h1 := (hinv x y).1 h
    have hx0 : g⁻¹ x = 0 := by rw [← hgx, perm_inv_apply_self]
    rw [hx0, gammaNbr_zero] at h1
    exact ⟨g, hg, g⁻¹ y, h1, Or.inl ⟨hgx, perm_apply_inv_self g y⟩⟩
  · rintro ⟨g, hg, i, hi, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ((gammaNbr_inv hg) 0 i).1 ((gammaNbr_zero i).2 hi)
    · exact gammaNbr_symm (((gammaNbr_inv hg) 0 i).1 ((gammaNbr_zero i).2 hi))

theorem suzGamma_adj_zero
    (i : Fin 22880) :
    suzGamma.Adj 0 i ↔ i ∈ suzDeltaΩ := by
  rw [← gammaNbr_adj, gammaNbr_zero]

theorem nbrInv_of_gammaAut
    (σ : suzGamma ≃g suzGamma) : NbrInv gammaNbr σ.toEquiv := by
  intro x y
  rw [gammaNbr_adj, gammaNbr_adj]
  exact σ.map_rel_iff.symm

theorem gammaE0_map {τ : Equiv.Perm (Fin 22880)}
    (hτ : NbrInv gammaNbr τ) (h0 : τ 0 = 0) : ColMap 22880 gammaE0 gammaE0 τ := by
  have h := colourT_map (fun x => gammaNbr_facts.point x) hτ rep_idA (by rw [mul_one, one_mul])
    (pre := [0]) (by simp) 2
  have e : permNat τ 0 = 0 := by
    rw [permNat_lt τ (by norm_num : 0 < 22880)]
    exact congrArg Fin.val h0
  simp only [List.map_cons, List.map_nil, e] at h
  exact h

theorem mover_map {s : ℕ}
    (hs : s < 4) {σ : Equiv.Perm (Fin 22880)} (hσ : NbrInv gammaNbr σ)
    (hfix : σ (gammaBasePt s) = gammaBasePt s) (v : Fin 22880) :
    gammaE0[(gammaMover s)[((σ v : Fin 22880) : ℕ)]!]! = gammaE0[(gammaMover s)[(v : ℕ)]!]! := by
  have hU : Rep 22880 (gammaMover s) (gammaWordPerm (gammaWords.getD s [])) :=
    rep_gammaWordArr _ (gammaWords_lt hs)
  set U := gammaWordPerm (gammaWords.getD s [])
  have hU0 : U (gammaBasePt s) = 0 := by
    have h := hU (gammaBasePt s)
    rw [gammaBasePt_val (by omega), gammaAll_facts.2.1 s hs] at h
    exact Fin.ext h.symm
  have hUi : U⁻¹ 0 = gammaBasePt s := by
    rw [← hU0, perm_inv_apply_self]
  have hUN : NbrInv gammaNbr U := gammaNbr_inv (gammaWordPerm_mem _)
  have hτ : NbrInv gammaNbr (U * σ * U⁻¹) :=
    AdjFacts.nbrInv_mul (AdjFacts.nbrInv_mul hUN hσ) (AdjFacts.nbrInv_inv hUN)
  have hτ0 : (U * σ * U⁻¹) 0 = 0 := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hUi, hfix, hU0]
  have e : U (σ v) = (U * σ * U⁻¹) (U v) := by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, perm_inv_apply_self]
  rw [hU (σ v), hU v, e]
  exact gammaE0_map hτ hτ0 (U v)

theorem gammaStage_map
    {σ : Equiv.Perm (Fin 22880)} (hσ : NbrInv gammaNbr σ) :
    ∀ s ≤ 4, (∀ j < s, σ (gammaBasePt j) = gammaBasePt j) →
      ColMap 22880 (gammaStage s) (gammaStage s) σ
  | 0, _, _ => fun v => by rw [gammaStage, replicate_getElem! (σ v).2, replicate_getElem! v.2]
  | s + 1, hs, hfix => by
    rw [gammaStage]
    exact refineT_map (fun x => gammaNbr_facts.point x) hσ rep_idA (by rw [mul_one, one_mul])
      (gammaBaseCol_map (gammaStage_map hσ s (by omega) fun j hj => hfix j (by omega))
        (mover_map (by omega) hσ (hfix s (by omega)))) _

theorem gammaCell_le {s : ℕ} (hs0 : 0 < s) (hs : s < 4) :
    cellCount 22880 (gammaStage s) (gammaStage s)[s]! ≤ gammaBounds s := by
  obtain ⟨-, -, h1, h2, h3, -⟩ := gammaAll_facts
  interval_cases s
  · exact h1
  · exact h2
  · exact h3

theorem gammaStab_orbit
    {s : ℕ} (hs : s < 4) :
    (MulAction.orbit (gammaStab s) (gammaBasePt s)).ncard ≤ gammaBounds s := by
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · refine (Set.ncard_le_card _).trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact le_rfl
  refine le_trans ?_ (gammaCell_le hpos hs)
  rw [cellCount_eq]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro _ ⟨⟨σ, hσ⟩, rfl⟩
  have hm := gammaStage_map (nbrInv_of_gammaAut σ) s (by omega) (mem_gammaStab.1 hσ)
    (gammaBasePt s)
  rw [gammaBasePt_val (by omega)] at hm
  exact hm

theorem gammaStab_four :
    gammaStab 4 = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  have hc := gammaStage_map (nbrInv_of_gammaAut σ) 4 le_rfl (mem_gammaStab.1 hσ)
  exact RelIso.ext fun v => colInj_injective gammaAll_facts.2.2.2.2.2 (hc v)

theorem gammaFacts :     (∀ i : Fin 22880, suzGamma.Adj 0 i ↔ i ∈ suzDeltaΩ) ∧
    (∀ s < 4, (MulAction.orbit (gammaStab s) (gammaBasePt s)).ncard ≤ gammaBounds s) ∧
    gammaStab 4 = ⊥ := by
  intros
  exact ⟨suzGamma_adj_zero, fun _ hs => gammaStab_orbit hs, gammaStab_four⟩

end CertificateChecks.KernelSpor.OddCore.SGam
