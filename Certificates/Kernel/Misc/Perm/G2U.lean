module

public import Certificates.Kernel.Misc.Perm.G2UK
public import CFSG.Certificates.Kernel.Misc.PermG2USound
public import CFSG.Quasithin.Background.G2UGroupsInputs

public section

namespace CertificateChecks.KernelMisc.G2U

open Matrix CFSG.KC.Misc.Clos CFSG.KC.Misc.G2U CFSG.Quasithin.G2U

theorem rtAll : ∀ i < 12096, treeAt m2 (rows2 id2) GR 4 RE RP i = true :=
  forall_of_chunks 1008 12 _ fun c hc => RTK.all c hc

theorem rsAll : ∀ i < 12096, sortAt 12096 RE RS i = true :=
  forall_of_chunks 1008 12 _ fun c hc => RSK.all c hc

theorem rcAll : ∀ i < 12096, closedAt m2 GR 4 12096 RE RC i = true :=
  forall_of_chunks 1008 12 _ fun c hc => RCK.all c hc

theorem dtAll : ∀ i < 6048, treeAt mP oneD GD 2 DE DP i = true :=
  forall_of_chunks 1008 6 _ fun c hc => DTK.all c hc

theorem dsAll : ∀ i < 6048, sortAt 6048 DE DS i = true :=
  forall_of_chunks 1008 6 _ fun c hc => DSK.all c hc

theorem dcAll : ∀ i < 6048, closedAt mP GD 2 6048 DE DC i = true :=
  forall_of_chunks 1008 6 _ fun c hc => DCK.all c hc

theorem dpAll : ∀ i < 6048, pairAt (rows2 id2) (codes9 id3) DE i = true :=
  forall_of_chunks 1008 6 _ fun c hc => DPK.all c hc

theorem canon_g : canon2 g0c = true ∧ canon2 g1c = true ∧ canon2 g2c = true ∧ canon2 g3c = true ∧
    canon2 id2 = true ∧ canon3 Ac = true ∧ canon3 Bc = true ∧ canon3 id3 = true ∧
    canon2 ac = true ∧ canon2 bc = true := by
  decide +kernel

theorem gr_codes : GR 0 = rows2 g0c ∧ GR 1 = rows2 g1c ∧ GR 2 = rows2 g2c ∧ GR 3 = rows2 g3c := by
  decide +kernel

theorem gd_codes : GD 0 = codes9 Ac + 2 ^ 36 * rows2 ac ∧ GD 1 = codes9 Bc + 2 ^ 36 * rows2 bc := by
  decide +kernel

theorem one2 : encG2 1 = rows2 id2 := by
  rw [encG2, Units.val_one, ← dec2_id2, encM2_dec2 canon_g.2.2.2.2.1]

theorem one9 : encG9 1 = codes9 id3 := by
  rw [encG9, Units.val_one, ← dec3_id3, encM9_dec3 canon_g.2.2.2.2.2.2.2.1]

theorem oneGP : encGP 1 = oneD := by
  change encG9 1 + 2 ^ 36 * encG2 1 = _
  rw [one9, one2]
  rfl

abbrev gensR' : List (GL (Fin 14) (ZMod 2)) := [gen0, gen1, gen2, gen3]

theorem hGR : ∀ j < gensR'.length, GR j = encG2 (gensR'.getD j 1) := by
  intro j hj
  have hj4 : j < 4 := hj
  interval_cases j
  · rw [gr_codes.1]
    exact (encM2_dec2 canon_g.1).symm
  · rw [gr_codes.2.1]
    exact (encM2_dec2 canon_g.2.1).symm
  · rw [gr_codes.2.2.1]
    exact (encM2_dec2 canon_g.2.2.1).symm
  · rw [gr_codes.2.2.2]
    exact (encM2_dec2 canon_g.2.2.2.1).symm

abbrev gensD' : List (GL (Fin 14) (ZMod 2) × GL (Fin 3) F9) := [(aU, AU), (bU, BU)]

theorem hGD : ∀ j < gensD'.length, GD j = encGP (gensD'.getD j 1) := by
  intro j hj
  have hj2 : j < 2 := hj
  interval_cases j
  · change _ = encM9 (dec3 Ac) + 2 ^ 36 * encM2 (aU : Matrix (Fin 14) (Fin 14) (ZMod 2))
    rw [coe_aU, encM9_dec3 canon_g.2.2.2.2.2.1, encM2_dec2 canon_g.2.2.2.2.2.2.2.2.1,
      gd_codes.1]
  · change _ = encM9 (dec3 Bc) + 2 ^ 36 * encM2 (bU : Matrix (Fin 14) (Fin 14) (ZMod 2))
    rw [coe_bU, encM9_dec3 canon_g.2.2.2.2.2.2.1, encM2_dec2 canon_g.2.2.2.2.2.2.2.2.2,
      gd_codes.2]

theorem R_eq : rootGroup = Subgroup.closure {g | g ∈ gensR'} := by
  rw [rootGroup]
  congr 1
  ext z
  simp

theorem D_eq : graphD = Subgroup.closure {g | g ∈ gensD'} := by
  rw [graphD]
  congr 1
  ext z
  simp

theorem cardR : Nat.card rootGroup = 12096 := by
  rw [R_eq]
  have ht : ∀ k < 12096, treeAt m2 (encG2 1) GR gensR'.length RE RP k = true := by
    rw [one2]
    exact rtAll
  exact ((clos_card enc2 gensR' hGR (by norm_num) ht rsAll).2.2 rcAll).1

abbrev Dg : Subgroup (GL (Fin 14) (ZMod 2) × GL (Fin 3) F9) := Subgroup.closure {g | g ∈ gensD'}

theorem closD : (∀ k < 6048, ∃ g ∈ Dg, encGP g = DE k) ∧ 6048 ≤ Nat.card Dg ∧
    ∀ {CT : Nat → Nat}, (∀ k < 6048, closedAt mP GD gensD'.length 6048 DE CT k = true) →
      Nat.card Dg = 6048 ∧ ∀ g ∈ Dg, ∃ k < 6048, encGP g = DE k := by
  have ht : ∀ k < 6048, treeAt mP (encGP 1) GD gensD'.length DE DP k = true := by
    rw [oneGP]
    exact dtAll
  exact clos_card encP gensD' hGD (by norm_num) ht dsAll

theorem pair_spec (E : Nat → Nat) (k : Nat) (h : pairAt (rows2 id2) (codes9 id3) E k = true) :
    Nat.shiftRight (E k) 36 = rows2 id2 ↔ fldN (E k) 0 36 = codes9 id3 := by
  unfold pairAt at h
  rw [letB_eq] at h
  generalize E k = c at h ⊢
  generalize rows2 id2 = I2 at h ⊢
  generalize codes9 id3 = I9 at h ⊢
  constructor
  · intro hB
    have h1 : Nat.beq (Nat.shiftRight c 36) I2 = true := by rw [hB]; exact Nat.beq_refl _
    rw [h1] at h
    exact Nat.eq_of_beq_eq_true h
  · intro h9
    by_contra hne
    have hf : Nat.beq (Nat.shiftRight c 36) I2 = false :=
      Bool.eq_false_iff.2 fun h' => hne (Nat.eq_of_beq_eq_true h')
    have ht : Nat.beq (fldN c 0 36) I9 = true := by rw [h9]; exact Nat.beq_refl _
    rw [hf, ht] at h
    exact absurd h (by decide)

theorem pair_fact (g : GL (Fin 14) (ZMod 2) × GL (Fin 3) F9) (hg : g ∈ graphD) :
    encG2 g.1 = rows2 id2 ↔ encG9 g.2 = codes9 id3 := by
  rw [D_eq] at hg
  obtain ⟨k, hk, hgk⟩ := (closD.2.2 dcAll).2 g hg
  have hs := pair_spec DE k (dpAll k hk)
  rwa [← hgk, encGP_hi, encGP_lo] at hs

open CFSG.Quasithin.G2U in
theorem facts : Nat.card rootGroup = 12096 ∧ Nat.card graphD = 6048 ∧
    (∀ g ∈ graphD, g.1 = 1 → g.2 = 1) ∧ (∀ g ∈ graphD, g.2 = 1 → g.1 = 1) := by
  refine ⟨cardR, ?_, fun g hg h1 => ?_, fun g hg h2 => ?_⟩
  · rw [D_eq]
    exact (closD.2.2 dcAll).1
  · have h9 : encG9 g.2 = encG9 1 := by
      rw [one9]
      exact (pair_fact g hg).1 (by rw [h1, one2])
    exact enc9.inj h9
  · have h2' : encG2 g.1 = encG2 1 := by
      rw [one2]
      exact (pair_fact g hg).2 (by rw [h2, one9])
    exact enc2.inj h2'

end CertificateChecks.KernelMisc.G2U

end
