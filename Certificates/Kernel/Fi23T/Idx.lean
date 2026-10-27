module

public import Certificates.Kernel.Fi23T.Sets
public import CFSG.Certificates.Kernel.Fi23Tr.TrBFS
public import CFSG.Certificates.Kernel.Fi23Tr.Conj
public import CFSG.Certificates.Kernel.Fi23Tr.Loops
public import Certificates.Kernel.Fi23T.Orbit

public section

set_option maxRecDepth 400000

open Pointwise

namespace CertificateChecks.KernelFi23T

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23T CFSG.KC.Fi23C CFSG.KD.Fi23K CFSG.KD.Fi23T
  CFSG.KS.Fi23Tr CertificateChecks.KernelFi23M
open CFSG.Sporadic.Fi23.Native (trData cData tauAct dTable genTables PBits pBit pOf pZero pImg TrOrb
  trBFS trAct trD trBi dWord mkRowInv trIsFar)
open CFSG.Sporadic.Th.Native (ap Table none32)
open CFSG.Sporadic.Th (Rep idx_of_lt)
open CertificateChecks.KernelFi23C (cp cp_zero cp_step labW rep_alpha rep_beta acts_dWord7)

noncomputable abbrev orb : TrOrb :=
  trBFS (pZero ()) orbLit.alpha orbLit.beta (pOf (pZero ()) (trData ())) 200000

noncomputable abbrev vS (k : ℕ) : Finset (Fin 31671) := toF orb.sets[k]!

noncomputable abbrev tA (k m : ℕ) : ℕ := trAct orbLit orb (trD orb) (trBi orb) k m

noncomputable abbrev RI : Table :=
  mkRowInv orbLit orb (trD orb) (trBi orb) (pOf (pZero ()) (trData ()))

theorem orb_facts : 0 < orb.sets.size ∧ orb.sets[0]! = pOf (pZero ()) (trData ()) ∧
    orb.par.size = orb.sets.size ∧ orb.lab.size = orb.sets.size ∧
    (∀ i < orb.sets.size, ∀ j < orb.sets.size, orb.sets[i]! = orb.sets[j]! → i = j) ∧
    (∀ k < orb.sets.size, orb.tbl.get? orb.sets[k]! = some k) ∧
    (∀ B : PBits, (∀ k < orb.sets.size, orb.sets[k]! ≠ B) → orb.tbl.get? B = none) ∧
    (∀ k, 0 < k → k < orb.sets.size → ap orb.par k < k ∧
      ((ap orb.lab k = 1 ∧ orb.sets[k]! = pImg (pZero ()) orbLit.alpha orb.sets[ap orb.par k]!) ∨
        (ap orb.lab k = 2 ∧ orb.sets[k]! = pImg (pZero ()) orbLit.beta orb.sets[ap orb.par k]!))) ∧
    (orb.sets.size ≤ 200000 → orb.pa.size = orb.sets.size ∧ orb.pb.size = orb.sets.size ∧
      ∀ k < orb.sets.size, ap orb.pa k < orb.sets.size ∧
        pImg (pZero ()) orbLit.alpha orb.sets[k]! = orb.sets[ap orb.pa k]! ∧
        ap orb.pb k < orb.sets.size ∧
        pImg (pZero ()) orbLit.beta orb.sets[k]! = orb.sets[ap orb.pb k]!) :=
  trBFS_spec _ _ _ _ _ (by norm_num)

noncomputable def cc (k : ℕ) : Equiv.Perm (Fin 31671) :=
  if h : 0 < k ∧ ap orbLit.par k < k then
    (if ap orbLit.lab k = 1 then phiX wα else phiX wβ) * cc (ap orbLit.par k) *
      (if ap orbLit.lab k = 1 then phiX wα else phiX wβ)⁻¹
  else dEl (phiX wα) (phiX wβ)
termination_by k
decreasing_by exact h.2

theorem cc_eq (k : ℕ) : cc k = if 0 < k ∧ ap orbLit.par k < k then
    (if ap orbLit.lab k = 1 then phiX wα else phiX wβ) * cc (ap orbLit.par k) *
      (if ap orbLit.lab k = 1 then phiX wα else phiX wβ)⁻¹
    else dEl (phiX wα) (phiX wβ) := by
  rw [cc]
  exact dite_eq_ite

section


theorem vtx_smul {g : Equiv.Perm (Fin 31671)} (hg : g ∈ A0) {V : Finset (Fin 31671)}
    (hV : V ∈ cfg.Vtx) : g • V ∈ cfg.Vtx := by
  obtain ⟨h, hh, rfl⟩ := hV
  exact ⟨g * h, mul_mem hg hh, mul_smul _ _ _⟩

theorem T0_vtx : T0 ∈ cfg.Vtx := ⟨1, one_mem _, one_smul _ _⟩

theorem sets_ok : ∀ k < orb.sets.size, Canon orb.sets[k]! ∧ vS k ∈ cfg.Vtx := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases h0 : k = 0
    · subst h0
      rw [vS, orb_facts.2.1, toF_tB]
      exact ⟨canon_tB, T0_vtx⟩
    · obtain ⟨hp, hl⟩ := orb_facts.2.2.2.2.2.2.2.1 k (Nat.pos_of_ne_zero h0) hk
      obtain ⟨hc, hv⟩ := ih _ hp (by omega)
      rcases hl with ⟨-, e⟩ | ⟨-, e⟩
      · obtain ⟨h1, h2⟩ := toF_pImg rep_alpha alpha_out hc
        rw [vS, e, h2]
        exact ⟨e ▸ h1, vtx_smul alpha_mem hv⟩
      · obtain ⟨h1, h2⟩ := toF_pImg rep_beta beta_out hc
        rw [vS, e, h2]
        exact ⟨e ▸ h1, vtx_smul beta_mem hv⟩

theorem vS_inj0 {i j : ℕ} (hi : i < orb.sets.size) (hj : j < orb.sets.size) (h : vS i = vS j) :
    i = j :=
  orb_facts.2.2.2.2.1 i hi j hj (toF_inj (sets_ok i hi).1 (sets_ok j hj).1 h)

theorem image_sub : (((Finset.range orb.sets.size).image vS : Finset (Finset (Fin 31671))) :
    Set (Finset (Fin 31671))) ⊆ cfg.Vtx := by
  intro V hV
  rw [Finset.coe_image] at hV
  obtain ⟨k, hk, rfl⟩ := hV
  exact (sets_ok k (Finset.mem_range.1 (Finset.mem_coe.1 hk))).2

theorem image_card : ((Finset.range orb.sets.size).image vS).card = orb.sets.size := by
  rw [Finset.card_image_of_injOn (fun i hi j hj e => vS_inj0 (Finset.mem_range.1 (Finset.mem_coe.1 hi))
    (Finset.mem_range.1 (Finset.mem_coe.1 hj)) e), Finset.card_range]

theorem size_le : orb.sets.size ≤ 137632 := by
  have h := Set.ncard_le_ncard image_sub (Set.toFinite _)
  rw [Set.ncard_coe_finset, image_card, card_orbit] at h
  exact h

theorem closed : orb.pa.size = orb.sets.size ∧ orb.pb.size = orb.sets.size ∧
    ∀ k < orb.sets.size, ap orb.pa k < orb.sets.size ∧
      pImg (pZero ()) orbLit.alpha orb.sets[k]! = orb.sets[ap orb.pa k]! ∧
      ap orb.pb k < orb.sets.size ∧
      pImg (pZero ()) orbLit.beta orb.sets[k]! = orb.sets[ap orb.pb k]! :=
  orb_facts.2.2.2.2.2.2.2.2 (size_le.trans (by norm_num))

theorem pa_vS : ∀ k < orb.sets.size, ap orb.pa k < orb.sets.size ∧ vS (ap orb.pa k) = phiX wα • vS k := by
  intro k hk
  obtain ⟨h1, h2, -⟩ := closed.2.2 k hk
  refine ⟨h1, ?_⟩
  rw [vS, ← h2, (toF_pImg rep_alpha alpha_out (sets_ok k hk).1).2]

theorem pb_vS : ∀ k < orb.sets.size, ap orb.pb k < orb.sets.size ∧ vS (ap orb.pb k) = phiX wβ • vS k := by
  intro k hk
  obtain ⟨-, -, h1, h2⟩ := closed.2.2 k hk
  refine ⟨h1, ?_⟩
  rw [vS, ← h2, (toF_pImg rep_beta beta_out (sets_ok k hk).1).2]

theorem vS_zero : vS 0 = T0 := by rw [vS, orb_facts.2.1, toF_tB]

theorem vS_surj0 {V : Finset (Fin 31671)} (hV : V ∈ cfg.Vtx) : ∃ k < orb.sets.size, vS k = V := by
  obtain ⟨g, hg, rfl⟩ := hV
  have hT : cfg.T ∈ {V : Finset (Fin 31671) | ∃ k < orb.sets.size, vS k = V} :=
    ⟨0, orb_facts.1, vS_zero⟩
  have hX : ∀ γ ∈ cfg.Gab, ∀ V ∈ {V : Finset (Fin 31671) | ∃ k < orb.sets.size, vS k = V},
      γ • V ∈ {V : Finset (Fin 31671) | ∃ k < orb.sets.size, vS k = V} := by
    rintro γ (rfl | rfl) V ⟨k, hk, rfl⟩
    · obtain ⟨h1, h2⟩ := pa_vS k hk
      exact ⟨_, h1, h2⟩
    · obtain ⟨h1, h2⟩ := pb_vS k hk
      exact ⟨_, h1, h2⟩
  have hg' : g ∈ Subgroup.closure cfg.Gab := by
    rw [cfg_ok.hGab]
    exact hg
  exact orbit_sub hT hX g hg'

theorem size_eq : orb.sets.size = 137632 := by
  have he : (((Finset.range orb.sets.size).image vS : Finset (Finset (Fin 31671))) :
      Set (Finset (Fin 31671))) = cfg.Vtx := by
    refine Set.Subset.antisymm image_sub fun V hV => ?_
    obtain ⟨k, hk, rfl⟩ := vS_surj0 hV
    rw [Finset.coe_image]
    exact ⟨k, Finset.mem_coe.2 (Finset.mem_range.2 hk), rfl⟩
  have h := congrArg Set.ncard he
  rw [Set.ncard_coe_finset, image_card, card_orbit] at h
  exact h

theorem vS_inj {i j : ℕ} (hi : i < 137632) (hj : j < 137632) (h : vS i = vS j) : i = j :=
  vS_inj0 (size_eq ▸ hi) (size_eq ▸ hj) h

theorem vS_vtx {k : ℕ} (hk : k < 137632) : vS k ∈ cfg.Vtx := (sets_ok k (size_eq ▸ hk)).2

theorem canon_vS {k : ℕ} (hk : k < 137632) : Canon orb.sets[k]! := (sets_ok k (size_eq ▸ hk)).1

theorem vS_surj {V : Finset (Fin 31671)} (hV : V ∈ cfg.Vtx) : ∃ k < 137632, vS k = V := by
  obtain ⟨k, hk, e⟩ := vS_surj0 hV
  exact ⟨k, size_eq ▸ hk, e⟩

theorem mem_vS {k h : ℕ} (hh : h < 31671) : pBit orb.sets[k]! h = true ↔ fp h ∈ vS k := by
  rw [vS, mem_toF, fp_val hh]

theorem not_mem_vS {k h : ℕ} (hh : h < 31671) : pBit orb.sets[k]! h = false ↔ fp h ∉ vS k := by
  rw [← Bool.not_eq_true, mem_vS hh]

theorem cc_cp : ∀ k < 31671, cc k = cp k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rw [cc_eq]
    by_cases h0 : k = 0
    · subst h0
      rw [if_neg (by omega), cp_zero, dEl]
      have e : phiX wD = phiX (dWord.map fun x => if x = 0 then wα else wβ).prod ^ 7 :=
        ActsAs.ext phiX_wD acts_dWord7
      rw [e, map_list_prod, List.map_map]
      congr 2
    · have hp := (tr_pt hk h0).1
      have epar : ap orbLit.par k = tb G 91 k := ap_tabOf 91 hk
      have elb : ap orbLit.lab k = tb G 92 k := ap_tabOf 92 hk
      rw [if_pos ⟨Nat.pos_of_ne_zero h0, by rw [epar]; exact hp⟩, epar, elb, ih _ hp (by omega),
        cp_step hk h0]
      by_cases hl : tb G 92 k = 1
      · simp only [labW, if_pos hl]
      · simp only [labW, if_neg hl]

theorem act_conj : ∀ k < 31671, ∀ m < 137632, tA k m < 137632 ∧ vS (tA k m) = tau (fp k) • vS m := by
  have hpa : ∀ k < 137632, ap orb.pa k < 137632 ∧ vS (ap orb.pa k) = phiX wα • vS k := fun k hk => by
    have h := pa_vS k (size_eq ▸ hk)
    rw [size_eq] at h
    exact h
  have hpb : ∀ k < 137632, ap orb.pb k < 137632 ∧ vS (ap orb.pb k) = phiX wβ • vS k := fun k hk => by
    have h := pb_vS k (size_eq ▸ hk)
    rw [size_eq] at h
    exact h
  have h := trAct_conj (O := orbLit) cc hpa hpb alpha_sq beta_cube cc_eq
  intro k hk m hm
  obtain ⟨h1, h2⟩ := h k m hm
  rw [cc_cp k hk] at h2
  rw [tau, fp_val hk]
  exact ⟨h1, h2⟩

theorem tA_lt {k m : ℕ} (hk : k < 31671) (hm : m < 137632) : tA k m < 137632 := (act_conj k hk m hm).1

theorem vS_tA {k m : ℕ} (hk : k < 31671) (hm : m < 137632) : vS (tA k m) = tau (fp k) • vS m :=
  (act_conj k hk m hm).2

theorem adj_tA {k m : ℕ} (hk : k < 31671) (hm : m < 137632) (h : pBit orb.sets[m]! k = false) :
    Adj tau (vS m) (vS (tA k m)) :=
  ⟨fp k, (not_mem_vS hk).1 h, vS_tA hk hm⟩

theorem tB_false {f : ℕ} (hf : f < 31671) : pBit (pOf (pZero ()) (trData ())) f = false ↔ fp f ∉ T0 := by
  rw [← Bool.not_eq_true, tB_iff hf]

theorem hF0 : ∀ f < 31671, pBit (pOf (pZero ()) (trData ())) f = false →
    trAct orbLit orb (trD orb) (trBi orb) f 0 < 137632 := fun f hf _ => tA_lt hf (by norm_num)

theorem none32_big : ¬ (none32 ()).toNat < 31671 := by decide

theorem RI_spec : RI.size = 137632 ∧ ∀ m < 137632,
    (RI[m]! = none32 () ∧ ∀ f < 31671, pBit (pOf (pZero ()) (trData ())) f = false → tA f 0 ≠ m) ∨
      (ap RI m < 31671 ∧ pBit (pOf (pZero ()) (trData ())) (ap RI m) = false ∧ tA (ap RI m) 0 = m) :=
  mkRowInv_spec _ _ _ _ _ hF0

theorem nr_iff {m : ℕ} (hm : m < 137632) : RI[m]! ≠ none32 () ↔ vS m ∈ cfg.Nr := by
  rcases RI_spec.2 m hm with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · rw [h1]
    refine ⟨fun h => absurd rfl h, ?_⟩
    rintro ⟨f, hf, e⟩
    have h := act_conj f.val f.isLt 0 (by norm_num)
    rw [fp_of, vS_zero] at h
    exact absurd (vS_inj h.1 hm (h.2.trans e.symm)) (h2 f.val f.isLt ((tB_false f.isLt).2
      (by rwa [fp_of])))
  · refine ⟨fun _ => ⟨fp (ap RI m), (tB_false h1).1 h2, ?_⟩, fun _ e => ?_⟩
    · have e := vS_tA h1 (by norm_num : 0 < 137632)
      rw [h3, vS_zero] at e
      exact e
    · unfold ap at h1
      rw [e] at h1
      exact none32_big h1

theorem nr_of {m : ℕ} (hm : m < 137632) (h : RI[m]! ≠ none32 ()) : vS m ∈ cfg.Nr := (nr_iff hm).1 h

theorem far_iff {m : ℕ} (hm : m < 137632) :
    trIsFar RI m = true ↔ (vS m ≠ T0 ∧ vS m ∉ cfg.Nr) := by
  have h0 : m ≠ 0 ↔ vS m ≠ T0 := by
    rw [← vS_zero]
    exact ⟨fun h e => h (vS_inj hm (by norm_num) e), fun h e => h (by rw [e])⟩
  have h1 : RI[m]! = none32 () ↔ vS m ∉ cfg.Nr := by rw [← nr_iff hm, not_not]
  unfold trIsFar
  rw [Bool.and_eq_true, bne_iff_ne, beq_iff_eq, h0, h1]

end

end CertificateChecks.KernelFi23T

end
