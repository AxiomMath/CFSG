module

public import Certificates.Kernel.LocalComp.L34N3Chk
public import Certificates.Kernel.LocalComp.L34NFinal
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
import CFSG.Certificates.Kernel.L34KSnd.Tab

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.L34N3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Norm
open CertificateChecks.KernelLC.L34X CertificateChecks.KernelLC.L34Cert CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four
open CFSG.KC.HeAutK (cntR)

@[expose] def fixP (x : Equiv.Perm (Fin 42)) : ℕ := (Finset.univ.filter fun i => x i = i).card

@[expose] noncomputable def o3c (c : ℕ) (t : Tab) : Bool :=
  !(t == idTab 42) && (comp 42 t (comp 42 t t) == idTab 42) && (L34N.nfix t == 6 * c)

theorem fixP_conj (d y : Equiv.Perm (Fin 42)) : fixP (d * y * d⁻¹) = fixP y := by
  unfold fixP
  symm
  refine Finset.card_bij (fun i _ => d i) (fun i hi => ?_) (fun i _ j _ h => d.injective h)
    (fun j hj => ⟨d⁻¹ j, ?_, by simp⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    simp [Equiv.Perm.mul_apply, hi]
  · have hj' := (Finset.mem_filter.1 hj).2
    simp only [Equiv.Perm.mul_apply] at hj'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply d.injective
    simpa using hj'

theorem nfix_eq {t : Tab} {y : Equiv.Perm (Fin 42)} (ht : TabRep t y) : L34N.nfix t = fixP y := by
  unfold L34N.nfix fixP
  rw [CFSG.KC.HeAutK.cntR_eq, ← countBelow, countBelow_eq]
  symm
  refine Finset.card_bij (fun i _ => i.val) (fun i hi => ?_) (fun i _ j _ h => Fin.ext h)
    (fun j hj => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hi ⊢
    refine ⟨i.isLt, ?_⟩
    rw [ht.apply i, hi]
    exact beq_self_eq_true _
  · simp only [Finset.mem_filter, Finset.mem_range] at hj
    refine ⟨⟨j, hj.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.ext ((ht.apply ⟨j, hj.1⟩).symm.trans (beq_iff_eq.1 hj.2))

theorem o3c_iff {c : ℕ} {t : Tab} {y : Equiv.Perm (Fin 42)} (ht : TabRep t y) :
    o3c c t = true ↔ y ≠ 1 ∧ y ^ 3 = 1 ∧ fixP y = 6 * c := by
  unfold o3c
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
    ht.eq_iff TabRep.idTab, (ht.comp (ht.comp ht)).beq_iff TabRep.idTab, beq_iff_eq, nfix_eq ht,
    pow_three, and_assoc]

theorem T_lt {i : ℕ} (hi : i < 241920) :
    (enumBFS 42 gTabs 241920).tabs[i]! = unpack 42 6 (L34R.T i) := by
  rw [hR.1]
  exact CFSG.KC.L34KSnd.pts_get hi

theorem T_mem {i : ℕ} (hi : i < 241920) : unpack 42 6 (L34R.T i) ∈ enumR.tabs.toList := by
  rw [← T_lt hi]
  exact getElem!_mem (by rw [hR.1, size_pts]; exact hi)

theorem exists_T {x : Equiv.Perm (Fin 42)} (hx : x ∈ R) :
    ∃ i < 241920, TabRep (unpack 42 6 (L34R.T i)) x := by
  obtain ⟨k, hk, h⟩ := enumerates_R.exists_pos hx
  have hk' : k < 241920 := by
    rw [hR.1, size_pts] at hk
    exact hk
  rw [T_lt hk'] at h
  exact ⟨k, hk', h⟩

theorem kTot {c : ℕ} (hc : c < 3) : tot c = ON c := by
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
  · exact Nat.eq_of_beq_eq_true kTot0
  · exact Nat.eq_of_beq_eq_true kTot1
  · exact Nat.eq_of_beq_eq_true kTot2

theorem kOrb {c : ℕ} (hc : c < 3) : orb c = true := by
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
  exacts [kOrb0, kOrb1, kOrb2]

theorem kCent {c : ℕ} (hc : c < 3) : cent c = true := by
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
  exacts [kCent0, kCent1, kCent2]

theorem KR_lt {c : ℕ} (hc : c < 3) : KR c < 241920 := by
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> decide +kernel

theorem o3c_KR {c : ℕ} (hc : c < 3) : o3c c (unpack 42 6 (L34R.T (KR c))) = true := by
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl <;> decide +kernel

theorem length_o3c {c : ℕ} (hc : c < 3) : (enumR.tabs.toList.filter (o3c c)).length = ON c := by
  have e : (pts 42 6 241920 L34R.T).toList =
      (List.range 241920).map (fun i => unpack 42 6 (L34R.T i)) := by
    unfold pts
    exact CFSG.KC.BfsPin.pts_toList (N := 241920) (fun i => unpack 42 6 (L34R.T i))
  rw [hR.1, e, List.filter_map, List.length_map, ← CFSG.KC.HeAutK.cntR_eq,
    ← kTot hc]
  unfold tot
  rw [← L34N.count_eq (B := fun v => Nat.beq (v / 8) (c + 1)) (beq_false (by omega))]
  refine cntR_congr 0 241920 fun i hi => ?_
  rw [Nat.zero_add]
  have h := L34N.listed_iff (B := fun v => Nat.beq (v / 8) (c + 1)) (beq_false (by omega)) hi
  simp only [Nat.beq_eq] at h
  rw [Bool.eq_iff_iff, Function.comp_apply, Nat.beq_eq, h, ← L34N.order3_iff hi hc]
  unfold o3c
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, beq_iff_eq, and_assoc]

theorem pinOrb {c : ℕ} (hc : c < 3) : PinO 42 6 gTabs (unpack 42 6 (L34R.T (KR c))) (ON c) 6
    (ON c) 12 (L34R.T (KR c)) L34R.G GI (OT c) (OE c) (OS c) (OSI c) :=
  ⟨bindR.1, bindR.2, rfl, kOrb hc, le_refl _⟩

theorem size_ON {c : ℕ} (hc : c < 3) : (pts 42 6 (ON c) (OT c)).toList.length = ON c := by
  rw [Array.length_toList, size_pts]

@[expose] def X3 (c : ℕ) : Set (Equiv.Perm (Fin 42)) :=
  {y | y ∈ R ∧ y ≠ 1 ∧ y ^ 3 = 1 ∧ fixP y = 6 * c}

theorem card_X3 {c : ℕ} (hc : c < 3) : Nat.card (X3 c) = ON c := by
  rw [← length_o3c hc]
  refine card_set_of_tabs (fun t ht => ?_) (fun y hy => ?_) (enumerates_R.nodup.filter _)
  · rw [List.mem_filter] at ht
    obtain ⟨y, hy, hr⟩ := enumerates_R.sound t ht.1
    exact ⟨y, ⟨hy, (o3c_iff hr).1 ht.2⟩, hr⟩
  · obtain ⟨t, ht, hr⟩ := enumerates_R.complete y hy.1
    exact ⟨t, List.mem_filter.2 ⟨ht, (o3c_iff hr).2 hy.2⟩, hr⟩

theorem conj_X3 {c : ℕ} {d y : Equiv.Perm (Fin 42)} (hd : d ∈ R)
    (hy : y ∈ X3 c) : d * y * d⁻¹ ∈ X3 c := by
  obtain ⟨hyR, h1, h3, hf⟩ := hy
  refine ⟨R.mul_mem (R.mul_mem hd hyR) (R.inv_mem hd), fun h => h1 ?_, ?_, ?_⟩
  · have e : y = d⁻¹ * (d * y * d⁻¹) * d := by group
    rw [e, h]
    group
  · rw [conj_pow, h3, mul_one, mul_inv_cancel]
  · rw [fixP_conj, hf]

theorem conj_rep {c : ℕ} (hc : c < 3) :
    ∃ g ∈ X3 c, TabRep (unpack 42 6 (L34R.T (KR c))) g ∧ ∀ y ∈ X3 c, ∃ d ∈ R, y = d * g * d⁻¹ := by
  obtain ⟨g, hgR, hg⟩ := enumerates_R.sound _ (T_mem (KR_lt hc))
  have hgX : g ∈ X3 c := ⟨hgR, (o3c_iff hg).1 (o3c_KR hc)⟩
  refine ⟨g, hgX, hg, ?_⟩
  obtain ⟨hs, hcpl, hn⟩ := conj_orbit gTabs_cover gTabs_tabs hg (orbit_sound (pinOrb hc)).2
  rw [(orbit_sound (pinOrb hc)).1] at hs hcpl hn
  have hR' : Subgroup.closure ({g₁, g₂, g₃, g₄, g₅, g₆} : Set (Equiv.Perm (Fin 42))) = R := rfl
  rw [hR'] at hs hcpl
  let Cl : Set (Equiv.Perm (Fin 42)) := {y | ∃ d ∈ R, y = d * g * d⁻¹}
  have hCl : Nat.card Cl = ON c := by
    rw [← size_ON hc]
    refine card_set_of_tabs (fun t ht => ?_) (fun y hy => ?_) hn
    · obtain ⟨d, hd, hr⟩ := hs t ht
      exact ⟨_, ⟨d, hd, rfl⟩, hr⟩
    · obtain ⟨d, hd, rfl⟩ := hy
      exact hcpl d hd
  have hsub : Cl ⊆ X3 c := by
    rintro _ ⟨d, hd, rfl⟩
    exact conj_X3 hd hgX
  have heq : Cl = X3 c := by
    apply Set.eq_of_subset_of_ncard_le hsub _ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, card_X3 hc, hCl]
  intro y hy
  rw [← heq] at hy
  exact hy

theorem card_centS_conj {d g : Equiv.Perm (Fin 42)} (hd : d ∈ R) :
    Nat.card (Subgroup.centralizer {d * g * d⁻¹} ⊓ S : Subgroup (Equiv.Perm (Fin 42))) =
      Nat.card (Subgroup.centralizer {g} ⊓ S : Subgroup (Equiv.Perm (Fin 42))) := by
  have key : ∀ {e h z : Equiv.Perm (Fin 42)}, e ∈ R →
      z ∈ (Subgroup.centralizer {h} ⊓ S : Subgroup (Equiv.Perm (Fin 42))) →
      e * z * e⁻¹ ∈ (Subgroup.centralizer {e * h * e⁻¹} ⊓ S : Subgroup (Equiv.Perm (Fin 42))) := by
    intro e h z he hz
    rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hz ⊢
    refine ⟨?_, conj_mem_S he hz.2⟩
    calc e * z * e⁻¹ * (e * h * e⁻¹) = e * (z * h) * e⁻¹ := by group
      _ = e * (h * z) * e⁻¹ := by rw [hz.1]
      _ = e * h * e⁻¹ * (e * z * e⁻¹) := by group
  have e1 : ∀ h : Equiv.Perm (Fin 42), d⁻¹ * (d * h * d⁻¹) * d⁻¹⁻¹ = h := fun h => by group
  symm
  refine Nat.card_congr
    { toFun := fun z => ⟨d * z * d⁻¹, key hd z.2⟩
      invFun := fun z => ⟨d⁻¹ * z * d⁻¹⁻¹, by
        have := key (R.inv_mem hd) z.2
        rwa [e1] at this⟩
      left_inv := fun z => Subtype.ext (by simp only; group)
      right_inv := fun z => Subtype.ext (by simp only; group) }

theorem card_centS_rep {c : ℕ} (hc : c < 3) {g : Equiv.Perm (Fin 42)}
    (hg : TabRep (unpack 42 6 (L34R.T (KR c))) g) :
    Nat.card (Subgroup.centralizer {g} ⊓ S : Subgroup (Equiv.Perm (Fin 42))) = CN c := by
  have h := cent_sound (x := unpack 42 6 (L34R.T (KR c))) rfl (pinR.canon _ (KR_lt hc))
    pinS.canon (kCent hc)
  rw [(enumerates_cent hg).card, Array.length_toList, centS, hS.1, h, size_pts]

theorem card_centS_X3 {c : ℕ} (hc : c < 3)
    {x : Equiv.Perm (Fin 42)} (hx : x ∈ X3 c) :
    Nat.card (Subgroup.centralizer {x} ⊓ S : Subgroup (Equiv.Perm (Fin 42))) = CN c := by
  obtain ⟨g, -, hg, hall⟩ := conj_rep hc
  obtain ⟨d, hd, rfl⟩ := hall x hx
  rw [card_centS_conj hd, card_centS_rep hc hg]

theorem card_centS_of_order3 {x : Equiv.Perm (Fin 42)}
    (hx : x ∈ R) (h3 : x ^ 3 = 1) (h1 : x ≠ 1) :
    ((Finset.univ.filter fun i => x i = i).card = 0 ∧
        Nat.card (Subgroup.centralizer {x} ⊓ S : Subgroup (Equiv.Perm (Fin 42))) = 21) ∨
      ((Finset.univ.filter fun i => x i = i).card = 6 ∧
        Nat.card (Subgroup.centralizer {x} ⊓ S : Subgroup (Equiv.Perm (Fin 42))) = 9) ∨
      ((Finset.univ.filter fun i => x i = i).card = 12 ∧
        Nat.card (Subgroup.centralizer {x} ⊓ S : Subgroup (Equiv.Perm (Fin 42))) = 60) := by
  obtain ⟨i, hi, ht⟩ := exists_T hx
  have h1' : unpack 42 6 (L34R.T i) ≠ idTab 42 := fun e => h1 ((ht.eq_iff TabRep.idTab).1 e)
  have h3' : comp 42 (unpack 42 6 (L34R.T i)) (comp 42 (unpack 42 6 (L34R.T i))
      (unpack 42 6 (L34R.T i))) = idTab 42 :=
    ((ht.comp (ht.comp ht)).eq_iff TabRep.idTab).2 (by rw [← pow_three]; exact h3)
  have hf := L34N.nfix_of_order3 hi h1' h3'
  rw [nfix_eq ht] at hf
  have hX : ∀ c, fixP x = 6 * c → x ∈ X3 c := fun c e => ⟨hx, h1, h3, e⟩
  rcases hf with e | e | e
  · exact Or.inl ⟨e, card_centS_X3 (c := 0) (by decide) (hX 0 e)⟩
  · exact Or.inr (Or.inl ⟨e, card_centS_X3 (c := 1) (by decide) (hX 1 e)⟩)
  · exact Or.inr (Or.inr ⟨e, card_centS_X3 (c := 2) (by decide) (hX 2 e)⟩)

end CertificateChecks.KernelLC.L34N3

end
