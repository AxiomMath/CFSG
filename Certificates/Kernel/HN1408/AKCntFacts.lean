module

public import Certificates.Kernel.HN1408.AKCntChk
public import Certificates.Kernel.HN1408.AKFacts
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.AK

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native CFSG.KD.HN1408

theorem nat_eqC {X Y : Nat} {g : Equiv.Perm (Fin 1408)} (hX : RepC X g) (hY : RepC Y g) :
    X = Y := by
  obtain ⟨-, hw, h1, -⟩ := CFSG.KS.PF.canon_facts hX.1
  obtain ⟨-, -, h2, -⟩ := CFSG.KS.PF.canon_facts hY.1
  exact CFSG.KS.PF.eq_of_fields (CFSG.KS.PF.w_pos hw) h1 h2 fun i hi => by
    rw [SylSG.pt_rep hX.1 hX.2 hi, SylSG.pt_rep hY.1 hY.2 hi]

theorem commF_iff {R Y : Nat} {r y : Equiv.Perm (Fin 1408)} (hR : RepC R r) (hY : RepC Y y) :
    commF R Y = true ↔ r * y = y * r := by
  constructor
  · intro h
    unfold commF at h
    simp only [CFSG.KS.Raw.Orb.bIf_eq] at h
    split_ifs at h
    all_goals first
      | exact comm_of_commP hR hY h
      | exact absurd h Bool.false_ne_true
  · intro h
    have hp : ∀ p, p < 1408 → commAt R Y p = true := by
      intro p hp
      unfold commAt
      rw [← pt_pc hR.1 hp, ← pt_pc hY.1 hp, repC_pt (repC_pc hR hY) hp,
        repC_pt (repC_pc hY hR) hp, h]
      exact Nat.beq_refl _
    have hc : commP R Y = true := by
      unfold commP
      have e : pc R Y = pc Y R := nat_eqC (repC_pc hR hY) (by rw [h]; exact repC_pc hY hR)
      rw [e]
      exact Nat.beq_refl _
    unfold commF
    rw [hp 0 (by norm_num), hp 1 (by norm_num), hp 2 (by norm_num), hp 3 (by norm_num), hc]

theorem conj_comm_iff {G : Type*} [Group G] (a x c : G) :
    a * (c⁻¹ * (x * c)) = c⁻¹ * (x * c) * a ↔ c * a * c⁻¹ * x = x * (c * a * c⁻¹) := by
  constructor
  · intro h
    calc c * a * c⁻¹ * x = c * (a * (c⁻¹ * (x * c))) * c⁻¹ := by group
      _ = c * (c⁻¹ * (x * c) * a) * c⁻¹ := by rw [h]
      _ = x * (c * a * c⁻¹) := by group
  · intro h
    calc a * (c⁻¹ * (x * c)) = c⁻¹ * (c * a * c⁻¹ * x) * c := by group
      _ = c⁻¹ * (x * (c * a * c⁻¹)) * c := by rw [h]
      _ = c⁻¹ * (x * c) * a := by group

noncomputable def cz (r : Nat → Equiv.Perm (Fin 1408)) (p : Nat × Nat) : Equiv.Perm (Fin 1408) :=
  elemW y0Word ^ p.2 * r p.1 * (elemW y0Word ^ p.2)⁻¹

theorem elemW_classz : elemW classz.rep = elemZ := by
  have e : classz.rep = wordZ := by decide
  rw [e]
  rfl

theorem grid (hP : Nat.card ↥P1408 = 177408000) :
    ∃ r : Nat → Equiv.Perm (Fin 1408), (∀ i < 525, RepC (MRZ i) (r i)) ∧
      Set.InjOn (cz r) ↑(Finset.range 525 ×ˢ Finset.range 11) ∧
      (↑((Finset.range 525 ×ˢ Finset.range 11).image (cz r)) : Set (Equiv.Perm (Fin 1408))) =
        conjClass P1408 elemZ := by
  classical
  have h := kCZ
  obtain ⟨-, -, hs, -⟩ := clsK_parts h
  have hreps := reps_mem (by decide) h
  rw [elemW_classz] at hreps
  have H : ∀ i, ∃ r : Equiv.Perm (Fin 1408), i < 525 → r ∈ conjClass P1408 elemZ ∧
      RepC (MRZ i) r := by
    intro i
    by_cases hi : i < 525
    · obtain ⟨c, hcP, hcR⟩ := hreps i hi
      exact ⟨_, fun _ => ⟨⟨c, hcP, rfl⟩, hcR⟩⟩
    · exact ⟨1, fun h => absurd h hi⟩
  choose r hr using H
  refine ⟨r, fun i hi => (hr i hi).2, ?_⟩
  have hS : ∀ m < 5775, f16 (MSZ m) 0 < 525 ∧ f16 (MSZ m) 1 < 11 := by
    intro m hm
    have h1 := allN_spec hs m hm
    simp only [strictB_app] at h1
    obtain ⟨a, h1⟩ := mkA h1
    obtain ⟨b, -⟩ := mkA h1
    exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp b⟩
  obtain ⟨e, he⟩ : ∃ e : Nat → Equiv.Perm (Fin 1408), ∀ m,
      e m = cz r (f16 (MSZ m) 0, f16 (MSZ m) 1) := ⟨_, fun _ => rfl⟩
  have hkey : ∀ m < 5775, keyK (MRZ (f16 (MSZ m) 0)) (f16 (MSZ m) 1) = keyP (e m) := by
    intro m hm
    rw [he m]
    exact keyK_eq (hr _ (hS m hm).1).2 (by have := (hS m hm).2; omega)
  have hsucc : ∀ m, m + 1 < 5775 → keyP (e m) < keyP (e (m + 1)) := by
    intro m hm
    have h1 := allN_spec hs m (by omega)
    simp only [strictB_app] at h1
    obtain ⟨-, h1⟩ := mkA h1
    obtain ⟨-, h1⟩ := mkA h1
    have e1 : Nat.blt (m + 1) 5775 = true := Nat.blt_eq.mpr hm
    rw [e1] at h1
    rw [← hkey m (by omega), ← hkey (m + 1) hm]
    exact Nat.blt_eq.mp h1
  have hmono : ∀ m m', m < m' → m' < 5775 → keyP (e m) < keyP (e m') := by
    intro m m' hlt hm'
    induction m' with
    | zero => omega
    | succ m' ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h' | h'
      · exact (ih h' (by omega)).trans (hsucc m' hm')
      · rw [h']
        exact hsucc m' hm'
  have hinj : Set.InjOn e ↑(Finset.range 5775) := by
    intro m hm m' hm' hee
    have hm1 : m < 5775 := Finset.mem_range.1 hm
    have hm2 : m' < 5775 := Finset.mem_range.1 hm'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := hmono m m' hlt hm2
      rw [hee] at h1
      exact lt_irrefl _ h1
    · have h1 := hmono m' m hlt hm1
      rw [hee] at h1
      exact lt_irrefl _ h1
  set G := Finset.range 525 ×ˢ Finset.range 11 with hG
  have hsub : (↑(G.image (cz r)) : Set (Equiv.Perm (Fin 1408))) ⊆ conjClass P1408 elemZ := by
    intro x hx
    obtain ⟨⟨i, k⟩, hp, rfl⟩ := Finset.mem_image.1 hx
    simp only [hG, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨⟨c, hcP, hcr⟩, -⟩ := hr i hp.1
    refine ⟨elemW y0Word ^ k * c, mul_mem (pow_mem (elemW_mem _) _) hcP, ?_⟩
    change elemW y0Word ^ k * r i * (elemW y0Word ^ k)⁻¹ = _
    rw [hcr]
    group
  have hge : 5775 ≤ (G.image (cz r)).card := by
    have hsub2 : (Finset.range 5775).image e ⊆ G.image (cz r) := by
      intro x hx
      obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hx
      have hm1 := (hS m (Finset.mem_range.1 hm))
      rw [he m]
      exact Finset.mem_image_of_mem _ (by
        simp only [hG, Finset.mem_product, Finset.mem_range]
        exact hm1)
    have h1 := Finset.card_le_card hsub2
    rwa [Finset.card_image_of_injOn hinj, Finset.card_range] at h1
  have heq : (↑(G.image (cz r)) : Set (Equiv.Perm (Fin 1408))) = conjClass P1408 elemZ := by
    refine Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)
    rw [CzT.class_z_card hP, Set.ncard_coe_finset]
    exact hge
  have hcard : (G.image (cz r)).card = G.card := by
    have h1 := congrArg Set.ncard heq
    rw [Set.ncard_coe_finset, CzT.class_z_card hP] at h1
    rw [h1, hG, Finset.card_product, Finset.card_range, Finset.card_range]
  exact ⟨Finset.card_image_iff.mp hcard, heq⟩

theorem foldr_add_range (c : Nat → Nat) :
    ∀ n s : Nat, (List.range n).foldr (fun k s => s + c k) s = s + ∑ k ∈ Finset.range n, c k
  | 0, s => by simp
  | n + 1, s => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_add_range c n,
      Finset.sum_range_succ]
    ring

theorem foldr_nIf (q : Nat → Bool) : ∀ n s : Nat,
    (List.range n).foldr (fun i s => nIf(q i, Nat.succ s, s)) s =
      s + ∑ i ∈ Finset.range n, if q i = true then 1 else 0
  | 0, s => by simp
  | n + 1, s => by
    rw [List.range_succ, List.foldr_append, List.foldr_cons, List.foldr_nil, foldr_nIf q n,
      Finset.sum_range_succ]
    cases q n
    · change s + _ = s + (_ + 0)
      omega
    · change Nat.succ s + _ = s + (_ + 1)
      omega

theorem cntR_eq (Y s : Nat) :
    cntR Y s = s + ∑ i ∈ Finset.range 525, if commF (MRZ i) Y = true then 1 else 0 := by
  unfold cntR
  rw [CFSG.KS.Raw.Orb.foldN_eq]
  exact foldr_nIf (fun i => commF (MRZ i) Y) 525 s

theorem cntZ_eq (X : Nat) : cntZ X = ∑ k ∈ Finset.range 11, ∑ i ∈ Finset.range 525,
    if commF (MRZ i) (pc (MYP (11 - k)) (pc X (MYP k))) = true then 1 else 0 := by
  unfold cntZ
  rw [CFSG.KS.Raw.Orb.foldN_eq]
  have e : (fun k s => strictN (pc (MYP (11 - k)) (pc X (MYP k))) fun Y => cntR Y s) =
      fun k s => s + ∑ i ∈ Finset.range 525,
        if commF (MRZ i) (pc (MYP (11 - k)) (pc X (MYP k))) = true then 1 else 0 := by
    funext k s
    rw [CFSG.KS.Raw.Orb.strictN_eq, cntR_eq]
  refine (congrArg (fun f => (List.range 11).foldr f 0) e).trans ?_
  exact (foldr_add_range (fun k => ∑ i ∈ Finset.range 525,
    if commF (MRZ i) (pc (MYP (11 - k)) (pc X (MYP k))) = true then 1 else 0) 11 0).trans
    (Nat.zero_add _)

noncomputable def ncz (x : Equiv.Perm (Fin 1408)) : Nat :=
  {c | c ∈ conjClass P1408 elemZ ∧ c * x = x * c}.ncard

theorem cnt_eq (hP : Nat.card ↥P1408 = 177408000) {X : Nat} {x : Equiv.Perm (Fin 1408)}
    (hX : RepC X x) : ncz x = cntZ X := by
  classical
  obtain ⟨r, hr, hinj, himg⟩ := grid hP
  set G := Finset.range 525 ×ˢ Finset.range 11 with hG
  set F := G.filter fun p => cz r p * x = x * cz r p with hF
  have e1 : {c | c ∈ conjClass P1408 elemZ ∧ c * x = x * c} =
      (↑(F.image (cz r)) : Set (Equiv.Perm (Fin 1408))) := by
    ext c
    constructor
    · rintro ⟨hc, hcomm⟩
      rw [← himg] at hc
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hc)
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨p, Finset.mem_filter.2 ⟨hp, hcomm⟩, rfl⟩)
    · intro h
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 h)
      refine ⟨?_, (Finset.mem_filter.1 hp).2⟩
      rw [← himg]
      exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_filter.1 hp).1)
  have hinjF : Set.InjOn (cz r) ↑F :=
    hinj.mono (Finset.coe_subset.2 (Finset.filter_subset _ _))
  unfold ncz
  rw [e1, Set.ncard_coe_finset, Finset.card_image_of_injOn hinjF, hF, Finset.card_filter, hG,
    Finset.sum_product, Finset.sum_comm, cntZ_eq]
  refine Finset.sum_congr rfl fun k hk => Finset.sum_congr rfl fun i hi => ?_
  have hk' : k < 11 := Finset.mem_range.1 hk
  have hi' : i < 525 := Finset.mem_range.1 hi
  have hY : RepC (pc (MYP (11 - k)) (pc X (MYP k)))
      ((elemW y0Word ^ k)⁻¹ * (x * elemW y0Word ^ k)) := by
    have h1 := repC_pc (repC_yp (k := 11 - k) (by omega)) (repC_pc hX (repC_yp (k := k) (by omega)))
    rwa [y_inv (by omega)] at h1
  have hiff : commF (MRZ i) (pc (MYP (11 - k)) (pc X (MYP k))) = true ↔
      cz r (i, k) * x = x * cz r (i, k) :=
    (commF_iff (hr i hi') hY).trans (conj_comm_iff _ _ _)
  by_cases hq : cz r (i, k) * x = x * cz r (i, k)
  · rw [if_pos hq, if_pos (hiff.2 hq)]
  · rw [if_neg hq, if_neg (mt hiff.1 hq)]

theorem ncz_conj {g x : Equiv.Perm (Fin 1408)} (hg : g ∈ P1408) : ncz (g * x * g⁻¹) = ncz x := by
  unfold ncz
  have e : {c | c ∈ conjClass P1408 elemZ ∧ c * (g * x * g⁻¹) = g * x * g⁻¹ * c} =
      (fun c => g * c * g⁻¹) '' {c | c ∈ conjClass P1408 elemZ ∧ c * x = x * c} := by
    ext c
    constructor
    · rintro ⟨⟨h, hh, rfl⟩, hc⟩
      refine ⟨g⁻¹ * (h * elemZ * h⁻¹) * g, ⟨⟨g⁻¹ * h, mul_mem (inv_mem hg) hh, by group⟩, ?_⟩, by
        group⟩
      calc g⁻¹ * (h * elemZ * h⁻¹) * g * x
          = g⁻¹ * ((h * elemZ * h⁻¹) * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * (h * elemZ * h⁻¹)) * g := by rw [hc]
        _ = x * (g⁻¹ * (h * elemZ * h⁻¹) * g) := by group
    · rintro ⟨c, ⟨⟨h, hh, rfl⟩, hc⟩, rfl⟩
      refine ⟨⟨g * h, mul_mem hg hh, by group⟩, ?_⟩
      calc g * (h * elemZ * h⁻¹) * g⁻¹ * (g * x * g⁻¹)
          = g * ((h * elemZ * h⁻¹) * x) * g⁻¹ := by group
        _ = g * (x * (h * elemZ * h⁻¹)) * g⁻¹ := by rw [hc]
        _ = g * x * g⁻¹ * (g * (h * elemZ * h⁻¹) * g⁻¹) := by group
  rw [e, Set.ncard_image_of_injective _ (fun a b hab => by simpa using hab)]

theorem vals_of {B Z : Nat} (h : bAnd(Nat.beq B 315, Nat.beq Z 75) = true) : B = 315 ∧ Z = 75 := by
  obtain ⟨hb, hz⟩ := mkA h
  exact ⟨Nat.eq_of_beq_eq_true hb, Nat.eq_of_beq_eq_true hz⟩

theorem cnt_vals : cntZ (WK wordB) = 315 ∧ cntZ (WK wordZ₁) = 75 := by
  have h := cnt_ok
  unfold cntK at h
  exact vals_of (B := cntZ (WK wordB)) (Z := cntZ (WK wordZ₁)) h

theorem ncz_b (hP : Nat.card ↥P1408 = 177408000) : ncz elemB = 315 :=
  (cnt_eq hP (repC_word (w := wordB) (by decide))).trans cnt_vals.1

theorem ncz_z₁ (hP : Nat.card ↥P1408 = 177408000) : ncz elemZ₁ = 75 :=
  (cnt_eq hP (repC_word (w := wordZ₁) (by decide))).trans cnt_vals.2

theorem b_not_conj_z₁ (hP : Nat.card ↥P1408 = 177408000) : elemB ∉ conjClass P1408 elemZ₁ := by
  have eb := ncz_b hP
  have ez := ncz_z₁ hP
  rintro ⟨g, hg, e⟩
  rw [e, ncz_conj hg, ez] at eb
  exact absurd eb (by norm_num)

end CFSG.KD.HN1408.AK

end
