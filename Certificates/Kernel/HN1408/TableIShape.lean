
module

public import Certificates.Kernel.HN1408.TableIGlue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeA8
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableISpec
import CFSG.Certificates.Kernel.BfsPinSetSound

public section

namespace CFSG.KD.HN1408

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KC.Blk

theorem closure_mapsTo {α : Type*} [Fintype α] [DecidableEq α] {T : Set (Equiv.Perm α)}
    (s : Finset α) (h : ∀ g ∈ T, ∀ x ∈ s, g x ∈ s) : ∀ g ∈ closure T, ∀ x ∈ s, g x ∈ s := by
  let H : Subgroup (Equiv.Perm α) :=
    { carrier := {g | ∀ x ∈ s, g x ∈ s}
      one_mem' := fun x hx => hx
      mul_mem' := fun {g g'} hg hg' x hx => by
        rw [Equiv.Perm.mul_apply]
        exact hg _ (hg' x hx)
      inv_mem' := fun {g} hg x hx => by
        have hsub : s.image g ⊆ s := fun y hy => by
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hy
          exact hg z hz
        have heq : s.image g = s :=
          Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injective _ g.injective])
        rw [← heq] at hx
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hx
        simpa using hz }
  have hle : closure T ≤ H := by
    rw [closure_le]
    exact fun g hg => h g hg
  exact fun g hg => hle hg

theorem ap_val {T : Table} {g : Equiv.Perm (Fin 1408)} (hT : Rep 1408 T g) (p : Fin 1408) :
    ap T p.val = (g p).val := by
  rw [hT p.val p.2, idx_of_lt g p.2, Equiv.Perm.smul_def]

theorem repW {w : List Nat} (hw : lettersOK w = true) : Rep 1408 (tabW w) (elemW w) :=
  rep_elemW_of_gensOK gensOK_true (wordOK_of hw)

theorem pt_val {w : List Nat} (hw : lettersOK w = true) (p : Fin 1408) :
    pt (WK w) p.val = (elemW w p).val := by
  rw [← ap_eq (tabW_eq hw).2 p.2, ← (tabW_eq hw).1]
  exact ap_val (repW hw) p

@[expose] noncomputable def orbSet : Finset (Fin 1408) :=
  Finset.univ.filter fun x => inOrbS2 x.val = true

theorem mem_orbSet {x : Fin 1408} : x ∈ orbSet ↔ inOrbS2 x.val = true := by simp [orbSet]

theorem orbMapK_spec {w : List Nat} (hw : lettersOK w = true) (h : orbMapK (WK w) = true) :
    ∀ x ∈ orbSet, elemW w x ∈ orbSet := by
  intro x hx
  rw [mem_orbSet] at hx ⊢
  rw [← pt_val hw]
  unfold orbMapK at h
  unfold inOrbS2 at hx
  obtain ⟨o, ho, he⟩ := List.any_eq_true.1 hx
  rw [← Nat.eq_of_beq_eq_true he]
  exact List.all_eq_true.1 h o ho

theorem t2_parts :
    (∀ j < 2, commP (WK (sWords2.getD j [])) (WK wordB) = true ∧
      orbMapK (WK (sWords2.getD j [])) = true) ∧
    blkTrivK 1408 11 4 (TB.F 1) (WK wordA) = true ∧ blkTrivK 1408 11 4 (TB.F 1) (WK wordB) = true ∧
    inOrbS2 (pt (WK wordA) 3) = false ∧ inOrbS2 (pt (WK wordB) 3) = false ∧
    inOrbS2 (pt (WK (wordA ++ wordB)) 3) = false := by
  have t := kT2
  simp only [bAnd_iff] at t
  obtain ⟨t1, t3, t5, t7, t9, t10⟩ := t
  refine ⟨fun j hj => ?_, t3, t5, ?_, ?_, ?_⟩
  · have h := allN_spec t1 j hj
    simp only [strictB_app, bAnd_iff] at h
    exact h
  · cases e : inOrbS2 (pt (WK wordA) 3)
    · rfl
    · rw [e] at t7
      cases t7
  · cases e : inOrbS2 (pt (WK wordB) 3)
    · rfl
    · rw [e] at t9
      cases t9
  · cases e : inOrbS2 (pt (WK (wordA ++ wordB)) 3)
    · rfl
    · rw [e] at t10
      cases t10

theorem sw_mem {w : List Nat} (hw : w ∈ sWords2) : ∃ j < 2, sWords2.getD j [] = w := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
  exact ⟨j, hj, List.getD_eq_getElem _ _ hj⟩

theorem orb_S : ∀ g ∈ closure (elemW '' {w | w ∈ sWords2}), ∀ x ∈ orbSet, g x ∈ orbSet := by
  refine closure_mapsTo orbSet ?_
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨j, hj, rfl⟩ := sw_mem hw
  exact orbMapK_spec (hl2 _ hw) (t2_parts.1 j hj).2

theorem not_mem_S {w : List Nat} (hw : lettersOK w = true) (h : inOrbS2 (pt (WK w) 3) = false) :
    elemW w ∉ closure (elemW '' {w | w ∈ sWords2}) := by
  intro hm
  have h3 : (⟨3, by norm_num⟩ : Fin 1408) ∈ orbSet := by rw [mem_orbSet]; decide
  have := orb_S _ hm _ h3
  rw [mem_orbSet, ← pt_val hw] at this
  rw [this] at h
  cases h

theorem rA : Rep 1408 (tabW wordA) elemA := repW (by decide)
theorem rB : Rep 1408 (tabW wordB) elemB := repW (by decide)

theorem basic_ab : orderOf elemA = 2 ∧ orderOf elemB = 2 ∧ (∀ g ∈ P1408, elemA * g = g * elemA) ∧
    elemA ∈ blocks1408 ∧ elemB ∉ blocks1408 := by
  have h := twoHSBasicOK_of
  simp only [twoHSBasicOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hA⟩, -⟩, hB⟩, -⟩, hc⟩, hbA⟩, -⟩, -⟩, hsB⟩, -⟩ := h
  refine ⟨orderOf_eq_two_of_involOK (by norm_num) rA hA,
    orderOf_eq_two_of_involOK (by norm_num) rB hB, ?_,
    mem_blocks1408_of_preservesHalves rA hbA, not_mem_blocks1408_of_swapsZero rB hsB⟩
  intro g hg
  rw [← genOf_h1408Gens] at hg
  have hgen : ∀ x ∈ h1408Gens, elemA * tp 1408 x = tp 1408 x * elemA := by
    intro x hx
    have hp : permOK 1408 x = true := by
      have h := List.all_eq_true.1 gens_all x hx
      simp only [Bool.and_eq_true] at h
      exact h.1
    exact (commTT_iff rA (rep_tp hp)).1 (hc x hx)
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact hgen x (by simpa using hx)
  | one => simp
  | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
  | inv x _ hx =>
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, hx, ← mul_assoc, inv_mul_cancel, one_mul]

theorem ker_eq {G : Type*} [Group G] {X V : Subgroup G} (hVX : V ≤ X) {H : Type*} [Group H]
    (φ : ↥X →* H) (hX : Nat.card ↥X = 80640) (hr : Nat.card ↥φ.range = 20160)
    (hV : Nat.card ↥V = 4) (hVker : ∀ (v : G) (h : v ∈ V), φ ⟨v, hVX h⟩ = 1) :
    ∀ x : ↥X, φ x = 1 → (x : G) ∈ V := by
  have hK : Nat.card ↥φ.ker = 4 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hr, hX] at h
    omega
  have hV' : Nat.card ↥(V.subgroupOf X) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv, hV]
  have hle : V.subgroupOf X ≤ φ.ker := fun x hx => by
    rw [MonoidHom.mem_ker]
    exact hVker x (Subgroup.mem_subgroupOf.1 hx)
  have : Finite ↥φ.ker := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hK, hV'])
  intro x hx
  have : x ∈ V.subgroupOf X := by rw [heq]; exact hx
  exact Subgroup.mem_subgroupOf.1 this

theorem tableI2_shape_of
    (hX : Nat.card ↥(closure (elemW '' {w | w ∈ blkData2.gens})) = 80640)
    (hXeq : closure (elemW '' {w | w ∈ blkData2.gens}) =
      P1408 ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408)))) :
    IsShapeTwoTwoTimesA8 ↥(closure (elemW '' {w | w ∈ blkData2.gens})) := by
  obtain ⟨hst, ht3, ht5, hnA, hnB, hnAB⟩ := t2_parts
  obtain ⟨hoA, hoB, hcA, hbA, hbB⟩ := basic_ab
  obtain ⟨φ, -, hrange, hker⟩ := blkData_spec dat2
  have hg : gensOK = true := gensOK_of_blkDataOK dat2
  have ha2 : elemA * elemA = 1 := mul_self_eq_one_of_orderOf_eq_two hoA
  have hb2 : elemB * elemB = 1 := mul_self_eq_one_of_orderOf_eq_two hoB
  have hab : elemA * elemB = elemB * elemA := hcA _ elemB_mem
  have hSX : closure (elemW '' {w | w ∈ sWords2}) ≤ closure (elemW '' {w | w ∈ blkData2.gens}) := by
    rw [hXeq, closure_le]
    rintro _ ⟨w, hw, rfl⟩
    refine Subgroup.mem_inf.2 ⟨elemW_mem w, mem_centralizer_iff.2 ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    obtain ⟨j, hj, rfl⟩ := sw_mem hw
    have hc := (hst j hj).1
    rw [← commTT_eq (tabW_eq (hl2 _ hw)).2 (tabW_eq (wd := wordB) (by decide)).2,
      ← (tabW_eq (hl2 _ hw)).1, ← (tabW_eq (wd := wordB) (by decide)).1] at hc
    exact ((commTT_iff (repW (hl2 _ hw)) rB).1 hc).symm
  have hVX : closure ({elemA, elemB} : Set (Equiv.Perm (Fin 1408))) ≤
      closure (elemW '' {w | w ∈ blkData2.gens}) := by
    rw [hXeq, closure_le]
    intro v hv
    rcases hv with rfl | hv
    · exact Subgroup.mem_inf.2 ⟨elemA_mem, mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hab.symm⟩
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact Subgroup.mem_inf.2 ⟨elemB_mem, mem_centralizer_iff.2 fun h hh => by
        rw [Set.mem_singleton_iff] at hh
        rw [hh]⟩
  have hVcen : ∀ v ∈ closure ({elemA, elemB} : Set (Equiv.Perm (Fin 1408))),
      ∀ x ∈ closure (elemW '' {w | w ∈ blkData2.gens}), x * v = v * x := by
    intro v hv x hx
    rw [hXeq] at hx
    have hxP : x ∈ P1408 := (Subgroup.mem_inf.1 hx).1
    have hxC := mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 elemB rfl
    rcases (TwoHSData.mem_closure_pair_iff ha2 hb2 hab).1 hv with rfl | rfl | rfl | rfl
    · simp
    · exact (hcA x hxP).symm
    · exact hxC.symm
    · rw [← mul_assoc, ← (hcA x hxP), mul_assoc, ← hxC, mul_assoc]
  have hA1 : elemA ≠ 1 := fun h => by rw [h, orderOf_one] at hoA; cases hoA
  have hB1 : elemB ≠ 1 := fun h => by rw [h, orderOf_one] at hoB; cases hoB
  have hAB : elemA ≠ elemB := fun h => hbB (h ▸ hbA)
  have hV : Nonempty (↥(closure ({elemA, elemB} : Set (Equiv.Perm (Fin 1408)))) ≃* Elem2 2) :=
    TwoHSData.nonempty_mulEquiv_elem2_closure_pair ha2 hb2 hab hA1 hB1 hAB
  have hVcard : Nat.card ↥(closure ({elemA, elemB} : Set (Equiv.Perm (Fin 1408)))) = 4 :=
    TwoHSData.card_closure_pair ha2 hb2 hab hA1 hB1 hAB
  have hfixV : ∀ t ∈ ({elemA, elemB} : Set (Equiv.Perm (Fin 1408))),
      ∀ p : Fin 1408, blkF blkData2.k blkData2.blk (t p) = blkF blkData2.k blkData2.blk p := by
    have eA : blkTrivOK blkData2.blk (tabW wordA) = true := by
      rw [blk2, (tabW_eq (wd := wordA) (by decide)).1, blkTrivOK_eq (tabW_eq (wd := wordA) (by decide)).2]
      exact ht3
    have eB : blkTrivOK blkData2.blk (tabW wordB) = true := by
      rw [blk2, (tabW_eq (wd := wordB) (by decide)).1, blkTrivOK_eq (tabW_eq (wd := wordB) (by decide)).2]
      exact ht5
    rintro t (rfl | ht)
    · exact fun p => blkTrivOK_spec rA eA p
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      exact fun p => blkTrivOK_spec rB eB p
  have hVker : ∀ (v : Equiv.Perm (Fin 1408))
      (h : v ∈ closure ({elemA, elemB} : Set (Equiv.Perm (Fin 1408)))), φ ⟨v, hVX h⟩ = 1 :=
    fun v h => (hker ⟨v, hVX h⟩).2 (blkTriv_closure_set hfixV v h)
  have hrange' : Nat.card ↥φ.range = 20160 := by
    rw [hrange]
    exact blkImage_spec dat2 (by decide) img2
  have hSV : ∀ s ∈ closure (elemW '' {w | w ∈ sWords2}),
      s ∈ closure ({elemA, elemB} : Set (Equiv.Perm (Fin 1408))) → s = 1 := by
    intro s hs hv
    rcases (TwoHSData.mem_closure_pair_iff ha2 hb2 hab).1 hv with rfl | rfl | rfl | rfl
    · rfl
    · exact absurd hs (not_mem_S (by decide) hnA)
    · exact absurd hs (not_mem_S (by decide) hnB)
    · have e : elemA * elemB = elemW (wordA ++ wordB) := (elemW_append wordA wordB).symm
      rw [e] at hs
      exact absurd hs (not_mem_S (by decide) hnAB)
  have hkerV := ker_eq hVX φ hX hrange' hVcard hVker
  have hSinj : ∀ (s : Equiv.Perm (Fin 1408)) (h : s ∈ closure (elemW '' {w | w ∈ sWords2})),
      φ ⟨s, hSX h⟩ = 1 → s = 1 := fun s h h1 => hSV s h (hkerV _ h1)
  have hScard : Nat.card ↥(closure (elemW '' {w | w ∈ sWords2})) = 20160 := by
    refine le_antisymm ?_ ?_
    · rw [← hrange']
      refine Nat.card_le_card_of_injective
        (fun s => (⟨φ ⟨s, hSX s.2⟩, MonoidHom.mem_range.2 ⟨_, rfl⟩⟩ : ↥φ.range)) ?_
      intro s t hst'
      have e : φ ⟨s, hSX s.2⟩ = φ ⟨t, hSX t.2⟩ := congrArg Subtype.val hst'
      have hm : (s : Equiv.Perm (Fin 1408)) * (t : Equiv.Perm (Fin 1408))⁻¹ ∈
          closure (elemW '' {w | w ∈ sWords2}) := mul_mem s.2 (inv_mem t.2)
      have h1 : φ ⟨_, hSX hm⟩ = 1 := by
        have : (⟨_, hSX hm⟩ : ↥(closure (elemW '' {w | w ∈ blkData2.gens}))) =
            ⟨s, hSX s.2⟩ * (⟨t, hSX t.2⟩)⁻¹ := rfl
        rw [this, map_mul, map_inv, e, mul_inv_cancel]
      exact Subtype.ext (mul_inv_eq_one.1 (hSinj _ hm h1))
    · obtain ⟨φS, -, hrS, -⟩ := blkData_spec datS
      have hcS : Nat.card ↥φS.range = 20160 := by
        rw [hrS]
        exact blkImage_spec datS (by decide) imgS
      rw [← hcS]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd φS)
  exact TwoHSData.isShapeTwoTwoTimesA8_of_hom
    (closure (elemW '' {w | w ∈ blkData2.gens}))
    (closure ({elemA, elemB} : Set (Equiv.Perm (Fin 1408))))
    (closure (elemW '' {w | w ∈ sWords2})) φ hVX hSX hVcen hV hVker hX hScard hrange' hSinj

end CFSG.KD.HN1408

end
