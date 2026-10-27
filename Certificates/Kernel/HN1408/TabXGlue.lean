module

public import Certificates.Kernel.HN1408.TabXGrpFacts
public import Certificates.Kernel.HN1408.InvClassK
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TabXFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.WordSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableIData
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Elems
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.HSide.Map
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.OrbitCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCongrK
public import Certificates.Kernel.HN1408.ClsAZFacts

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.TabX

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.BaseEq CFSG.KD.HN1408.CzT
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.EvenSporadicStandard.HNRecog.Section3Model CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open CFSG.KS.MulH CFSG.KC.BfsPin

local notation "𝒞" => CFSG.Sporadic.SmallOddCore.conjClass

noncomputable abbrev c1K : Equiv.Perm (Fin 1408) := t0P 817 * t1P 0

theorem c1K_mem (hP : Nat.card ↥P1408 = 177408000) : c1K ∈ xK :=
  CzInv.mem_cz hP (by norm_num) (by norm_num)

theorem card_cent_c1K (hP : Nat.card ↥P1408 = 177408000) :
    Nat.card ↥(xK ⊓ centralizer ({c1K} : Set (Equiv.Perm (Fin 1408)))) = 384 := by
  have h := card_cent_c1' hP
  rw [(named_facts hP).2.2.2.2.1] at h
  exact h

theorem inv_class_at (hP : Nat.card ↥P1408 = 177408000) {i j : Nat} (hi : i < 1280) (hj : j < 24)
    (hsq : isBase (pt (T0 i) (pt (T1 j) (pt (T0 i) (pt (T1 j) 0))))
      (pt (T0 i) (pt (T1 j) (pt (T0 i) (pt (T1 j) 1)))) 0 1 = true)
    (hne' : (!isBase (pt (T0 i) (pt (T1 j) 0)) (pt (T0 i) (pt (T1 j) 1)) 0 1) = true) :
    ∃ h ∈ xK, t0P i * t1P j * h = h * CzInv.repE (Nat.pred (fd (CzInv.W i) (Nat.mul 3 j))) := by
  have hne : isBase (pt (T0 i) (pt (T1 j) 0)) (pt (T0 i) (pt (T1 j) 1)) 0 1 = false := by
    simpa using hne'
  have hg := CzInv.mem_cz hP hi hj
  have hc := CzInv.cell_ok hi hj
  unfold CzInv.cellK at hc
  simp only [strictB_app] at hc
  rw [hsq, hne] at hc
  rcases mkIf hc with ⟨-, hX⟩ | ⟨-, hX⟩
  · exact absurd hX Bool.false_ne_true
  rcases mkIf hX with ⟨-, hX⟩ | ⟨-, hK⟩
  · exact absurd hX Bool.false_ne_true
  obtain ⟨hi', hj', hq, hq', e0, e1⟩ := CzInv.conjK_parts hK
  refine ⟨_, CzInv.mem_cz hP hi' hj', ?_⟩
  unfold CzInv.cjAt at e0 e1
  have g0 := Nat.eq_of_beq_eq_true e0
  have g1 := Nat.eq_of_beq_eq_true e1
  rw [CzInv.ev_mul hi hj hi' hj' (by norm_num), CzInv.ev_mul hi' hj' hq hq' (by norm_num)] at g0
  rw [CzInv.ev_mul hi hj hi' hj' (by norm_num), CzInv.ev_mul hi' hj' hq hq' (by norm_num)] at g1
  exact eq_of_base hP (mul_mem hg (CzInv.mem_cz hP hi' hj')) (mul_mem (CzInv.mem_cz hP hi' hj')
    (CzInv.mem_cz hP hq hq')) (Fin.ext g0) (Fin.ext g1)

theorem rep_wit_at {c : Nat} (h5 : 5 ≤ c) (h12 : c < 12) :
    ∃ g ∈ P1408, CzInv.repE c = g * CzInv.namedE (CzInv.witT.getD (c - 5) 0) * g⁻¹ := by
  have h0 := CzInv.rep_wit_ok
  unfold CzInv.repWitK at h0
  have h := allN_spec h0 (c - 5) (by omega)
  have e : Nat.add (c - 5) 5 = c := by
    simp only [Nat.add_eq]
    omega
  rw [e] at h
  obtain ⟨hq, hq', ht0, ht5, hall, he⟩ := CzInv.witK_parts h
  have hT := repC_pc (t0P_spec hq).2 (t1P_spec hq').2
  obtain ⟨g, hgP, hg⟩ := CzInv.repC_conjW (CzInv.repC_named ht0 ht5) _ hall
  rw [← he] at hg
  exact ⟨g, hgP, eq_of_repC hT hg⟩

theorem eq_t01 (hP : Nat.card ↥P1408 = 177408000) {X i j : Nat} {g : Equiv.Perm (Fin 1408)}
    (hi : i < 1280) (hj : j < 24) (hX : RepC X g) (hg : g ∈ xK)
    (h0 : Nat.beq (pt X 0) (pt (T0 i) (pt (T1 j) 0)) = true)
    (h1 : Nat.beq (pt X 1) (pt (T0 i) (pt (T1 j) 1)) = true) : g = t0P i * t1P j :=
  eq_of_base hP hg (CzInv.mem_cz hP hi hj)
    (Fin.ext ((repC_pt hX (by norm_num)).symm.trans
      ((Nat.eq_of_beq_eq_true h0).trans (ev_eq hi hj (by norm_num)))))
    (Fin.ext ((repC_pt hX (by norm_num)).symm.trans
      ((Nat.eq_of_beq_eq_true h1).trans (ev_eq hi hj (by norm_num)))))

theorem elemB_mem_xK (hP : Nat.card ↥P1408 = 177408000) : elemB ∈ xK :=
  rK_le hP (named_facts hP).2.2.1

theorem elemA_mem_xK : elemA ∈ xK :=
  mem_inf.2 ⟨elemA_mem, mem_centralizer_singleton_iff.2 (basic_ab.2.2.1 _ elemZ_mem)⟩

theorem elemZ_mem_xK : elemZ ∈ xK :=
  mem_inf.2 ⟨elemZ_mem, mem_centralizer_singleton_iff.2 rfl⟩

theorem conj_conj {g h r y k : Equiv.Perm (Fin 1408)} (hh : h ∈ P1408) (hk : k ∈ P1408)
    (e : g * h = h * r) (er : r = k * y * k⁻¹) : g ∈ 𝒞 P1408 y :=
  CFSG.Sporadic.SmallOddCore.mem_conjClass.2 ⟨h * k, mul_mem hh hk, by
    rw [← mul_inv_cancel_right g h, e, er]
    group⟩

theorem azb_conj (hP : Nat.card ↥P1408 = 177408000) : elemA * elemZ * elemB ∈ 𝒞 P1408 elemB := by
  have hX : RepC (pc (pc (WK wordA) (WK wordZ)) (WK wordB)) (elemA * elemZ * elemB) :=
    repC_pc (repC_pc (repC_word (by decide)) (repC_word (by decide))) (repC_word (by decide))
  have e := eq_t01 hP (i := 728) (j := 20) (by norm_num) (by norm_num) hX
    (mul_mem (mul_mem elemA_mem_xK elemZ_mem_xK) (elemB_mem_xK hP)) (by quickRfl) (by quickRfl)
  obtain ⟨h, hh, eh⟩ := inv_class_at hP (i := 728) (j := 20) (by norm_num) (by norm_num)
    (by quickRfl) (by quickRfl)
  have ec : Nat.beq (fd (CzInv.W 728) (Nat.mul 3 20)) 4 = true := by quickRfl
  have ep : Nat.pred 4 = 3 := rfl
  rw [Nat.eq_of_beq_eq_true ec, ep] at eh
  obtain ⟨-, -, e3⟩ := CzInv.named_eq hP (c := 3) (by norm_num)
  have hb : CzInv.namedA 3 = elemB := by simp [CzInv.namedA, CzInv.namedE]
  rw [e]
  exact conj_conj hh.1 (one_mem _) eh (by rw [e3, hb]; group)

theorem repE_ten : CzInv.repE 10 = c1K := by
  have e0 : Nat.beq (fd (CzInv.R 10) 0) 817 = true := by quickRfl
  have e1 : Nat.beq (fd (CzInv.R 10) 1) 0 = true := by quickRfl
  unfold CzInv.repE
  rw [Nat.eq_of_beq_eq_true e0, Nat.eq_of_beq_eq_true e1]

theorem c1_conj : c1K ∈ 𝒞 P1408 elemB := by
  obtain ⟨g, hg, e⟩ := rep_wit_at (c := 10) (by norm_num) (by norm_num)
  have ht : CzInv.namedE (CzInv.witT.getD (10 - 5) 0) = elemB := by
    simp [CzInv.witT, CzInv.namedE]
  rw [ht, repE_ten] at e
  exact CFSG.Sporadic.SmallOddCore.mem_conjClass.2 ⟨g, hg, e⟩

theorem azc1_conj (hP : Nat.card ↥P1408 = 177408000) : elemA * elemZ * c1K ∈ 𝒞 P1408 elemZ₁ := by
  have hX : RepC (pc (pc (WK wordA) (WK wordZ)) (pc (T0 817) (T1 0))) (elemA * elemZ * c1K) :=
    repC_pc (repC_pc (repC_word (by decide)) (repC_word (by decide)))
      (repC_pc (t0P_spec (i := 817) (by norm_num)).2 (t1P_spec (j := 0) (by norm_num)).2)
  have e := eq_t01 hP (i := 776) (j := 0) (by norm_num) (by norm_num) hX
    (mul_mem (mul_mem elemA_mem_xK elemZ_mem_xK) (c1K_mem hP)) (by quickRfl) (by quickRfl)
  obtain ⟨h, hh, eh⟩ := inv_class_at hP (i := 776) (j := 0) (by norm_num) (by norm_num)
    (by quickRfl) (by quickRfl)
  have ec : Nat.beq (fd (CzInv.W 776) (Nat.mul 3 0)) 10 = true := by quickRfl
  have ep : Nat.pred 10 = 9 := rfl
  rw [Nat.eq_of_beq_eq_true ec, ep] at eh
  obtain ⟨g, hg, e9⟩ := rep_wit_at (c := 9) (by norm_num) (by norm_num)
  have ht : CzInv.namedE (CzInv.witT.getD (9 - 5) 0) = elemZ₁ := by
    simp [CzInv.witT, CzInv.namedE]
  rw [ht] at e9
  rw [e]
  exact conj_conj hh.1 hg eh e9

theorem namedA_conj_b (hP : Nat.card ↥P1408 = 177408000) {t : Nat} (ht : t < 5)
    (h : CzInv.namedA t ∈ 𝒞 P1408 elemB) : t = 3 := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := CzInv.classes_distinctK hP
  have back : ∀ x : Equiv.Perm (Fin 1408), x ∈ 𝒞 P1408 elemB → elemB ∈ 𝒞 P1408 x := by
    intro x hx
    rw [CzInv.conjClass_eq_of_mem hx]
    exact CFSG.Sporadic.SmallOddCore.self_mem_conjClass _ _
  interval_cases t
  · exfalso
    have e : CzInv.namedA 0 = elemA := by simp [CzInv.namedA]
    rw [e] at h
    obtain ⟨k, hk, hk'⟩ := CFSG.Sporadic.SmallOddCore.mem_conjClass.1 h
    apply d3
    have eb : elemB = k⁻¹ * elemA * k := by rw [hk']; group
    rw [eb, mul_assoc, basic_ab.2.2.1 k hk, inv_mul_cancel_left]
  · exfalso
    have e : CzInv.namedA 1 = elemZ := by simp [CzInv.namedA, CzInv.namedE]
    rw [e] at h
    exact d6 (back _ h)
  · exfalso
    have e : CzInv.namedA 2 = elemA * elemZ := by simp [CzInv.namedA, CzInv.namedE]
    rw [e] at h
    exact d8 (back _ h)
  · rfl
  · exfalso
    have e : CzInv.namedA 4 = elemZ₁ := by simp [CzInv.namedA, CzInv.namedE]
    rw [e] at h
    exact d10 h

theorem b_class_of (hP : Nat.card ↥P1408 = 177408000) {g : Equiv.Perm (Fin 1408)} (hg : g ∈ xK)
    (hb : g ∈ 𝒞 P1408 elemB) :
    g ∈ 𝒞 xK elemB ∨ g ∈ 𝒞 xK c1K := by
  obtain ⟨k, hk, rfl⟩ := CFSG.Sporadic.SmallOddCore.mem_conjClass.1 hb
  have hb2 : elemB * elemB = 1 := mul_self_eq_one_of_orderOf_eq_two basic_ab.2.1
  have h2 : k * elemB * k⁻¹ * (k * elemB * k⁻¹) = 1 := by
    calc k * elemB * k⁻¹ * (k * elemB * k⁻¹) = k * (elemB * elemB) * k⁻¹ := by group
      _ = 1 := by rw [hb2]; group
  have h1 : k * elemB * k⁻¹ ≠ 1 := by
    intro e
    have e' : elemB = 1 := by
      calc elemB = k⁻¹ * (k * elemB * k⁻¹) * k := by group
        _ = 1 := by rw [e]; group
    have ho := basic_ab.2.1
    rw [e', orderOf_one] at ho
    exact absurd ho (by norm_num)
  obtain ⟨c, hc, -, -, h, hh, e⟩ := CzInv.inv_conj hP hg h2 h1
  have hgx : k * elemB * k⁻¹ = h * CzInv.repE c * h⁻¹ := by rw [← e]; group
  have hrep : CzInv.repE c ∈ 𝒞 P1408 elemB :=
    CFSG.Sporadic.SmallOddCore.mem_conjClass.2 ⟨h⁻¹ * k, mul_mem (inv_mem hh.1) hk, by
      calc CzInv.repE c = h⁻¹ * (h * CzInv.repE c * h⁻¹) * h := by group
        _ = h⁻¹ * (k * elemB * k⁻¹) * h := by rw [hgx]
        _ = _ := by group⟩
  by_cases hc5 : c < 5
  · have e3 := (CzInv.named_eq hP hc5).2.2
    rw [e3] at hrep
    have hc3 := namedA_conj_b hP hc5 hrep
    subst hc3
    have hb : CzInv.namedA 3 = elemB := by simp [CzInv.namedA, CzInv.namedE]
    rw [e3, hb] at hgx
    exact Or.inl (CFSG.Sporadic.SmallOddCore.mem_conjClass.2 ⟨h, hh, hgx⟩)
  · obtain ⟨g', hg', e'⟩ := rep_wit_at (c := c) (by omega) hc
    have hm : CzInv.namedE (CzInv.witT.getD (c - 5) 0) ∈ 𝒞 P1408 elemB := by
      obtain ⟨k', hk', ek'⟩ := CFSG.Sporadic.SmallOddCore.mem_conjClass.1 hrep
      refine CFSG.Sporadic.SmallOddCore.mem_conjClass.2 ⟨g'⁻¹ * k', mul_mem (inv_mem hg') hk', ?_⟩
      calc CzInv.namedE (CzInv.witT.getD (c - 5) 0)
          = g'⁻¹ * (g' * CzInv.namedE (CzInv.witT.getD (c - 5) 0) * g'⁻¹) * g' := by group
        _ = g'⁻¹ * (k' * elemB * k'⁻¹) * g' := by rw [← e', ← ek']
        _ = _ := by group
    have key : ∀ t, 0 < t → t < 5 → CzInv.namedE t ∈ 𝒞 P1408 elemB → t = 3 := by
      intro t h0 h5 hm'
      have e0 : CzInv.namedA t = CzInv.namedE t := by
        simp [CzInv.namedA, Nat.pos_iff_ne_zero.1 h0]
      exact namedA_conj_b hP h5 (by rw [e0]; exact hm')
    have ht := key _ (by interval_cases c <;> decide) (by interval_cases c <;> decide) hm
    have hc10 : c = 10 := by
      interval_cases c <;> first | rfl | exact absurd ht (by decide)
    subst hc10
    rw [repE_ten] at hgx
    exact Or.inr (CFSG.Sporadic.SmallOddCore.mem_conjClass.2 ⟨h, hh, hgx⟩)

theorem base_perm (hP : Nat.card ↥P1408 = 177408000) :
    {g | g ∈ 𝒞 P1408 elemB ∧ g ∈ xK}.ncard = 120 := by
  have hXc : Nat.card ↥xK = 30720 := by
    have e : xK = czC := (czT_eq hP).1.symm
    rw [e]
    exact (czT_eq hP).2
  have hS : {g | g ∈ 𝒞 P1408 elemB ∧ g ∈ xK} = 𝒞 xK elemB ∪ 𝒞 xK c1K := by
    ext g
    constructor
    · rintro ⟨hb, hg⟩
      exact b_class_of hP hg hb
    · rintro (hg | hg)
      · obtain ⟨k, hk, rfl⟩ := CFSG.Sporadic.SmallOddCore.mem_conjClass.1 hg
        exact ⟨CFSG.Sporadic.SmallOddCore.mem_conjClass.2 ⟨k, hk.1, rfl⟩,
          mul_mem (mul_mem hk (elemB_mem_xK hP)) (inv_mem hk)⟩
      · obtain ⟨k, hk, rfl⟩ := CFSG.Sporadic.SmallOddCore.mem_conjClass.1 hg
        obtain ⟨k', hk', e'⟩ := CFSG.Sporadic.SmallOddCore.mem_conjClass.1 c1_conj
        refine ⟨CFSG.Sporadic.SmallOddCore.mem_conjClass.2 ⟨k * k', mul_mem hk.1 hk', ?_⟩,
          mul_mem (mul_mem hk (c1K_mem hP)) (inv_mem hk)⟩
        rw [e']
        group
  have h0 := CFSG.Sporadic.SmallOddCore.ncard_conjClass_mul_card xK elemB
  have h1 := CFSG.Sporadic.SmallOddCore.ncard_conjClass_mul_card xK c1K
  have s0 : Nat.card ↥(xK ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408)))) = 768 :=
    card_cent_b hP
  have s1 : Nat.card ↥(xK ⊓ centralizer ({c1K} : Set (Equiv.Perm (Fin 1408)))) = 384 :=
    card_cent_c1K hP
  rw [s0, hXc] at h0
  rw [s1, hXc] at h1
  have hdisj : Disjoint (𝒞 xK elemB) (𝒞 xK c1K) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    obtain ⟨k, hk, rfl⟩ := CFSG.Sporadic.SmallOddCore.mem_conjClass.1 hx
    obtain ⟨k', hk', e⟩ := CFSG.Sporadic.SmallOddCore.mem_conjClass.1 hx'
    have ec : c1K = (k'⁻¹ * k) * elemB * (k'⁻¹ * k)⁻¹ := by
      calc c1K = k'⁻¹ * (k' * c1K * k'⁻¹) * k' := by group
        _ = k'⁻¹ * (k * elemB * k⁻¹) * k' := by rw [← e]
        _ = _ := by group
    obtain ⟨φ⟩ := nonempty_mulEquiv_inf_Gx_of_conj (K := xK) (c := elemB)
      (mul_mem (inv_mem hk') hk)
    have hc := Nat.card_congr φ.toEquiv
    rw [← ec] at hc
    have hc' : Nat.card ↥(xK ⊓ centralizer ({c1K} : Set (Equiv.Perm (Fin 1408)))) =
        Nat.card ↥(xK ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408)))) := hc
    rw [s0, s1] at hc'
    exact absurd hc' (by norm_num)
  rw [hS, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  omega

theorem map_Gx_P (c : ↥P1408) :
    (Gx c).map P1408.subtype = P1408 ⊓ centralizer ({(c : Equiv.Perm (Fin 1408))} : Set _) := by
  rw [map_Gx_of_injective P1408.subtype_injective, Subgroup.range_subtype, inf_comm]
  all_goals rfl

theorem map_X : (Gx pZ).map P1408.subtype = xK := map_Gx_P pZ

theorem map_D (hP : Nat.card ↥P1408 = 177408000) :
    (derivedOf (Gx pZ)).map P1408.subtype = dK := by
  rw [← derivedOf_map_of_injective P1408.subtype_injective, map_X, dK_eq hP]

theorem map_R (hP : Nat.card ↥P1408 = 177408000) :
    (wordSubgroupP nWords1).map P1408.subtype = rK := by
  rw [wordSubgroupP, Subgroup.map_subgroupOf_eq_of_le (wordSubgroup_le _), rK_eq hP]

theorem map_XC (c : ↥P1408) :
    (Gx pZ ⊓ Gx c).map P1408.subtype =
      xK ⊓ centralizer ({(c : Equiv.Perm (Fin 1408))} : Set _) := by
  rw [Subgroup.map_inf_eq _ _ _ P1408.subtype_injective, map_X, map_Gx_P, ← inf_assoc,
    inf_eq_left.2 (inf_le_left : xK ≤ P1408)]

theorem map_inf_Gx_P' (A : Subgroup ↥P1408) (σ : ↥P1408) :
    (A ⊓ Gx σ).map P1408.subtype =
      A.map P1408.subtype ⊓ centralizer ({(σ : Equiv.Perm (Fin 1408))} : Set _) := by
  rw [Subgroup.map_inf_eq _ _ _ P1408.subtype_injective, map_Gx_P, ← inf_assoc,
    inf_eq_left.2 (Subgroup.map_subtype_le A)]

theorem cardP (S : Subgroup ↥P1408) : Nat.card ↥S = Nat.card ↥(S.map P1408.subtype) :=
  (Subgroup.card_map_of_injective P1408.subtype_injective).symm

theorem memP {S : Subgroup ↥P1408} {T : Subgroup (Equiv.Perm (Fin 1408))}
    (h : S.map P1408.subtype = T) {x : ↥P1408} : x ∈ S ↔ (x : Equiv.Perm (Fin 1408)) ∈ T := by
  rw [← h]
  exact (Subgroup.mem_map_iff_mem P1408.subtype_injective).symm

theorem isElemTwo_of_sq {E : Subgroup (Equiv.Perm (Fin 1408))} {n : ℕ}
    (hsq : ∀ x ∈ E, x * x = 1) (hc : Nat.card ↥E = 2 ^ n) : IsElemTwo n E :=
  ⟨⟨isMulCommutative_of_sq hsq, fun x hx => by rw [pow_two]; exact hsq x hx⟩, hc⟩

theorem tabXFacts_K (hP : Nat.card ↥P1408 = 177408000) :
    TabXFacts pA pZ pB pZ₁ (wordSubgroupP nWords1) := by
  have inj := P1408.subtype_injective
  have hX := map_X
  have hD := map_D hP
  have hR := map_R hP
  have hZmap : (centerOf (derivedOf (Gx pZ))).map P1408.subtype = centerOf dK := by
    rw [← centerOf_map_of_injective inj, hD]
  obtain ⟨-, -, hbR, -, fc, hc1R, m₁, hm₁, m₂, hm₂, k₁, k₂, hcomm⟩ := named_facts hP
  have hc1R' : c1K ∉ rK := by
    rw [fc] at hc1R
    exact hc1R
  rw [fc] at k₁ k₂
  let pc1 : ↥P1408 := ⟨c1K, (c1K_mem hP).1⟩
  have hsq1 : ∀ x ∈ xK ⊓ centralizer ({c1K} : Set (Equiv.Perm (Fin 1408))) ⊓ rK, x * x = 1 := by
    have h := sq_c1R hP
    rw [fc] at h
    exact h
  obtain ⟨a1, b1, c1⟩ := card_c1 hP
  rw [fc] at a1 b1 c1
  obtain ⟨a0, b0, c0⟩ := card_c0 hP
  obtain ⟨-, sm, so, tm, st, -⟩ := sig_facts hP
  let pσ : ↥P1408 := ⟨elC (nm 60), sm.1⟩
  let pt' : ↥P1408 := ⟨elC (nm 61), tm.1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ⟨![pB, pc1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨⟨m₁, (dK_le hP hm₁).1⟩, ?_, ⟨m₂, (dK_le hP hm₂).1⟩, ?_, ?_⟩, pσ, ?_, ?_, pt', ?_, ?_, ?_,
    ?_⟩⟩
  · intro x hx
    exact (memP hX).2 (rK_le hP ((memP hR).1 hx))
  · rw [cardP, hR]
    exact (rk_facts hP).2
  · have himg : Subtype.val '' {c : ↥P1408 | IsConj pB c ∧ c ∈ Gx pZ} =
        {g | g ∈ 𝒞 P1408 elemB ∧ g ∈ xK} := by
      ext g
      constructor
      · rintro ⟨c, ⟨hc, hz⟩, rfl⟩
        exact ⟨(isConj_iff_mem_conjClass P1408 pB c).1 hc, (memP hX).1 hz⟩
      · rintro ⟨hg, hgX⟩
        exact ⟨⟨g, hgX.1⟩, ⟨(isConj_iff_mem_conjClass P1408 pB ⟨g, hgX.1⟩).2 hg,
          (memP hX).2 hgX⟩, rfl⟩
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, himg]
    exact base_perm hP
  · rw [cardP, hD]
    exact (dk_facts hP).2
  · rw [cardP, Subgroup.map_inf_eq _ _ _ inj, hD, hR]
    exact card_DR hP
  · rw [cardP, Subgroup.map_sup, hD, hR]
    exact card_DRs hP
  · obtain ⟨s1, s2, n1, n2, n12⟩ := quot_parts hP
    have u0 := uK_mem (l := 0) (by norm_num)
    have u1 := uK_mem (l := 1) (by norm_num)
    exact ⟨⟨uK 0, u0.1⟩, (memP hX).2 u0, ⟨uK 1, u1.1⟩, (memP hX).2 u1, (memP hD).2 s1,
      (memP hD).2 s2, fun h => n1 ((memP hD).1 h), fun h => n2 ((memP hD).1 h),
      fun h => n12 ((memP hD).1 h)⟩
  · apply Subgroup.map_injective inj
    rw [hZmap, ← centerOf_map_of_injective inj, Subgroup.map_inf_eq _ _ _ inj, hD, hR]
    exact zD_eq hP
  · obtain ⟨e⟩ := zD_iso hP
    exact ⟨((centerOf (derivedOf (Gx pZ))).equivMapOfInjective P1408.subtype inj).trans
      ((MulEquiv.subgroupCongr hZmap).trans e)⟩
  · intro i
    fin_cases i
    · refine ⟨IsConj.refl _, (memP hX).2 (elemB_mem_xK hP), Or.inr (Or.inr ?_)⟩
      exact (isConj_iff_mem_conjClass P1408 pB _).2 (azb_conj hP)
    · exact ⟨(isConj_iff_mem_conjClass P1408 pB pc1).2 c1_conj, (memP hX).2 (c1K_mem hP),
        Or.inr ((isConj_iff_mem_conjClass P1408 pZ₁ _).2 (azc1_conj hP))⟩
  · intro i
    fin_cases i
    · change Nat.card ↥(Gx pZ ⊓ Gx pB) = 768
      rw [cardP, map_XC]
      exact card_cent_b hP
    · change Nat.card ↥(Gx pZ ⊓ Gx pc1) = 384
      rw [cardP, map_XC]
      exact card_cent_c1K hP
  · exact (memP hR).2 hbR
  · change Nat.card ↥(Gx pZ ⊓ Gx pB ⊓ wordSubgroupP nWords1) = 2 ^ 7
    rw [cardP, Subgroup.map_inf_eq _ _ _ inj, map_XC, hR]
    exact a0.trans (by norm_num)
  · change Nat.card ↥(Gx pZ ⊓ Gx pB ⊓ wordSubgroupP nWords1 ⊓ derivedOf (Gx pZ)) = 2 ^ 6
    rw [cardP, Subgroup.map_inf_eq _ _ _ inj, Subgroup.map_inf_eq _ _ _ inj, map_XC, hR, hD]
    exact b0.trans (by norm_num)
  · change Nat.card ↥(Gx pZ ⊓ Gx pB ⊓ derivedOf (Gx pZ)) = 2 ^ 6 * 3
    rw [cardP, Subgroup.map_inf_eq _ _ _ inj, map_XC, hD]
    exact c0.trans (by norm_num)
  · change pc1 ∉ wordSubgroupP nWords1
    exact fun h => hc1R' ((memP hR).1 h)
  · change IsElemTwo 5 (Gx pZ ⊓ Gx pc1 ⊓ wordSubgroupP nWords1)
    refine isElemTwo_of_map inj ?_
    rw [Subgroup.map_inf_eq _ _ _ inj, map_XC, hR]
    exact isElemTwo_of_sq hsq1 (a1.trans (by norm_num))
  · change IsElemTwo 4 (Gx pZ ⊓ Gx pc1 ⊓ wordSubgroupP nWords1 ⊓ derivedOf (Gx pZ))
    refine isElemTwo_of_map inj ?_
    rw [Subgroup.map_inf_eq _ _ _ inj, Subgroup.map_inf_eq _ _ _ inj, map_XC, hR, hD]
    exact isElemTwo_of_sq (fun x hx => hsq1 x hx.1) (b1.trans (by norm_num))
  · change Nat.card ↥(Gx pZ ⊓ Gx pc1 ⊓ derivedOf (Gx pZ)) = 2 ^ 5 * 3
    rw [cardP, Subgroup.map_inf_eq _ _ _ inj, map_XC, hD]
    exact c1.trans (by norm_num)
  · have hS : (Gx pZ ⊓ Gx pc1 ⊓ derivedOf (Gx pZ)).map P1408.subtype =
        xK ⊓ centralizer ({c1K} : Set (Equiv.Perm (Fin 1408))) ⊓ dK := by
      rw [Subgroup.map_inf_eq _ _ _ inj, map_XC, hD]
    exact (memP hS).2 ⟨⟨dK_le hP hm₁, mem_centralizer_singleton_iff.2 k₁⟩, hm₁⟩
  · have hS : (Gx pZ ⊓ Gx pc1 ⊓ derivedOf (Gx pZ)).map P1408.subtype =
        xK ⊓ centralizer ({c1K} : Set (Equiv.Perm (Fin 1408))) ⊓ dK := by
      rw [Subgroup.map_inf_eq _ _ _ inj, map_XC, hD]
    exact (memP hS).2 ⟨⟨dK_le hP hm₂, mem_centralizer_singleton_iff.2 k₂⟩, hm₂⟩
  · exact fun h => hcomm ((memP hR).1 h)
  · exact (memP hX).2 sm
  · rw [← Subgroup.orderOf_coe]
    exact so
  · exact (memP hX).2 tm
  · exact Subtype.ext st
  · change wordSubgroupP nWords1 ⊓ Gx pσ =
      closure ((centerOf (derivedOf (Gx pZ)) : Set ↥P1408) ∪ {pB})
    apply Subgroup.map_injective inj
    rw [MonoidHom.map_closure, Set.image_union, Set.image_singleton, ← Subgroup.coe_map, hZmap,
      map_inf_Gx_P', hR]
    exact hCR_K hP
  · apply Subgroup.map_injective inj
    rw [map_inf_Gx_P', Subgroup.map_inf_eq _ _ _ inj, hD, hR, hZmap]
    exact hCD_K hP

end CFSG.KD.HN1408.TabX

end
