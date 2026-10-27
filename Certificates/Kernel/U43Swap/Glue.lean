module

public import Certificates.Kernel.U43Mod.Glue
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5XSwCen
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.EvenSporadicStandard.Reduction
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Contra
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.OutU43Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Stages
public import CFSG.Sporadic.Schreier.ONArrayDatum

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CertificateChecks.KernelU43Swap

open CFSG.OddStandard.SmallF3.Omega CFSG.LieType.Multipliers.U43 CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Quasithin.H13.U43 CFSG.KGroups.U43 Certificates.Asc82Swap
  CFSG.KS.U43Mod CertificateChecks.KernelU43Mod

theorem natAny_iff (n : ℕ) (f : (i : ℕ) → i < n → Bool) :
    Nat.any n f = true ↔ ∃ i, ∃ h : i < n, f i h = true := by
  rw [Nat.any_eq_finRange_any, List.any_eq_true]
  constructor
  · rintro ⟨x, -, hx⟩
    exact ⟨x.1, x.2, hx⟩
  · rintro ⟨i, hi, hf⟩
    exact ⟨⟨i, hi⟩, List.mem_finRange _, hf⟩

theorem map_conjArr_get {O Oi O1 : Array (Array ℕ)} {a : ℕ} (ha : a < O1.size) :
    (O1.map (conjArr 820 O Oi))[a]! = conjArr 820 O Oi O1[a]! := by
  rw [getElem!_pos _ a (by simpa using ha), Array.getElem_map, getElem!_pos O1 a ha]

theorem size_filter_ncard {α : Type*} [Inhabited α] (T : Array α) (p : α → Bool) :
    (T.filter p).size = ({i : ℕ | i < T.size ∧ p T[i]! = true} : Set ℕ).ncard := by
  have hmap : (List.range T.size).map (fun k => T[k]!) = T.toList := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range]
      rw [getElem!_pos T i (by simpa using h1)]
      simp
  have hset : ({i : ℕ | i < T.size ∧ p T[i]! = true} : Set ℕ) =
      ↑((Finset.range T.size).filter fun d => p T[d]! = true) := by
    ext d
    simp
  rw [← Array.countP_eq_size_filter, ← Array.countP_toList, List.countP_eq_length_filter, ← hmap,
    List.filter_map, List.length_map, hset, Set.ncard_coe_finset]
  simp only [Finset.card, Finset.filter_val, Finset.range_val, Multiset.range, Multiset.filter_coe,
    Multiset.coe_card]
  apply congrArg List.length
  apply List.filter_congr
  intro x _
  simp

theorem invsOK_cover {L : Array (Array ℕ)} {S : Set X₀} (h : SwCover L S) :
    invsOK 820 L (invArrs 820 L) = true :=
  invsOK_invArrs fun i hi => by
    obtain ⟨s, -, hs⟩ := h.1 i hi
    exact ⟨_, hs⟩


theorem swap_ok (hT : SwTables) : swapTCheck 820 tabA tabB = true := by
  have hL : SwCover (elemList 820 tabA tabB) (SwC : Set X₀) := sw_elemList_enum.cover
  have hO : SwCover (oddList 820 (elemList 820 tabA tabB)) {o | o ∈ SwC ∧ Odd (orderOf o)} :=
    sw_oddList_cover
  have hO1 := sw_oddNe_cover
  have hLi := invsOK_cover hL
  have hOi := invsOK_cover hO
  unfold swapTCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨hLi, hOi⟩, (eqA_iff (rep_compA rep_A rep_A) rep_idA).2 CP0_sq⟩, ?_⟩
  set L := elemList 820 tabA tabB
  set O := oddList 820 L
  set O1 := oddNe 820 O (idA 820)
  rw [swapTAux, allLt_iff]
  intro i hi
  rw [allLt_iff]
  intro j hj
  obtain ⟨g₁, ⟨hg₁C, hg₁o, hg₁n⟩, hr₁⟩ := hO1.1 i hi
  obtain ⟨g₂, ⟨hg₂C, hg₂o, hg₂n⟩, hr₂⟩ := hO1.1 j hj
  rw [map_conjArr_get hi, map_conjArr_get hj, Bool.or_eq_true]
  by_cases hm : (cenB 820 (conjArr 820 O (invArrs 820 O) O1[j]!) O1[i]! &&
      cenB 820 (conjArr 820 O (invArrs 820 O) O1[i]!) O1[j]!) = true
  · right
    rw [Bool.and_eq_true] at hm
    obtain ⟨hT1, c, hc, hX1, hX2⟩ := hT g₁ hg₁C g₂ hg₂C hg₁o hg₂o hg₁n hg₂n
      ⟨hg₁C, (sw_cenB_iff hO hOi hr₂ hr₁).1 hm.1⟩ ⟨hg₂C, (sw_cenB_iff hO hOi hr₁ hr₂).1 hm.2⟩
    rw [Bool.and_eq_true]
    constructor
    · rw [t1Check, allLt_iff]
      intro k hk
      obtain ⟨h, hhC, hrh⟩ := hL.1 k hk
      by_cases hb : (cenB 820 (conjArr 820 O (invArrs 820 O) O1[i]!) L[k]! &&
          cenB 820 (conjArr 820 O (invArrs 820 O) O1[j]!) L[k]!) = true
      · rw [Bool.and_eq_true] at hb
        rcases hT1 h ⟨hhC, (sw_cenB_iff hO hOi hr₁ hrh).1 hb.1⟩
            ⟨hhC, (sw_cenB_iff hO hOi hr₂ hrh).1 hb.2⟩ with rfl | rfl
        · rw [(eqA_iff hrh rep_idA).2 (map_one psi)]
          simp
        · rw [(eqA_iff hrh rep_tabA).2 rfl]
          simp
      · rw [Bool.not_eq_true] at hb
        rw [hb]
        rfl
    · rw [t2Check, natAny_iff]
      obtain ⟨kc, hkc, hrc⟩ := hL.2 c hc
      have hrci : Rep 820 (invArrs 820 L)[kc]! (psi c⁻¹) := sw_rep_inv hLi hkc hrc
      refine ⟨kc, hkc, ?_⟩
      rw [Bool.and_eq_true, Array.all_eq_true', Array.all_eq_true']
      constructor
      · intro o' ho'
        obtain ⟨ho'O, hcen⟩ := Array.mem_filter.mp ho'
        obtain ⟨k, hk, hke⟩ := Array.mem_iff_getElem.mp ho'O
        obtain ⟨o, ⟨hoC, hoOdd⟩, hro⟩ := hO.1 k hk
        rw [getElem!_pos O k hk, hke] at hro
        have hoCen := (sw_cenB_iff hO hOi hr₂ hro).1 hcen
        have hrep : Rep 820 (compA 820 (invArrs 820 L)[kc]! (compA 820 o' L[kc]!))
            (psi (c⁻¹ * o * c)) := by
          rw [map_mul, map_mul, mul_assoc]
          exact rep_compA hrci (rep_compA hro hrc)
        exact (sw_cenB_iff hO hOi hr₁ hrep).2 (hX1 o hoC hoOdd ⟨hoC, hoCen⟩).2
      · intro o' ho'
        obtain ⟨ho'O, hcen⟩ := Array.mem_filter.mp ho'
        obtain ⟨k, hk, hke⟩ := Array.mem_iff_getElem.mp ho'O
        obtain ⟨o, ⟨hoC, hoOdd⟩, hro⟩ := hO.1 k hk
        rw [getElem!_pos O k hk, hke] at hro
        have hoCen := (sw_cenB_iff hO hOi hr₁ hro).1 hcen
        have hrep : Rep 820 (compA 820 L[kc]! (compA 820 o' (invArrs 820 L)[kc]!))
            (psi (c * o * c⁻¹)) := by
          rw [map_mul, map_mul, mul_assoc]
          exact rep_compA hrc (rep_compA hro hrci)
        exact (sw_cenB_iff hO hOi hr₂ hrep).2 (hX2 o hoC hoOdd ⟨hoC, hoCen⟩).2
  · left
    rw [Bool.not_eq_true] at hm
    rw [hm]
    rfl

theorem oddCent_ok (hK : ∀ y ∈ SwC, Odd (orderOf y) → y ≠ 1 →
    Nat.card ↥(SwC ⊓ Subgroup.centralizer ({y} : Set X₀)) % 16 ≠ 0) :
    oddCentCheck 820 tabA tabB = true := by
  obtain ⟨f, hf, hinj, himg⟩ := sw_elemList_enum
  have hO1 := sw_oddNe_cover
  unfold oddCentCheck oddCentAux
  simp only []
  set L := elemList 820 tabA tabB
  set O1 := oddNe 820 (oddList 820 L) (idA 820)
  rw [allLt_iff]
  intro a ha
  obtain ⟨y, ⟨hyC, hyo, hyn⟩, hry⟩ := hO1.1 a ha
  have hcomm : ∀ i (hi : i < L.size), commB 820 O1[a]! L[i]! = true ↔ y * f i = f i * y := by
    intro i hi
    rw [commB, eqA_iff (rep_compA hry (hf i hi)) (rep_compA (hf i hi) hry), ← map_mul, ← map_mul,
      psi_inj.eq_iff]
  have himage : f '' {i : ℕ | i < L.size ∧ commB 820 O1[a]! L[i]! = true} =
      (↑(SwC ⊓ Subgroup.centralizer ({y} : Set X₀)) : Set X₀) := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hx : f i ∈ f '' Set.Iio L.size := ⟨i, hi.1, rfl⟩
      rw [himg] at hx
      refine Subgroup.mem_inf.mpr ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      exact ((hcomm i hi.1).1 hi.2).symm
    · intro hx
      obtain ⟨hxC, hxc⟩ := Subgroup.mem_inf.mp hx
      have hx' : x ∈ f '' Set.Iio L.size := by rw [himg]; exact hxC
      obtain ⟨i, hi, rfl⟩ := hx'
      exact ⟨i, ⟨hi, (hcomm i hi).2 (Subgroup.mem_centralizer_singleton_iff.1 hxc).symm⟩, rfl⟩
  have hcard : (L.filter fun h => commB 820 O1[a]! h).size =
      Nat.card ↥(SwC ⊓ Subgroup.centralizer ({y} : Set X₀)) := by
    rw [size_filter_ncard, ← Set.InjOn.ncard_image (f := f) (hinj.mono fun i hi => hi.1), himage,
      ← Nat.card_coe_set_eq]
    rfl
  rw [bne_iff_ne, hcard]
  exact hK y hyC hyo hyn

end CertificateChecks.KernelU43Swap

end
