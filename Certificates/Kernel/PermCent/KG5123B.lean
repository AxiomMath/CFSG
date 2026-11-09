
module

public import Certificates.Data.Kernel.PermCent.KGrpC
public import CFSG.GH74.KGroups.L34AutInputs
import CFSG.Certificates.Kernel.PermCent.KGrpCSound

public section

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CFSG.Certificates.Kernel.PkCV.KGrp.K5123

open CFSG.GH74.KGroups CFSG.GH74.KGroups.L34 CFSG.Certificates.Kernel.PkEnum CFSG.Certificates
  CFSG.Sporadic.Schreier

theorem len_filter_drop_take {α : Type*} (l : List α) (p : α → Bool) (c : Nat) : ∀ m : Nat,
    (l.filter p).length =
      ((List.range m).map fun j => (((l.drop (j * c)).take c).filter p).length).sum +
        ((l.drop (m * c)).filter p).length
  | 0 => by simp
  | m + 1 => by
    rw [len_filter_drop_take l p c m, List.range_succ, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton, Nat.add_assoc]
    congr 1
    conv_lhs => rw [← List.take_append_drop c (l.drop (m * c))]
    rw [List.filter_append, List.length_append, List.drop_drop, Nat.add_one_mul]

theorem len_filter_blocks8 {α : Type*} (l : List α) (p q : α → Bool) (c : Nat)
    {n₀ n₁ n₂ n₃ n₄ n₅ n₆ n₇ n : Nat}
    (h₀ : (((l.drop (0 * c)).take c).filter fun y => q y && p y).length = n₀)
    (h₁ : (((l.drop (1 * c)).take c).filter fun y => q y && p y).length = n₁)
    (h₂ : (((l.drop (2 * c)).take c).filter fun y => q y && p y).length = n₂)
    (h₃ : (((l.drop (3 * c)).take c).filter fun y => q y && p y).length = n₃)
    (h₄ : (((l.drop (4 * c)).take c).filter fun y => q y && p y).length = n₄)
    (h₅ : (((l.drop (5 * c)).take c).filter fun y => q y && p y).length = n₅)
    (h₆ : (((l.drop (6 * c)).take c).filter fun y => q y && p y).length = n₆)
    (h₇ : ((l.drop (7 * c)).filter fun y => q y && p y).length = n₇)
    (hn : n₀ + n₁ + n₂ + n₃ + n₄ + n₅ + n₆ + n₇ = n) :
    ((l.filter q).filter p).length = n := by
  have hr : List.range 7 = [0, 1, 2, 3, 4, 5, 6] := rfl
  rw [List.filter_filter, List.filter_congr (fun y _ => Bool.and_comm (p y) (q y)),
    len_filter_drop_take l _ c 7, hr]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h₀, h₁, h₂, h₃, h₄, h₅,
    h₆, h₇]
  omega

theorem kOrd : orderIsC (cOf PA) 2 = true ∧ orderIsC (cOf PB) 4 = true ∧
    pairInvC ws (cOf PA) (cOf PB) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

theorem kNorm : normC QP (QA.original.toList.map cOf) (cOf PA) (cOf PB) = true := by
  decide +kernel

theorem kInv : ((elemsC QP).filter fun x => orderIsC x 2).length = 315 := by decide +kernel

@[expose] def pA315Word : Nat → Nat → List Bool
  | 0, _ => []
  | f + 1, c => if c ≤ 1 then [] else (c % 2 == 1) :: pA315Word f (c / 2)

@[expose] def pA315Codes : List Nat := [
    1, 3, 6, 7, 13, 14, 15, 26, 27, 29, 30, 53, 54, 55, 58, 59, 61, 106, 107, 109, 110, 117, 118,
    119, 122, 123, 213, 214, 215, 218, 219, 234, 235, 238, 245, 246, 247, 426, 427, 429, 430, 437,
    438, 439, 469, 470, 471, 477, 490, 491, 493, 494, 854, 855, 858, 859, 861, 874, 875, 877, 938,
    941, 942, 954, 955, 981, 982, 989, 1709, 1710, 1717, 1718, 1719, 1722, 1723, 1749, 1750, 1751,
    1754, 1882, 1883, 1885, 1909, 1910, 1911, 1962, 1965, 1978, 1979, 3418, 3419, 3421, 3434, 3437,
    3438, 3445, 3447, 3499, 3501, 3502, 3509, 3765, 3766, 3767, 3770, 3771, 3818, 3819, 3821, 3822,
    3930, 3931, 3957, 3958, 6837, 6838, 6839, 6843, 6869, 6874, 6877, 6890, 6891, 6998, 7002, 7005,
    7018, 7019, 7530, 7531, 7533, 7534, 7541, 7639, 7642, 7861, 7862, 7915, 7917, 13675, 13686,
    13687, 13739, 13749, 13754, 13755, 13781, 13782, 13783, 13997, 14005, 14010, 14037, 14038,
    14039, 15061, 15062, 15063, 15066, 15069, 15082, 15083, 15278, 15285, 15722, 15723, 15725,
    15831, 27350, 27351, 27479, 27498, 27499, 27511, 27562, 27563, 27565, 27566, 27995, 28010,
    28011, 28021, 28074, 28077, 30123, 30125, 30133, 30139, 30165, 30166, 30167, 30557, 30571,
    31445, 31447, 31450, 31662, 54702, 54958, 54997, 54999, 55022, 55126, 55127, 55130, 55133,
    56023, 56042, 56043, 56154, 60246, 60247, 60250, 60251, 60267, 60279, 60333, 60334, 61115,
    61142, 61143, 62890, 62891, 62894, 63325, 109405, 109917, 109994, 109995, 109998, 110253,
    110254, 110261, 112046, 112085, 112087, 112309, 120493, 120501, 120503, 120667, 120669, 122231,
    122285, 122286, 125782, 125783, 125789, 126651, 218810, 218811, 219834, 219835, 219990, 219991,
    219997, 220509, 220523, 224093, 224170, 224171, 224174, 240986, 241002, 241335, 251565, 251566,
    251578, 251579, 253302, 253303, 437622, 439670, 439981, 439982, 439995, 441018, 441019, 441046,
    441047, 448187, 448342, 481973, 482670, 503131, 503133, 503157, 503158, 506605, 879341, 879963,
    879990, 882039, 882094, 896374, 896685, 963947, 1006263, 1006267, 1006314, 1758682, 1759926,
    1759981, 1764189, 1793371, 1927894, 2012526, 2012534, 2012535, 2012629, 3519853, 3528378,
    3586742, 4025053, 7173485]

@[expose] noncomputable def pA315ConjBy (g a : CV 42) : CV 42 := g * a * g⁻¹

@[expose] noncomputable def pA315Conj : List (CV 42) :=
  pA315Codes.map fun c => pA315ConjBy (evalW (cOf PA) (cOf PB) (pA315Word 23 c)) (cOf PA)

theorem kQPs : schP QP = true := by decide +kernel

theorem kPA315 : pA315Conj.Nodup := by decide +kernel

theorem kPA315Len : pA315Conj.length = 315 := by
  rw [pA315Conj, List.length_map]
  rfl

theorem kConj : ((elemsC QP).filter fun x => orderIsC x 2).all
    (fun x => (elemsC QP).any fun g => eq22C g (cOf PA) x g) = true := by
  have hQP : ValidSchreier QP := check_certificate_of _ _ _ _ _ kQPs
  have hgen : ∀ σ ∈ ({PA, PB} : Set (Equiv.Perm (Fin 42))), cOf σ ∈ elemsC QP := fun σ hσ => by
    rw [mem_elemsC QP hQP, ev_cOf, QP_closure]
    exact Subgroup.subset_closure hσ
  have hPA : cOf PA ∈ elemsC QP := hgen PA (by simp)
  have hw : ∀ w, evalW (cOf PA) (cOf PB) w ∈ elemsC QP := by
    intro w
    rw [mem_elemsC QP hQP, ← evalW_ev, ev_cOf, ev_cOf, QP_closure]
    induction w with
    | nil => exact Subgroup.one_mem _
    | cons b w ih =>
      cases b
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) ih
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) ih
  have hL : ∀ x ∈ pA315Conj, ∃ g ∈ elemsC QP, x = g * cOf PA * g⁻¹ := by
    intro x hx
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
    exact ⟨evalW (cOf PA) (cOf PB) (pA315Word 23 c), hw _, rfl⟩
  have hsub : pA315Conj ⊆ (elemsC QP).filter fun x => orderIsC x 2 := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := hL x hx
    rw [List.mem_filter, orderIsC_conj]
    exact ⟨conj_mem_elemsC QP hQP hg hPA, kOrd.1⟩
  have hperm := (List.subperm_of_subset kPA315 hsub).perm_of_length_le (by rw [kInv, kPA315Len])
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨g, hg, rfl⟩ := hL x (hperm.mem_iff.2 hx)
  refine List.any_eq_true.2 ⟨g, hg, ?_⟩
  rw [eq22C_eq, decide_eq_true_iff]
  group

theorem kPartBlk0 : ((((elemsC QP).drop (0 * 2520)).take 2520).filter
    fun y => orderIsC y 4 && pairInvC ws (cOf PA) y).length = 65 := by decide +kernel
theorem kPartBlk1 : ((((elemsC QP).drop (1 * 2520)).take 2520).filter
    fun y => orderIsC y 4 && pairInvC ws (cOf PA) y).length = 99 := by decide +kernel
theorem kPartBlk2 : ((((elemsC QP).drop (2 * 2520)).take 2520).filter
    fun y => orderIsC y 4 && pairInvC ws (cOf PA) y).length = 98 := by decide +kernel
theorem kPartBlk3 : ((((elemsC QP).drop (3 * 2520)).take 2520).filter
    fun y => orderIsC y 4 && pairInvC ws (cOf PA) y).length = 108 := by decide +kernel
theorem kPartBlk4 : ((((elemsC QP).drop (4 * 2520)).take 2520).filter
    fun y => orderIsC y 4 && pairInvC ws (cOf PA) y).length = 91 := by decide +kernel
theorem kPartBlk5 : ((((elemsC QP).drop (5 * 2520)).take 2520).filter
    fun y => orderIsC y 4 && pairInvC ws (cOf PA) y).length = 104 := by decide +kernel
theorem kPartBlk6 : ((((elemsC QP).drop (6 * 2520)).take 2520).filter
    fun y => orderIsC y 4 && pairInvC ws (cOf PA) y).length = 91 := by decide +kernel
theorem kPartTail : (((elemsC QP).drop (7 * 2520)).filter
    fun y => orderIsC y 4 && pairInvC ws (cOf PA) y).length = 112 := by decide +kernel

theorem kPart : (((elemsC QP).filter fun y => orderIsC y 4).filter fun y =>
    pairInvC ws (cOf PA) y).length = 768 :=
  len_filter_blocks8 (elemsC QP) (fun y => pairInvC ws (cOf PA) y) (fun y => orderIsC y 4) 2520
    kPartBlk0 kPartBlk1 kPartBlk2 kPartBlk3 kPartBlk4 kPartBlk5 kPartBlk6 kPartTail rfl

theorem kNeg : orderIsC (cOf PB) 2 = false ∧
    ((elemsC QP).any fun g => eq22C g (cOf PA) (cOf PB) g) = false := by
  constructor <;> decide +kernel

end CFSG.Certificates.Kernel.PkCV.KGrp.K5123
