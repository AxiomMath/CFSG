module

public import Certificates.Kernel.Fi23Cls.Glue
public import CFSG.Certificates.Kernel.Fi23Tw.Sound
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Twin
import Certificates.Kernel.Fi23Cls.Scan
import Certificates.Kernel.Fi23Tw.Mat
import Certificates.Kernel.Fi23Tw.Twin
public import Certificates.Kernel.Fi23Tw.Data

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Tw

open CFSG.Sporadic.Fi23 CFSG.Sporadic.Th CFSG.KC.Fi23K CFSG.KD.Fi23K CFSG.KC.Fi23Five
  CFSG.KC.Fi23Tw CFSG.KD.Fi23Tw CFSG.KD.Fi23Cls CertificateChecks.KernelFi23Q
  CertificateChecks.KernelFi23Cls CertificateChecks.KernelFi23Five
  CFSG.HardMathSupport.Dickson.I271.TabFi23
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 (t3)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem w2_eq' : CFSG.KD.Fi23Q.t3R 2 = CFSG.KD.Fi23Cls.w2 := by decide

theorem fix_iff (r : Fin 31671) : t3 2 • r = r ↔ r.val ∈ L2 := by
  have hL := fixK_spec (ch17338scan2_ok : fixK G CFSG.KD.Fi23Cls.w2 L2 = true)
  have hact := act_t3 (c := 2) (by norm_num) w2_eq'
  rw [← hL, List.mem_filter, List.mem_range, Nat.beq_eq, hact r.val r.2, idx_of_lt _ r.2]
  exact ⟨fun h => ⟨r.2, congrArg Fin.val h⟩, fun h => Fin.ext h.2⟩

theorem L2_len : L2.length = 135 := by decide

theorem L2_nodup : L2.Nodup := by decide

theorem L2_lt : ∀ a ∈ L2, a < 31671 := by decide

theorem L2_pos {a : ℕ} (h : a ∈ L2) : ∃ i < 135, L2.getD i 0 = a := by
  obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 h
  refine ⟨i, L2_len ▸ hi, ?_⟩
  rw [List.getD_eq_getElem _ _ hi, e]

theorem L2_mem {i : ℕ} (hi : i < 135) : L2.getD i 0 ∈ L2 := by
  rw [List.getD_eq_getElem _ _ (L2_len ▸ hi)]
  exact List.getElem_mem _

theorem L2_inj {i j : ℕ} (hi : i < 135) (hj : j < 135) (h : L2.getD i 0 = L2.getD j 0) :
    i = j := by
  rw [List.getD_eq_getElem _ _ (L2_len ▸ hi), List.getD_eq_getElem _ _ (L2_len ▸ hj)] at h
  exact (List.Nodup.getElem_inj_iff L2_nodup).1 h

theorem mat_lt {i j : ℕ} (hij : i < j) (hj : j < 135) :
    A.testBit (135 * i + j) = cmK G (L2.getD i 0) (L2.getD j 0) ∧
      A.testBit (135 * j + i) = cmK G (L2.getD i 0) (L2.getD j 0) := by
  have hjl : j < L2.length := by rw [L2_len]; exact hj
  rcases (show i < 15 ∨ (15 ≤ i ∧ i < 30) ∨ (30 ≤ i ∧ i < 45) ∨ (45 ≤ i ∧ i < 60) ∨
      (60 ≤ i ∧ i < 75) ∨ (75 ≤ i ∧ i < 90) ∨ (90 ≤ i ∧ i < 105) ∨ (105 ≤ i ∧ i < 120) ∨
      (120 ≤ i ∧ i < 135) by omega) with h | h | h | h | h | h | h | h | h
  · exact matK_spec (lo := 0) (c := 15) ch17340mat0_ok i (by omega) (by omega) j hij hjl
  · exact matK_spec (lo := 15) (c := 15) ch17340mat1_ok i h.1 (by omega) j hij hjl
  · exact matK_spec (lo := 30) (c := 15) ch17340mat2_ok i h.1 (by omega) j hij hjl
  · exact matK_spec (lo := 45) (c := 15) ch17340mat3_ok i h.1 (by omega) j hij hjl
  · exact matK_spec (lo := 60) (c := 15) ch17340mat4_ok i h.1 (by omega) j hij hjl
  · exact matK_spec (lo := 75) (c := 15) ch17340mat5_ok i h.1 (by omega) j hij hjl
  · exact matK_spec (lo := 90) (c := 15) ch17340mat6_ok i h.1 (by omega) j hij hjl
  · exact matK_spec (lo := 105) (c := 15) ch17340mat7_ok i h.1 (by omega) j hij hjl
  · exact matK_spec (lo := 120) (c := 15) ch17340mat8_ok i h.1 (by omega) j hij hjl

theorem comm_iff {i j : ℕ} (hi : i < 135) (hj : j < 135) (hij : i ≠ j) :
    A.testBit (135 * i + j) = true ↔
      conjPt (L2.getD i 0) * conjPt (L2.getD j 0) = conjPt (L2.getD j 0) * conjPt (L2.getD i 0) := by
  have hli := L2_lt _ (L2_mem hi)
  have hlj := L2_lt _ (L2_mem hj)
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · rw [(mat_lt h hj).1, cmK_iff hli hlj]
    exact eq_comm
  · rw [(mat_lt h hi).2, cmK_iff hlj hli]

@[expose] noncomputable def Tq (q : ℕ) : List ℕ :=
  [T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14].getD q []

theorem PE_eq : PE = (List.range 15).flatMap Tq := by decide

theorem tq_ok : ∀ q < 15, twLoop A 1215 (1215 * q) (Tq q) = true := by
  intro q hq
  interval_cases q
  · exact ch17340tw0_ok
  · exact ch17340tw1_ok
  · exact ch17340tw2_ok
  · exact ch17340tw3_ok
  · exact ch17340tw4_ok
  · exact ch17340tw5_ok
  · exact ch17340tw6_ok
  · exact ch17340tw7_ok
  · exact ch17340tw8_ok
  · exact ch17340tw9_ok
  · exact ch17340tw10_ok
  · exact ch17340tw11_ok
  · exact ch17340tw12_ok
  · exact ch17340tw13_ok
  · exact ch17340tw14_ok

theorem twB_iff_pe {m : ℕ} (hm : m < 18225) :
    twB A m = true ↔ ∃ e ∈ PE, e % 32768 = m := by
  rw [PE_eq]
  constructor
  · intro h
    have hq : m / 1215 < 15 := by omega
    obtain ⟨-, hiff⟩ := twLoop_spec 1215 (1215 * (m / 1215)) (Tq (m / 1215)) (tq_ok _ hq)
    obtain ⟨e, he, he'⟩ := (hiff m (by omega) (by omega)).1 h
    exact ⟨e, List.mem_flatMap.2 ⟨m / 1215, List.mem_range.2 hq, he⟩, he'⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨q, hq, he⟩ := List.mem_flatMap.1 he
    have hq' := List.mem_range.1 hq
    obtain ⟨hr, hiff⟩ := twLoop_spec 1215 (1215 * q) (Tq q) (tq_ok q hq')
    have := hr e he
    exact (hiff _ this.1 this.2).2 ⟨e, he, rfl⟩

@[expose] noncomputable def pt (i : ℕ) (hi : i < 135) : Fin 31671 :=
  ⟨L2.getD i 0, L2_lt _ (L2_mem hi)⟩

theorem twin_iff_pe {i j : ℕ} (hi : i < 135) (hj : j < 135) :
    Twin (fun r : Fin 31671 => conjPt r.val) (t3 2) (pt i hi) (pt j hj) ↔
      ∃ e ∈ PE, e % 32768 = 135 * i + j := by
  have hm : 135 * i + j < 18225 := by omega
  have hdi : (135 * i + j) / 135 = i := by omega
  have hmj : (135 * i + j) % 135 = j := by omega
  rw [← twB_iff_pe hm, twB_iff, hdi, hmj]
  unfold Twin
  constructor
  · rintro ⟨-, -, hab, hnc, hall⟩
    have hij : i ≠ j := fun h => hab (by subst h; rfl)
    refine ⟨hij, Bool.eq_false_iff.2 fun h => hnc ((comm_iff hi hj hij).1 h), fun l hl hli hlj => ?_⟩
    have hc := hall (pt l hl) ((fix_iff _).2 (L2_mem hl))
      (fun h => hli (L2_inj hl hi (congrArg Fin.val h)))
      (fun h => hlj (L2_inj hl hj (congrArg Fin.val h)))
    apply Bool.eq_iff_iff.2
    rw [comm_iff hi hl (Ne.symm hli), comm_iff hj hl (Ne.symm hlj)]
    constructor
    · intro h
      exact (hc.1 h.symm).symm
    · intro h
      exact (hc.2 h.symm).symm
  · rintro ⟨hij, hnc, hall⟩
    refine ⟨(fix_iff _).2 (L2_mem hi), (fix_iff _).2 (L2_mem hj),
      fun h => hij (L2_inj hi hj (congrArg Fin.val h)),
      fun h => (by rw [(comm_iff hi hj hij).2 h] at hnc; cases hnc), fun c hc hca hcb => ?_⟩
    obtain ⟨l, hl, hle⟩ := L2_pos ((fix_iff c).1 hc)
    have hcl : c = pt l hl := Fin.ext hle.symm
    subst hcl
    have hli : l ≠ i := fun h => hca (by subst h; rfl)
    have hlj : l ≠ j := fun h => hcb (by subst h; rfl)
    have hb := hall l hl hli hlj
    have h1 := comm_iff hi hl (Ne.symm hli)
    have h2 := comm_iff hj hl (Ne.symm hlj)
    rw [hb] at h1
    constructor
    · intro h
      exact (h2.1 (h1.2 h.symm)).symm
    · intro h
      exact (h1.1 (h2.2 h.symm)).symm

end CertificateChecks.KernelFi23Tw

end
