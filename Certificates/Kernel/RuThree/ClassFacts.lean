module

public import Certificates.Kernel.RuThree.ClassK
public import Certificates.Kernel.RuThree.Facts
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
public import CFSG.Certificates.Kernel.K426KSound
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3RuInputs
public meta import CFSG.HardMathSupport.Solomon.Coordinator.GFR3RuInputs
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Group
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR3Core
public meta import CFSG.HardMathSupport.Solomon.Coordinator.GFR3Core
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public meta import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelRuThree

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.HeLoc CFSG.KC.K426K
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer
open CFSG.RankThree.Native CFSG.RankThree.PartOne CFSG.Sporadic.RuSchreier CFSG.Sporadic.Schreier
open CFSG.Certificates CFSG.Certificates.Native CFSG.EvenSporadicStandard.RuStd.S2
open CFSG.HardMathSupport.Solomon.Coordinator

theorem card_filter_range (p : ℕ → Bool) :
    ∀ m, ((Finset.range m).filter fun j => p j = true).card = (List.range m).countP p
  | 0 => by simp
  | m + 1 => by
    have hr : Finset.range (m + 1) = insert m (Finset.range m) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert]
      omega
    rw [hr, Finset.filter_insert, List.range_succ, List.countP_append, ← card_filter_range p m]
    by_cases hp : p m = true
    · rw [if_pos hp, Finset.card_insert_of_notMem (by simp)]
      simp [hp]
    · rw [if_neg hp]
      simp [hp]


theorem repF_cv {i : ℕ} (hi : i < 2160) : RepF 4060 (cv i) (treePerm gpC C0.P C0.L i) :=
  repF_trV ctree cg 2160 i hi.le hi

theorem T_C {i : ℕ} (hi : i < 2160) :
    treePerm gpC C0.P C0.L i ∈ Subgroup.closure (permsA 4060 ruThreeC0Gens) :=
  enumOK_mem keys_lt c_enum (by rw [c_size]; exact hi) (c_rep hi)

theorem T_inj {a b : ℕ} (ha : a < 2160) (hb : b < 2160)
    (e : treePerm gpC C0.P C0.L a = treePerm gpC C0.P C0.L b) : a = b := by
  have hva := (enumOK_spec keys_lt c_enum).2.2 a (by rw [c_size]; exact ha)
  have hvb := (enumOK_spec keys_lt c_enum).2.2 b (by rw [c_size]; exact hb)
  apply ckeys_inj a ha b hb
  rw [← c_get ha, ← c_get hb]
  exact keyA_eq keys_lt hva hvb
    (by rw [CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep (c_rep ha),
      CFSG.Monster.B.Mathieu.permOfArr_eq_of_rep (c_rep hb), e])

theorem commV_iff {j i : ℕ} (hj : j < 2160) (hi : i < 2160) :
    commV j i = true ↔ treePerm gpC C0.P C0.L j * treePerm gpC C0.P C0.L i =
      treePerm gpC C0.P C0.L i * treePerm gpC C0.P C0.L j :=
  ⟨fun h => eq_of_eqOnL faith.1 ((repF_cv hj).comp (repF_cv hi)) ((repF_cv hi).comp (repF_cv hj))
      (ruP.mul_mem (c_mem hj) (c_mem hi)) (ruP.mul_mem (c_mem hi) (c_mem hj)) h,
    fun h => eqOnL_of_eq bs_lt ((repF_cv hj).comp (repF_cv hi))
      (((repF_cv hi).comp (repF_cv hj)).congr h.symm)⟩

theorem countK_eq {i : ℕ} (hi : i < 2160) : countK i = ((Finset.range 2160).filter fun j =>
    treePerm gpC C0.P C0.L j * treePerm gpC C0.P C0.L i =
      treePerm gpC C0.P C0.L i * treePerm gpC C0.P C0.L j).card := by
  unfold countK
  rw [← card_filter_range]
  congr 1
  apply Finset.filter_congr
  intro j hj
  exact commV_iff (Finset.mem_range.1 hj) hi

theorem comm_eq {i : ℕ} (hi : i < 2160) :
    gfr3CommCount 4060 ruThreeC0Cert.pts ruThreeC0Cert.pts[i]! = ((Finset.range 2160).filter
      fun j => treePerm gpC C0.P C0.L j * treePerm gpC C0.P C0.L i =
        treePerm gpC C0.P C0.L i * treePerm gpC C0.P C0.L j).card := by
  unfold gfr3CommCount
  rw [c_size]
  congr 1
  apply Finset.filter_congr
  intro j hj
  exact commA_iff (c_rep (Finset.mem_range.1 hj)) (c_rep hi)

theorem count_le {g i r : ℕ} (hg : g < 2160) (hi : i < 2160) (hr : r < 2160)
    (h : treePerm gpC C0.P C0.L g * treePerm gpC C0.P C0.L i =
      treePerm gpC C0.P C0.L r * treePerm gpC C0.P C0.L g) :
    countK i ≤ countK r := by
  classical
  rw [countK_eq hi, countK_eq hr]
  set T := treePerm gpC C0.P C0.L
  have hex : ∀ j < 2160, ∃ j' < 2160, T j' = T g * T j * (T g)⁻¹ := by
    intro j hj
    have hmem : T g * T j * (T g)⁻¹ ∈ Subgroup.closure (permsA 4060 ruThreeC0Gens) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (T_C hg) (T_C hj)) (Subgroup.inv_mem _ (T_C hg))
    obtain ⟨j', hj', hrep⟩ := enumOK_exists_rep keys_lt c_enum hmem
    rw [c_size] at hj'
    exact ⟨j', hj', (c_rep hj').unique hrep⟩
  let φ : ℕ → ℕ := fun j => if hj : j < 2160 then Classical.choose (hex j hj) else 0
  have hφ : ∀ j (hj : j < 2160), φ j < 2160 ∧ T (φ j) = T g * T j * (T g)⁻¹ := fun j hj => by
    simp only [φ, dif_pos hj]
    exact Classical.choose_spec (hex j hj)
  have hTr : T r = T g * T i * (T g)⁻¹ := by rw [h, mul_inv_cancel_right]
  apply Finset.card_le_card_of_injOn φ
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq,
      Finset.mem_coe] at hj ⊢
    obtain ⟨hj1, hc⟩ := hj
    refine ⟨(hφ j hj1).1, ?_⟩
    rw [(hφ j hj1).2, hTr]
    calc T g * T j * (T g)⁻¹ * (T g * T i * (T g)⁻¹) = T g * (T j * T i) * (T g)⁻¹ := by group
      _ = T g * (T i * T j) * (T g)⁻¹ := by rw [hc]
      _ = T g * T i * (T g)⁻¹ * (T g * T j * (T g)⁻¹) := by group
  · intro a ha b hb e
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_range, Set.mem_setOf_eq,
      Finset.mem_coe] at ha hb
    have e' := congrArg T e
    rw [(hφ a ha.1).2, (hφ b hb.1).2] at e'
    exact T_inj ha.1 hb.1 (by simpa using e')

theorem wit_bound {i m : ℕ} (hi : i < 2160) (h : witOK i m = true) : countK i * m < 2160 := by
  unfold witOK at h
  simp only [Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨⟨⟨⟨hg, ht⟩, hr⟩, hc⟩, hm⟩ := h
  have hconj := eq_of_eqOnL faith.1 ((repF_cv hg).comp (repF_cv hi))
    ((repF_cv hr).comp (repF_cv hg)) (ruP.mul_mem (c_mem hg) (c_mem hi))
    (ruP.mul_mem (c_mem hr) (c_mem hg)) hc
  have hle := count_le hg hi hr hconj
  have hcnt : countK (RR.getD (wt i) 0) = RC.getD (wt i) 0 := by
    interval_cases (wt i)
    · exact Nat.eq_of_beq_eq_true kCount0
    · exact Nat.eq_of_beq_eq_true kCount1
  rw [hcnt] at hle
  exact lt_of_le_of_lt (Nat.mul_le_mul_right m hle) hm

theorem classAt_all : ∀ i < 2160, classAt i = true := by
  have hb : allN (540 * 4) classAt = true := allN_of_blocks (L := 540) (K := 4) fun s hs => by
    interval_cases s
    exacts [kClass0, kClass1, kClass2, kClass3]
  exact fun i hi => Orb.allN_iff.1 hb i (by omega)

theorem class_ok : ruThreeClassCheck () = true := by
  unfold ruThreeClassCheck gfr3ClassOK
  rw [allLt_iff, c_size]
  intro i hi
  have hc := classAt_all i hi
  have hT := c_rep hi
  have hf := repF_cv hi
  have hm := c_mem hi
  have h1 : eqOnL bs (cv i) (fun x => x) = true ↔ treePerm gpC C0.P C0.L i = 1 :=
    fixL_iff faith.1 bs_lt hf hm
  have hp : ∀ e, eqOnL bs (powF (cv i) e) (fun x => x) = true ↔
      treePerm gpC C0.P C0.L i ^ e = 1 := fun e =>
    fixL_iff faith.1 bs_lt (hf.powF e) (ruP.pow_mem hm e)
  have e1 : eqA 4060 ruThreeC0Cert.pts[i]! (idA 4060) = true ↔ treePerm gpC C0.P C0.L i = 1 :=
    eqA_iff hT rep_idA
  have ep : ∀ e, eqA 4060 (powArr 4060 ruThreeC0Cert.pts[i]! e) (idA 4060) = true ↔
      treePerm gpC C0.P C0.L i ^ e = 1 := fun e => eqA_iff (rep_powArr hT e) rep_idA
  unfold classAt at hc
  rw [comm_eq hi, ← countK_eq hi]
  by_cases hone : treePerm gpC C0.P C0.L i = 1
  · have h' := e1.2 hone
    simp [h']
  · have hno : eqOnL bs (cv i) (fun x => x) = false := by
      cases hh : eqOnL bs (cv i) (fun x => x)
      · rfl
      · exact absurd (h1.1 hh) hone
    rw [hno, Bool.false_or, Bool.and_eq_true] at hc
    obtain ⟨hc2, hc5⟩ := hc
    rw [Bool.and_eq_true]
    constructor
    · by_cases h2 : treePerm gpC C0.P C0.L i ^ 2 = 1
      · rw [(hp 2).2 h2, Bool.not_true, Bool.false_or] at hc2
        have hb := wit_bound hi hc2
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        right
        norm_num
        omega
      · have hf2 : eqA 4060 (powArr 4060 ruThreeC0Cert.pts[i]! 2) (idA 4060) = false := by
          cases hh : eqA 4060 (powArr 4060 ruThreeC0Cert.pts[i]! 2) (idA 4060)
          · rfl
          · exact absurd ((ep 2).1 hh) h2
        simp [hf2]
    · by_cases h5 : treePerm gpC C0.P C0.L i ^ 5 = 1
      · rw [(hp 5).2 h5, Bool.not_true, Bool.false_or] at hc5
        have hb := wit_bound hi hc5
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        right
        norm_num
        omega
      · have hf5 : eqA 4060 (powArr 4060 ruThreeC0Cert.pts[i]! 5) (idA 4060) = false := by
          cases hh : eqA 4060 (powArr 4060 ruThreeC0Cert.pts[i]! 5) (idA 4060)
          · rfl
          · exact absurd ((ep 5).1 hh) h5
        simp [hf5]

end CertificateChecks.KernelRuThree

end
