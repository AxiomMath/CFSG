module

public import Certificates.Kernel.HN1408.Y442202Glue
public import Certificates.Kernel.HN1408.W441872Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CompatModel.Basic
import Certificates.Kernel.HN1408.W441872Chk
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableISpec

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.W441872

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KD.HN1408 CFSG.KD.HN1408.Y442202
open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.CompatModel
  CFSG.EvenSporadicStandard.HNRecog.Simple2S5 CFSG.Sporadic.SmallOddCore
open CFSG.KS.Raw.Orb (strictB_eq bAnd_eq bIf_eq)

theorem gen_sq {l : ℕ} (h1 : 1 ≤ l) (h7 : l ≤ 7) : elemW [l] * elemW [l] = 1 := by
  have h := CFSG.KS.Raw.Orb.allN_iff.1 ch441872_inv (l - 1) (by change l - 1 < 7; omega)
  beta_reduce at h
  rw [strictB_eq] at h
  beta_reduce at h
  have e : Nat.add (l - 1) (nat_lit 1) = l := by
    change l - 1 + 1 = l
    omega
  rw [e] at h
  have hw : lettersOK [l] = true := by simp [lettersOK, h1, h7]
  exact perm_eq (rc_pc (rc_word hw) (rc_word hw)) (by rw [Nat.eq_of_beq_eq_true h]; exact rc_id)

theorem elemW_rev {w : List ℕ} (hw : lettersOK w = true) : elemW w.reverse = (elemW w)⁻¹ := by
  induction w with
  | nil => simp [elemW, CFSG.EvenSporadicStandard.TwoHS.wordVal]
  | cons l w ih =>
    have hl := lettersOK_spec hw l List.mem_cons_self
    have hw' : lettersOK w = true := by
      unfold lettersOK at hw ⊢
      exact List.all_eq_true.2 fun y hy => List.all_eq_true.1 hw y (List.mem_cons_of_mem _ hy)
    rw [List.reverse_cons, elemW_append, ih hw', show l :: w = [l] ++ w from rfl, elemW_append,
      mul_inv_rev, inv_eq_of_mul_eq_one_right (gen_sq hl.1 hl.2)]

theorem elemW_wordAZ : elemW wordAZ = elemA * elemZ := elemW_append wordA wordZ

theorem rcA : RC (WK wordA) elemA := rc_word (w := wordA) (by decide)

theorem rcB : RC (WK wordB) elemB := rc_word (w := wordB) (by decide)

theorem rcAZ : RC (WK wordAZ) (elemA * elemZ) := by
  have h := rc_word (w := wordAZ) (by decide)
  rwa [elemW_wordAZ] at h

theorem rcAB : RC (WK (wordA ++ wordB)) (elemA * elemB) := by
  have h := rc_word (w := wordA ++ wordB) (by decide)
  rwa [elemW_append] at h

@[expose] noncomputable def vE (j : ℕ) : Equiv.Perm (Fin 1408) := elemW (vWords.getD j [])

theorem vWords_letters : ∀ j < 16, lettersOK (vWords.getD j []) = true := by decide

theorem vSq_letters : ∀ j < 16, lettersOK (vSq.getD j []) = true := by decide

theorem conjB_letters : ∀ j < 6, lettersOK (witConjB.getD j []) = true := by decide

theorem conjAZ_letters : ∀ j < 10, lettersOK (witConjAZ.getD j []) = true := by decide

theorem vWords_split : ∀ j < 16,
    (j < 6 ∧ vWords.getD j [] = witConjB.getD j [] ++ wordB ++ (witConjB.getD j []).reverse) ∨
      (6 ≤ j ∧ vWords.getD j [] =
        witConjAZ.getD (j - 6) [] ++ wordAZ ++ (witConjAZ.getD (j - 6) []).reverse) := by
  decide

theorem rc_V {j : ℕ} (hj : j < 16) : RC (V j) (vE j) := by
  have h := CFSG.KS.Raw.Orb.allN_iff.1 ch441872_vt j hj
  rw [Nat.eq_of_beq_eq_true h]
  exact rc_word (vWords_letters j hj)

theorem in2A_V {j : ℕ} (hj : j < 16) : In2A ⟨vE j, elemW_mem _⟩ := by
  rcases vWords_split j hj with ⟨hj6, e⟩ | ⟨hj6, e⟩
  · refine Or.inr (Or.inr (isConj_iff.2 ⟨⟨elemW (witConjB.getD j []), elemW_mem _⟩,
      Subtype.ext ?_⟩))
    change elemW (witConjB.getD j []) * elemW wordB * (elemW (witConjB.getD j []))⁻¹ = vE j
    rw [vE, e, elemW_append, elemW_append, elemW_rev (conjB_letters j hj6)]
  · refine Or.inr (Or.inl (isConj_iff.2 ⟨⟨elemW (witConjAZ.getD (j - 6) []), elemW_mem _⟩,
      Subtype.ext ?_⟩))
    change elemW (witConjAZ.getD (j - 6) []) * (elemA * elemZ) *
      (elemW (witConjAZ.getD (j - 6) []))⁻¹ = vE j
    rw [vE, e, elemW_append, elemW_append, elemW_rev (conjAZ_letters (j - 6) (by omega)),
      elemW_wordAZ]

theorem pow4_eq (x : Equiv.Perm (Fin 1408)) : x * x * (x * x) = x ^ 4 := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem pow5_eq (x : Equiv.Perm (Fin 1408)) : x * x * (x * x) * x = x ^ 5 := by
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem vertK_sound {b a az m X : ℕ} {g : List ℕ} {v : Equiv.Perm (Fin 1408)} (hX : RC X v)
    (hb : RC b elemB) (ha : RC a elemA) (haz : RC az (elemA * elemZ)) (hg : lettersOK g = true)
    (h : vertK b a az m g X = true) :
    v * elemB ≠ elemB * v ∧ (elemB * v) ^ 5 ≠ 1 ∧
      ((elemB * v) ^ 4 = 1 → (elemB * v) ^ 2 = elemA ∨
        ∃ c ∈ P1408, c * (elemA * elemZ) * c⁻¹ = (elemB * v) ^ 2) := by
  unfold vertK at h
  simp only [bAnd_eq, strictB_eq, Bool.and_eq_true] at h
  obtain ⟨hc, h5, hm⟩ := h
  have hP := rc_pc hb hX
  have hP2 := rc_pc hP hP
  have hP4 := rc_pc hP2 hP2
  have hP5 := rc_pc hP4 hP
  rw [pow4_eq] at hP4
  rw [pow5_eq] at hP5
  refine ⟨fun e => ne_of_bIf hc (nat_eq (rc_pc hX hb) (by rw [e]; exact rc_pc hb hX)),
    fun e5 => ne_of_bIf h5 (nat_eq hP5 (by rw [e5]; exact rc_id)), fun e4 => ?_⟩
  unfold modeK at hm
  rw [bIf_eq] at hm
  split_ifs at hm with h0
  · exact absurd (nat_eq hP4 (by rw [e4]; exact rc_id)) (ne_of_bIf hm)
  · rw [bIf_eq] at hm
    split_ifs at hm with h1
    · rw [Nat.eq_of_beq_eq_true hm] at hP2
      exact Or.inl (by rw [sq]; exact perm_eq hP2 ha)
    · exact Or.inr ⟨elemW g, elemW_mem g, by rw [sq]; exact conj_of (rc_word hg) haz hP2 hm⟩

theorem modelVertex_V {j : ℕ} (hj : j < 16) : ModelVertex ⟨vE j, elemW_mem _⟩ := by
  have h := ch441872_vert
  unfold vertsK at h
  simp only [strictB_eq] at h
  have hv := CFSG.KS.Raw.Orb.allN_iff.1 h j hj
  obtain ⟨hc, h5, h4⟩ := vertK_sound (rc_V hj) rcB rcA rcAZ (vSq_letters j hj) hv
  refine ⟨in2A_V hj, fun e => hc (congrArg Subtype.val e), ?_, fun e4 => ?_⟩
  · rw [← Subgroup.orderOf_coe]
    intro e5
    exact h5 (by rw [← e5]; exact pow_orderOf_eq_one _)
  · rw [← Subgroup.orderOf_coe] at e4
    have e4' : (elemB * vE j) ^ 4 = 1 := by rw [← e4]; exact pow_orderOf_eq_one _
    rcases h4 e4' with e | ⟨c, hc, e⟩
    · have e' : (pB * ⟨vE j, elemW_mem _⟩) ^ 2 = pA := Subtype.ext e
      rw [e']
      exact Or.inl (IsConj.refl _)
    · exact Or.inr (Or.inl (isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext e⟩))

theorem covAt_sound {Vf : ℕ → ℕ} {a b ab X c : ℕ} {s : Equiv.Perm (Fin 1408)} (hX : RC X s)
    (ha : RC a elemA) (hb : RC b elemB) (hab : RC ab (elemA * elemB))
    (hV : ∀ j < 16, RC (Vf j) (vE j)) (h : covAt Vf a b ab X c = true) (hs : orderOf s = 2) :
    s = elemA ∨ s = elemB ∨ s = elemA * elemB ∨ ∃ j < 16, vE j * s = s * vE j := by
  unfold covAt at h
  rw [bIf_eq] at h
  split_ifs at h with hc
  · have hc' := Nat.blt_eq.mp hc
    exact Or.inr (Or.inr (Or.inr ⟨c, hc', comm_of (hV c hc') hX h⟩))
  · rw [bIf_eq] at h
    split_ifs at h with hi
    · rw [bIf_eq, bIf_eq] at h
      split_ifs at h with e1 e2
      · rw [Nat.eq_of_beq_eq_true e1] at hX
        exact Or.inl (perm_eq hX ha)
      · rw [Nat.eq_of_beq_eq_true e2] at hX
        exact Or.inr (Or.inl (perm_eq hX hb))
      · rw [Nat.eq_of_beq_eq_true h] at hX
        exact Or.inr (Or.inr (Or.inl (perm_eq hX hab)))
    · exact (hi (by rw [← involOK_eq hX.1]; exact involOK_of_orderOf (by norm_num) hX.2 hs)).elim

theorem facts441872 :
    Nat.card ↥(closure (elemW '' {w | w ∈ witSylow})) = 256 ∧
      closure (elemW '' {w | w ∈ witSylow}) ≤
        P1408 ⊓ centralizer ({elemB} : Set (Equiv.Perm (Fin 1408))) ∧
      ∀ s ∈ closure (elemW '' {w | w ∈ witSylow}), orderOf s = 2 →
        s = elemA ∨ s = elemB ∨ s = elemA * elemB ∨
          ∃ w : ↥P1408, ModelVertex w ∧ (w : Equiv.Perm (Fin 1408)) * s = s * w := by
  have hk : witSylow.length = SW.k := by rw [ch441872_k]; rfl
  have hG : allN SW.k (fun j => Nat.beq (SW.G j) (WK (witSylow.getD j []))) = true := by
    rw [ch441872_k]
    exact ch441872_gens
  have hl : ∀ j < 5, lettersOK (witSylow.getD j []) = true := by decide
  obtain ⟨x, R⟩ := rec_facts ch441872_rec hk hG fun j hj => hl j (by rw [ch441872_k] at hj; exact hj)
  refine ⟨by rw [← ch441872_cnt]; exact R.card, ?_, ?_⟩
  · rw [closure_le]
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    have hj5 : j < 5 := hj
    have hc := ch441872_cent
    unfold centK at hc
    simp only [strictB_eq] at hc
    have hc' := CFSG.KS.Raw.Orb.allN_iff.1 hc j hj5
    rw [Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 ch441872_gens j hj5)] at hc'
    rw [← List.getD_eq_getElem _ [] hj]
    refine Subgroup.mem_inf.2 ⟨elemW_mem _, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of (rc_word (hl j hj5)) rcB hc'
  · intro s hs hso
    obtain ⟨i, hi, rfl⟩ := (R.mem _).1 hs
    have hi' : i < 256 := by rw [← ch441872_cnt]; exact hi
    have hc := ch441872_cov
    unfold covK at hc
    simp only [strictB_eq] at hc
    have hci := CFSG.KS.Raw.Orb.allN_iff.1 hc i hi'
    rcases covAt_sound (R.rc i hi) rcA rcB rcAB (fun j hj => rc_V hj) hci hso with
      e | e | e | ⟨j, hj, e⟩
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr ⟨⟨vE j, elemW_mem _⟩, modelVertex_V hj, e⟩))

end CFSG.KD.HN1408.W441872

end
