
module

public import Certificates.Kernel.HN1408.CzTFacts
public import Certificates.Kernel.HN1408.RepWitChk

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CzInv

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.KD.HN1408.CzT

@[expose] noncomputable def namedE (t : Nat) : Equiv.Perm (Fin 1408) :=
  if t = 1 then elemZ else if t = 2 then elemA * elemZ else if t = 3 then elemB else elemZ₁

theorem repC_named {t : Nat} (h0 : 0 < t) (h5 : t < 5) : RepC (namedP t) (namedE t) := by
  interval_cases t
  · have e : namedP 1 = WK wordZ := rfl
    have e' : namedE 1 = elemZ := by simp [namedE]
    rw [e, e']
    exact repC_word (by decide)
  · have e : namedP 2 = pc (WK wordA) (WK wordZ) := rfl
    have e' : namedE 2 = elemA * elemZ := by simp [namedE]
    rw [e, e']
    exact repC_pc (repC_word (by decide)) (repC_word (by decide))
  · have e : namedP 3 = WK wordB := rfl
    have e' : namedE 3 = elemB := by simp [namedE]
    rw [e, e']
    exact repC_word (by decide)
  · have e : namedP 4 = WK wordZ₁ := rfl
    have e' : namedE 4 = elemZ₁ := by simp [namedE]
    rw [e, e']
    exact repC_word (by decide)

theorem conjW_nil (X : Nat) : conjW [] X = X := rfl

theorem conjW_cons (j : Nat) (w : List Nat) (X : Nat) :
    conjW (j :: w) X = pc (pc (WK [j + 1]) (conjW w X)) (WK [j + 1]) := by
  change strictN (WK [j + 1]) (fun G => pc (pc G (conjW w X)) G) = _
  generalize WK [j + 1] = G
  cases G <;> rfl

theorem repC_conjW {X : Nat} {g : Equiv.Perm (Fin 1408)} (hX : RepC X g) :
    ∀ w : List Nat, w.all (fun j => Nat.blt j 7) = true →
      ∃ c ∈ P1408, RepC (conjW w X) (c * g * c⁻¹)
  | [], _ => ⟨1, one_mem _, by rw [conjW_nil]; simpa using hX⟩
  | j :: w, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨c, hcP, hc⟩ := repC_conjW hX w h.2
    have hj : j < 7 := Nat.blt_eq.mp h.1
    have hG := repC_word (lettersOK_gen hj)
    have hR := repC_pc (repC_pc hG hc) hG
    rw [← conjW_cons j w X] at hR
    refine ⟨elemW [j + 1] * c, mul_mem (elemW_mem _) hcP, ?_⟩
    convert hR using 1
    calc (elemW [j + 1] * c) * g * (elemW [j + 1] * c)⁻¹
        = elemW [j + 1] * (c * g * c⁻¹) * (elemW [j + 1])⁻¹ := by group
      _ = _ := by rw [gen_inv hj]

theorem witK_parts {c t : Nat} {w : List Nat} (h : witK c t w = true) :
    fd (R c) 0 < 1280 ∧ fd (R c) 1 < 24 ∧ 0 < t ∧ t < 5 ∧ w.all (fun j => Nat.blt j 7) = true ∧
      pc (T0 (fd (R c) 0)) (T1 (fd (R c) 1)) = conjW w (namedP t) := by
  unfold witK at h
  simp only [strictB_app] at h
  obtain ⟨a, h⟩ := mkA h
  obtain ⟨b, h⟩ := mkA h
  obtain ⟨d, h⟩ := mkA h
  obtain ⟨f, h⟩ := mkA h
  obtain ⟨k, l⟩ := mkA h
  exact ⟨Nat.blt_eq.mp a, Nat.blt_eq.mp b, Nat.blt_eq.mp d, Nat.blt_eq.mp f, k,
    Nat.eq_of_beq_eq_true l⟩

theorem rep_wit {c : Nat} (h5 : 5 ≤ c) (h12 : c < 12) :
    ∃ t, 0 < t ∧ t < 5 ∧ fd (R c) 0 < 1280 ∧ fd (R c) 1 < 24 ∧
      ∃ g ∈ P1408, t0P (fd (R c) 0) * t1P (fd (R c) 1) = g * namedE t * g⁻¹ := by
  have h0 := rep_wit_ok
  unfold repWitK at h0
  have h := allN_spec h0 (c - 5) (by omega)
  have e : Nat.add (c - 5) 5 = c := by
    simp only [Nat.add_eq]
    omega
  rw [e] at h
  obtain ⟨hq, hq', ht0, ht5, hall, he⟩ := witK_parts h
  have hT := repC_pc (t0P_spec hq).2 (t1P_spec hq').2
  obtain ⟨g, hgP, hg⟩ := repC_conjW (repC_named ht0 ht5) _ hall
  rw [← he] at hg
  exact ⟨_, ht0, ht5, hq, hq', g, hgP, eq_of_repC hT hg⟩

end CFSG.KD.HN1408.CzInv

end
