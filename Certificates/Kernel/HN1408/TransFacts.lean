module

public import Certificates.Kernel.HN1408.M11Facts
public import Certificates.Kernel.HN1408.TransChk

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.Trans

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MulH CFSG.KC.BfsPin
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem sel7_eq {j : Nat} (hj : j < 7) :
    sel7 (WK [1]) (WK [2]) (WK [3]) (WK [4]) (WK [5]) (WK [6]) (WK [7]) j = WK [j + 1] := by
  interval_cases j <;> rfl

theorem row_ok {q : Nat} (hq : q < 1408) :
    rowT TR (WK [1]) (WK [2]) (WK [3]) (WK [4]) (WK [5]) (WK [6]) (WK [7]) q = true := by
  have h := trans_ok
  unfold transK at h
  simp only [strictB_app] at h
  exact allN_spec h q hq

theorem trans_K : ∀ q : Fin 1408, ∃ g ∈ P1408, g q = 0 := by
  have key : ∀ d, ∀ q (hq : q < 1408), f16 (TR q) 2 = d → ∃ g ∈ P1408, g ⟨q, hq⟩ = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro q hq hd
      have h := row_ok hq
      unfold rowT at h
      simp only [strictB_app] at h
      rcases mkIf h with ⟨hq0, -⟩ | ⟨hq0, h⟩
      · obtain rfl : q = 0 := Nat.eq_of_beq_eq_true hq0
        exact ⟨1, one_mem _, rfl⟩
      obtain ⟨a, h⟩ := mkA h
      obtain ⟨b, h⟩ := mkA h
      obtain ⟨c, e⟩ := mkA h
      have hq' := Nat.blt_eq.mp a
      have hj := Nat.blt_eq.mp b
      have hdep := Nat.eq_of_beq_eq_true c
      rw [sel7_eq hj] at e
      have hG := repC_word (lettersOK_gen hj)
      have e1 := Nat.eq_of_beq_eq_true e
      rw [repC_pt hG hq'] at e1
      have e2 : elemW [f16 (TR q) 1 + 1] ⟨f16 (TR q) 0, hq'⟩ = ⟨q, hq⟩ := Fin.ext e1
      obtain ⟨g, hgP, hg⟩ := ih (f16 (TR (f16 (TR q) 0)) 2) (by omega) _ hq' rfl
      refine ⟨g * elemW [f16 (TR q) 1 + 1], mul_mem hgP (elemW_mem _), ?_⟩
      have e3 : elemW [f16 (TR q) 1 + 1] ⟨q, hq⟩ = ⟨f16 (TR q) 0, hq'⟩ := by
        calc elemW [f16 (TR q) 1 + 1] ⟨q, hq⟩ = (elemW [f16 (TR q) 1 + 1])⁻¹ ⟨q, hq⟩ := by
              rw [gen_inv hj]
          _ = ⟨f16 (TR q) 0, hq'⟩ := by
              rw [← e2]
              simp
      rw [Equiv.Perm.mul_apply, e3, hg]
  intro q
  exact key _ q.1 q.2 rfl

end CFSG.KD.HN1408.Trans

end
