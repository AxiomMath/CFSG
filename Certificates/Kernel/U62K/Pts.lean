module

public import Certificates.Kernel.Fi23Cov.Words
public import Certificates.Kernel.Fi23T2.Glue
public import Certificates.Kernel.U62K.Lift

public section

set_option maxRecDepth 400000

namespace CertificateChecks.U62Pts

open CFSG.KC.Enum CFSG.Sporadic.Th CFSG.KD.Fi23Cov CFSG.KC.Fi23Cov CertificateChecks.U62Lift
open CFSG.Sporadic.Fi23 (J sylG slvl)

@[expose] noncomputable def lsOK : Bool :=
  allN 42 (fun l =>
    (Nat.beq (CFSG.KD.Fi23S.LS l 14566) 14566 || Nat.beq (CFSG.KD.Fi23S.LS l 14566) 18249) &&
    (Nat.beq (CFSG.KD.Fi23S.LS l 18249) 14566 || Nat.beq (CFSG.KD.Fi23S.LS l 18249) 18249) &&
    Nat.beq (CFSG.KD.Fi23S.LS l 2776) 2776) &&
  Nat.beq (CFSG.KD.Fi23S.LS 2 14566) 18249

theorem lsOK_true : lsOK = true := by decide +kernel

@[expose] def gW : List Nat := [56, 60, 63, 65, 54, 54, 60, 60, 60]

@[expose] def xW : List Nat :=
  [63, 67, 71, 68, 61, 65, 67, 65, 65, 65, 67, 67, 65, 65, 67, 64, 64, 75, 73]

@[expose] def yW : List Nat := [61, 63, 60, 60, 65, 66, 69, 67, 64, 68, 65, 65, 75]

@[expose] def dW : List Nat := [40, 40, 39, 40, 40, 39, 40, 39, 40, 39, 40, 39]

@[expose] noncomputable def ptsOK : Bool :=
  Nat.beq (CFSG.KC.Fi23R.wa CFSG.KD.Fi23K.G gW 0) 2776 &&
  Nat.beq (CFSG.KC.Fi23R.wa CFSG.KD.Fi23K.G gW 1) 14566 &&
  Nat.beq (CFSG.KC.Fi23R.wa CFSG.KD.Fi23K.G xW 0) 0 &&
  Nat.beq (CFSG.KC.Fi23R.wa CFSG.KD.Fi23K.G xW 1) 1 &&
  Nat.beq (CFSG.KC.Fi23R.wa CFSG.KD.Fi23K.G yW 0) 0 &&
  Nat.beq (CFSG.KC.Fi23R.wa CFSG.KD.Fi23K.G yW 1) 1 &&
  E (yW ++ xW) (xW ++ (yW ++ repW dW 7))

theorem ptsOK_true : ptsOK = true := by decide +kernel

section J


theorem ls_facts : (∀ l < 42, InTwo 31671 14566 18249 (CFSG.Perm.pairG sylG l)) ∧
    (∀ l < 42, idx 31671 (CFSG.Perm.pairG sylG l) 2776 = 2776) ∧
    idx 31671 (CFSG.Perm.pairG sylG 2) 14566 = 18249 := by
  have h := lsOK_true
  unfold lsOK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at h
  obtain ⟨hall, h2⟩ := h
  have hall' := CFSG.KS.Raw.Orb.allN_iff.1 hall
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.beq_eq] at hall'
  refine ⟨fun l hl => ?_, fun l hl => ?_, ?_⟩
  · obtain ⟨⟨h1, h2⟩, -⟩ := hall' l hl
    unfold InTwo
    rw [CertificateChecks.KernelFi23T2.idx_lG (x := 14566) hl (by norm_num),
      CertificateChecks.KernelFi23T2.idx_lG (x := 18249) hl (by norm_num)]
    exact ⟨h1, h2⟩
  · rw [CertificateChecks.KernelFi23T2.idx_lG (x := 2776) hl (by norm_num)]
    exact (hall' l hl).2
  · rw [CertificateChecks.KernelFi23T2.idx_lG (l := 2) (x := 14566) (by norm_num) (by norm_num)]
    exact h2

end J

section W


theorem okW_gW : okW gW := okW_lit (by decide)
theorem okW_xW : okW xW := okW_lit (by decide)
theorem okW_yW : okW yW := okW_lit (by decide)
theorem okW_dW : okW dW := okW_lit (by decide)

theorem wJ_dW : wJ (repW dW 7) = CFSG.Sporadic.Fi23.d := by
  have e : wJ dW = CFSG.Sporadic.Fi23.wordJ CFSG.Sporadic.Fi23.Native.dWord := by
    simp only [dW, wJ_cons, wJ_nil, jL_39, jL_40, CFSG.Sporadic.Fi23.wordJ,
      CFSG.Sporadic.Fi23.Native.dWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, one_mul, mul_one, mul_assoc, if_pos rfl, one_ne_zero, if_false, if_true]
  rw [wJ_repW, e]
  rfl

theorem pts_facts : (∃ g : CFSG.Sporadic.Fi23.J, idx 31671 g 0 = 2776 ∧ idx 31671 g 1 = 14566) ∧
    ∃ x y : CFSG.Sporadic.Fi23.J, (idx 31671 x 0 = 0 ∧ idx 31671 x 1 = 1) ∧
      (idx 31671 y 0 = 0 ∧ idx 31671 y 1 = 1) ∧ x * y * x⁻¹ * y⁻¹ = CFSG.Sporadic.Fi23.d := by
  have h := ptsOK_true
  unfold ptsOK at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨g0, g1⟩, x0⟩, x1⟩, y0⟩, y1⟩, hE⟩ := h
  rw [wa_wJ _ okW_gW _ (by norm_num)] at g0 g1
  rw [wa_wJ _ okW_xW _ (by norm_num)] at x0 x1
  rw [wa_wJ _ okW_yW _ (by norm_num)] at y0 y1
  refine ⟨⟨_, g0, g1⟩, wJ xW, wJ yW, ⟨x0, x1⟩, ⟨y0, y1⟩, ?_⟩
  have e := eqw (okW_append okW_yW okW_xW)
    (okW_append okW_xW (okW_append okW_yW (okW_repW okW_dW 7))) hE
  rw [wJ_append, wJ_append, wJ_append, wJ_dW] at e
  rw [e]
  group

end W

end CertificateChecks.U62Pts
