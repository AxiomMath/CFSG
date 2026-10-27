module

public import Certificates.Kernel.Fi23R.Group
public import CFSG.Sporadic.FischerOddCore.Fi23WitCheckInputs
import Certificates.Kernel.Fi23R.Base
import Certificates.Kernel.Fi23R.Wit1
import Certificates.Kernel.Fi23R.Wit2
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23R

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KD.Fi23K CFSG.KD.Fi23R CFSG.KS.Raw.Orb
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native CertificateChecks.KernelFi23M
  CFSG.Sporadic.FischerOddCore

theorem base_facts : eqB G [43, 43] [] = true ∧ witB wX cw1 = true ∧ witB wXC cw2 = true ∧
    eqB G (u2W ++ u2W) [] = true ∧ eqB G (u3W ++ u3W) [] = true ∧ wa G u2W 2 ≠ 2 ∧
    wa G u3W 2 ≠ 2 ∧ (0 :: gU).all (cmB wX) = true ∧ (0 :: gT).all (cmB wXC) = true := by
  have h := baseK_ok
  unfold baseK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun e => ?_, fun e => ?_, h8, h9⟩
  · rw [e] at h6
    exact absurd h6 (by decide)
  · rw [e] at h7
    exact absurd h7 (by decide)

theorem ok_wX : ∀ c ∈ wX, okL c := by decide
theorem ok_wXC : ∀ c ∈ wXC, okL c := by decide
theorem ok_W0 : ∀ c ∈ W0n, okL c := by decide
theorem ok_W1 : ∀ c ∈ W1n, okL c := by decide
theorem ok_W2 : ∀ c ∈ W2n, okL c := by decide
theorem ok_WW : ∀ c ∈ WWn, okL c := by decide
theorem ok_u2 : ∀ c ∈ u2W, okL c := by decide

theorem ok_u3 : ∀ c ∈ u3W, okL c :=
  ok_append (ok_append (ok_append (ok_invW ok_WW) (by decide)) ok_WW) ok_u2


theorem dP_sq : dP * dP = 1 := by
  have h := wp_eq_of_eqB base_facts.1 (by decide) (by decide)
  rwa [wp_cons, wp_cons, wp_nil, one_mul, lp_43] at h

theorem rw_X : RW (compT 31671 (dTab orbLit)
    (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 1)) wX :=
  (rw_compT rw_dTab (rw_treeActTab (by norm_num))).word rfl

theorem rw_XC : RW (compT 31671 (compT 31671 (dTab orbLit)
    (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 1))
    (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) 39)) wXC :=
  (rw_compT rw_X (rw_treeActTab (by norm_num))).word rfl

theorem rw_bray {R G' : Table} {wR wG : List ℕ} (hR : RW R wR) (hG : RW G' wG) (e : ℕ)
    (odd : Bool) : RW (fi23BrayT R G' (invT 31671 G') e odd) (brayW wR wG e odd) := by
  have hp := rw_powT (rw_compT hR (rw_compT (rw_invT dP_sq hG) (rw_compT hR hG))) e
  unfold fi23BrayT brayW
  cases odd
  · simpa using hp
  · simpa using rw_compT hG hp

theorem rw_comm {X Y : Table} {wX' wY : List ℕ} (hX : RW X wX') (hY : RW Y wY) :
    RW (fi23CommT X Y) (commW wX' wY) :=
  rw_compT hX (rw_compT hY (rw_compT (rw_invT dP_sq hX) (rw_invT dP_sq hY)))

theorem witOK_of {R G' : Table} {wR wG : List ℕ} (hR : RW R wR) (hG : RW G' wG) (e : ℕ)
    (odd : Bool) (h : eqB G (wR ++ brayW wR wG e odd) (brayW wR wG e odd ++ wR) = true) :
    fi23WitOK R G' e odd = true := by
  have hB := rw_bray hR hG e odd
  have hok := ok_brayW hR.2.1 hG.2.1 e odd
  have e1 := wp_eq_of_eqB h (ok_append hR.2.1 hok) (ok_append hok hR.2.1)
  unfold fi23WitOK
  rw [rw_invOK dP_sq hG, rw_invOK dP_sq hB, (rw_compT hB hR).beq (rw_compT hR hB) e1] <;> rfl

theorem common_eq {R E₁ E₂ : Table} {wR w₁ w₂ : List ℕ} (hR : RW R wR) (h₁ : RW E₁ w₁)
    (h₂ : RW E₂ w₂) : fi23Common R E₁ E₂ =
      (List.range 31671).countP fun x => fxW G wR x && fxW G w₁ x && fxW G w₂ x := by
  unfold fi23Common
  apply List.countP_congr
  intro i hi
  have hi' := List.mem_range.1 hi
  rw [hR.ap hi', h₁.ap hi', h₂.ap hi']
  simp only [Bool.and_eq_true, beq_iff_eq, fxW_iff]

theorem rw_W0 : RW (wordT 31671 (genTables orbLit) fi23W0) W0n :=
  (rw_wordT fi23W0 (by decide)).word (by decide)
theorem rw_W1 : RW (wordT 31671 (genTables orbLit) fi23W1) W1n :=
  (rw_wordT fi23W1 (by decide)).word (by decide)
theorem rw_W2 : RW (wordT 31671 (genTables orbLit) fi23W2) W2n :=
  (rw_wordT fi23W2 (by decide)).word (by decide)

theorem caseOK_of {R : Table} {wR : List ℕ} (hR : RW R wR) (e₀ e₁ e₂ : ℕ) (o₀ o₁ o₂ : Bool)
    (hw : witB wR (cws wR e₀ e₁ e₂ o₀ o₁ o₂) = true)
    (hc : (List.range 31671).countP (cmQ wR (cws wR e₀ e₁ e₂ o₀ o₁ o₂)) = 2) :
    fi23CaseOK orbLit R e₀ e₁ e₂ o₀ o₁ o₂ = true := by
  unfold witB cws at hw
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hw
  obtain ⟨w0, w1, w2⟩ := hw
  have hE₁ := rw_comm (rw_bray hR rw_W1 e₁ o₁) (rw_bray hR rw_W0 e₀ o₀)
  have hE₂ := rw_comm (rw_bray hR rw_W2 e₂ o₂) (rw_bray hR rw_W0 e₀ o₀)
  unfold fi23CaseOK fi23CT
  rw [witOK_of hR rw_W0 e₀ o₀ w0, witOK_of hR rw_W1 e₁ o₁ w1, witOK_of hR rw_W2 e₂ o₂ w2,
    common_eq hR hE₁ hE₂]
  have e : (List.range 31671).countP (fun x => fxW G wR x &&
      fxW G (commW (brayW wR W1n e₁ o₁) (brayW wR W0n e₀ o₀)) x &&
      fxW G (commW (brayW wR W2n e₂ o₂) (brayW wR W0n e₀ o₀)) x) =
      (List.range 31671).countP (cmQ wR (cws wR e₀ e₁ e₂ o₀ o₁ o₂)) := rfl
  rw [e, hc] <;> rfl

theorem rw_u2 : RW (fi23U2T orbLit) u2W := by
  unfold fi23U2T
  exact (rw_compT rw_dTab (rw_compT (rw_genTables (z := 1) (by decide))
    (rw_compT rw_dTab (rw_genTables (z := -1) (by decide))))).word (by decide)

theorem rw_u3 : RW (fi23U3T orbLit) u3W := by
  have hW : RW (wordT 31671 (genTables orbLit) fi23WordW) WWn :=
    (rw_wordT fi23WordW (by decide)).word (by decide)
  unfold fi23U3T
  exact rw_compT rw_u2 (rw_compT hW (rw_compT rw_dTab (rw_invT dP_sq hW)))

theorem rep_ok : fi23RepOK orbLit = true := by
  obtain ⟨-, -, -, h4, h5, h6, h7, -, -⟩ := base_facts
  have hW : RW (wordT 31671 (genTables orbLit) fi23WordW) WWn :=
    (rw_wordT fi23WordW (by decide)).word (by decide)
  have f2 : (List.range 31671).countP (fxW G u2W) = 695 := by
    have h := rep2_ok
    unfold rep2 u2Cnt at h
    rw [← cntS_zero]
    exact Nat.eq_of_beq_eq_true h
  have f3 : (List.range 31671).countP (fxW G u3W) = 183 := by
    have ha := rep3a_ok
    have hb := rep3b_ok
    unfold rep3a u3Cnt at ha
    unfold rep3b u3Cnt at hb
    replace ha := Nat.eq_of_beq_eq_true ha
    replace hb := Nat.eq_of_beq_eq_true hb
    have s := cntS_add (fxW G u3W) 0 23684 7987
    simp only [Nat.zero_add, Nat.reduceAdd] at s
    rw [← cntS_zero]
    omega
  unfold fi23RepOK fi23Fix
  rw [rw_invOK dP_sq hW,
    (rw_compT rw_u2 rw_u2).beq rw_idT (wp_eq_of_eqB h4 (ok_append ok_u2 ok_u2) (by decide)),
    rw_u2.isIdT_false h6, rw_u2.countP, f2,
    (rw_compT rw_u3 rw_u3).beq rw_idT (wp_eq_of_eqB h5 (ok_append ok_u3 ok_u3) (by decide)),
    rw_u3.isIdT_false h7, rw_u3.countP, f3] <;> rfl

theorem cnt_case2 : (List.range 31671).countP (cmQ wXC cw2) = 2 := by
  have ha := wit2a_ok
  have hb := wit2b_ok
  have hc := wit2c_ok
  have hd := wit2d_ok
  unfold wit2a c2Cnt at ha
  unfold wit2b c2Cnt at hb
  unfold wit2c c2Cnt at hc
  unfold wit2d c2Cnt at hd
  replace ha := Nat.eq_of_beq_eq_true ha
  replace hb := Nat.eq_of_beq_eq_true hb
  replace hc := Nat.eq_of_beq_eq_true hc
  replace hd := Nat.eq_of_beq_eq_true hd
  have s1 := cntS_add (cmQ wXC cw2) 0 8727 8889
  have s2 := cntS_add (cmQ wXC cw2) 0 17616 9465
  have s3 := cntS_add (cmQ wXC cw2) 0 27081 4590
  simp only [Nat.zero_add, Nat.reduceAdd] at s1 s2 s3
  rw [← cntS_zero]
  omega

theorem wit_ok : fi23WitChecks orbLit = true := by
  obtain ⟨-, h2, h3, -, -, -, -, -, -⟩ := base_facts
  have c1 : (List.range 31671).countP (cmQ wX cw1) = 2 := by
    have h := wit1_ok
    unfold wit1 c1Cnt at h
    replace h := Nat.eq_of_beq_eq_true h
    rw [← cntS_zero, h]
  unfold fi23WitChecks
  rw [caseOK_of rw_X 2 2 3 true true false h2 c1,
    caseOK_of rw_XC 30 9 9 false false false h3 cnt_case2, rep_ok] <;> rfl

end CertificateChecks.KernelFi23R

end
