module

public import Certificates.Kernel.Fi23S.S12Defs
public import Certificates.Kernel.Fi23S.Fact1014
public import CFSG.Sporadic.Fi23.S12CertInputs
import Certificates.Kernel.Fi23S.S12
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23S

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KD.Fi23K CFSG.KD.Fi23S CFSG.KD.Fi23R
  CFSG.KS.Raw.Orb CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CertificateChecks.KernelFi23R
  CertificateChecks.KernelFi23M

theorem s12_facts :
    (∀ i < 10, eqB G [eS i, eS (i + 1), eS i] [eS (i + 1), eS i, eS (i + 1)] = true) ∧
    (∀ i < 11, ∀ j < 11, i + 2 ≤ j → eqB G [eS j, eS i] [eS i, eS j] = true) ∧
    eqB G (w4 ++ w4) [] = true ∧ eqB G (w6 ++ w6) [] = true ∧ wa G w4 2 ≠ 2 ∧
    wa G w6 2 ≠ 2 ∧ eqB G (invW g4 ++ wR4 ++ g4) w4 = true ∧
    eqB G (invW g6 ++ wR6 ++ g6) w6 = true := by
  have h := s12K_ok
  unfold s12K at h
  rw [bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq, bAnd_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨fun i hi => allN_iff.1 h1 i hi, fun i hi j hj hij => ?_, h3, h4, fun e => ?_,
    fun e => ?_, h7, h8⟩
  · have h2' := allN_iff.1 (allN_iff.1 h2 i hi) j hj
    have hn : ¬ j < i + 2 := by omega
    rw [bIf_eq, if_neg (by rw [Nat.blt_eq]; exact hn)] at h2'
    exact h2'
  · rw [e] at h5
    exact absurd h5 (by decide)
  · rw [e] at h6
    exact absurd h6 (by decide)

theorem eS_eq : ∀ i < 11, eS i = 128 + s12Pts[i]! := by decide

theorem okS : ∀ i < 11, okL (eS i) := by decide

theorem pts_lt : ∀ i < 11, s12Pts[i]! < 31671 := by decide

theorem ok_w4 : ∀ c ∈ w4, okL c := by decide
theorem ok_w6 : ∀ c ∈ w6, okL c := by decide
theorem ok_wR4 : ∀ c ∈ wR4, okL c := by decide
theorem ok_wR6 : ∀ c ∈ wR6, okL c := by decide


theorem rw_s {i : Nat} (hi : i < 11) : RW (s12Tab orbLit i) [eS i] := by
  unfold s12Tab
  rw [eS_eq i hi]
  exact rw_treeActTab (pts_lt i hi)

theorem ok_pair {a b : Nat} (ha : okL a) (hb : okL b) : ∀ c ∈ [a, b], okL c := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact ha
  · exact hb

theorem ok_three {a b : Nat} (ha : okL a) (hb : okL b) : ∀ c ∈ [a, b, a], okL c := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact ha

theorem braid_ok {i : Nat} (hi : i < 10) : s12Braid orbLit i = true := by
  unfold s12Braid
  have h0 := rw_s (i := i) (by omega)
  have h1 := rw_s (i := i + 1) (by omega)
  exact RW.beq (rw_compT (rw_compT h0 h1) h0) (rw_compT (rw_compT h1 h0) h1)
    (wp_eq_of_eqB ((s12_facts).1 i hi) (ok_three (okS i (by omega)) (okS (i + 1) (by omega)))
      (ok_three (okS (i + 1) (by omega)) (okS i (by omega))))

theorem comm_ok {i j : Nat} (hi : i < 11) (hj : j < 11) :
    (decide (j < i + 2) || s12Comm orbLit i j) = true := by
  by_cases h : j < i + 2
  · simp [h]
  · have hc : s12Comm orbLit i j = true := by
      unfold s12Comm
      exact RW.beq (rw_compT (rw_s hi) (rw_s hj)) (rw_compT (rw_s hj) (rw_s hi))
        (wp_eq_of_eqB ((s12_facts).2.1 i hi j hj (by omega)) (ok_pair (okS j hj) (okS i hi))
          (ok_pair (okS i hi) (okS j hj)))
    rw [hc, Bool.or_true]

theorem rw_P4 : RW (s12P4 orbLit) w4 := by
  unfold s12P4
  exact (rw_compT (rw_compT (rw_compT (rw_s (i := 0) (by norm_num)) (rw_s (i := 2) (by norm_num)))
    (rw_s (i := 4) (by norm_num))) (rw_s (i := 6) (by norm_num))).word rfl

theorem rw_P6 : RW (s12P6 orbLit) w6 := by
  unfold s12P6
  exact (rw_compT (rw_compT rw_P4 (rw_s (i := 8) (by norm_num))) (rw_s (i := 10) (by norm_num))).word
    rfl

theorem invo_of {T : Table} {w : List ℕ} (h : RW T w) (he : eqB G (w ++ w) [] = true) :
    CFSG.Sporadic.Th.Native.invoOK 31671 T = true := by
  have e := wp_eq_of_eqB he (ok_append h.2.1 h.2.1) (fun c hc => absurd hc List.not_mem_nil)
  unfold CFSG.Sporadic.Th.Native.invoOK
  rw [CFSG.KS.TW.allIn_iff]
  intro i hi
  rw [beq_iff_eq, h.ap hi, h.ap (h.tr.2 i hi).2, ← wa_append,
    ← wp_acts (w ++ w) (ok_append h.2.1 h.2.1) i hi, e, wp_nil]
  rfl

theorem nfix_of {wP g wX' u : List ℕ} (hP : ∀ c ∈ wP, okL c) (hg : ∀ c ∈ g, okL c)
    (hXo : ∀ c ∈ wX', okL c) (hu : ∀ c ∈ u, okL c)
    (he : eqB G (invW g ++ (invW u ++ wX' ++ u) ++ g) wP = true) :
    nfix (wp wP) = nfix (wp wX') := by
  have hR : ∀ c ∈ invW u ++ wX' ++ u, okL c := ok_append (ok_append (ok_invW hu) hXo) hu
  have e1 := wp_eq_of_eqB he (ok_append (ok_append (ok_invW hg) hR) hg) hP
  rw [← e1, wp_append, wp_append, wp_invW dP_sq g hg, ← mul_assoc, nfix_conj, wp_append,
    wp_append, wp_invW dP_sq u hu, ← mul_assoc, nfix_conj]

theorem fix_P4 : fixCount (s12P4 orbLit) = 183 := by
  unfold fixCount
  rw [rw_P4.countP, countP_nfix _ ok_w4]
  have hg : ∀ c ∈ g4, okL c := ok_powW (ok_append ok_w4 ok_wR4) 6
  have e := nfix_of (u := [40, 39]) ok_w4 hg ok_wXC (by decide) ((s12_facts).2.2.2.2.2.2.1)
  rw [e, ← countP_nfix _ ok_wXC, ← rw_XC.countP]
  have := counts_ok.2.2
  unfold fixCount at this
  exact this

theorem fix_P6 : fixCount (s12P6 orbLit) = 695 := by
  unfold fixCount
  rw [rw_P6.countP, countP_nfix _ ok_w6]
  have hg : ∀ c ∈ g6, okL c := ok_powW (ok_append ok_w6 ok_wR6) 2
  have e := nfix_of (u := [40, 39, 40]) ok_w6 hg ok_wX (by decide) ((s12_facts).2.2.2.2.2.2.2)
  rw [e, ← countP_nfix _ ok_wX, ← rw_X.countP]
  have := counts_ok.2.1
  unfold fixCount at this
  exact this

theorem s12_main : s12Checks orbLit = true := by
  obtain ⟨-, -, h3, h4, h5, h6, -, -⟩ := s12_facts
  unfold s12Checks
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, invo_of rw_P4 h3⟩, ?_⟩, ?_⟩, invo_of rw_P6 h4⟩, ?_⟩, ?_⟩
  · rw [CFSG.KS.TW.allIn_iff]
    intro i hi
    exact decide_eq_true (pts_lt i hi)
  · rw [CFSG.KS.TW.allIn_iff]
    intro i hi
    exact braid_ok hi
  · rw [CFSG.KS.TW.allIn_iff]
    intro i hi
    rw [CFSG.KS.TW.allIn_iff]
    intro j hj
    exact comm_ok hi hj
  · rw [RW.isIdT_false rw_P4 h5]
    rfl
  · rw [fix_P4]
    rfl
  · rw [RW.isIdT_false rw_P6 h6]
    rfl
  · rw [fix_P6]
    rfl

theorem s12_ok : s12Certificate = true := by
  unfold s12Certificate
  rw [orbitData_eq']
  exact s12_main

end CertificateChecks.KernelFi23S

end
