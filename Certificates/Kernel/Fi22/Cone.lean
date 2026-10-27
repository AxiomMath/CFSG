module

public import Certificates.Kernel.Fi22.Kill
import Certificates.Kernel.Fi22.Facts
import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.C_H_0
import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.C_L
import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.M
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelFi22

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.KC.Fi22K CFSG.KC.Fi22B.Cov CFSG.Certificates
  CFSG.Certificates.LCE CFSG.Certificates.Fi22Kill CertificateChecks.KernelCo2

theorem psi_mat (W n : ℕ) (h : ∀ q < n, wLet W q < 12) :
    ((psiX (bval gX W n) : GL4) : Matrix (Fin 27) (Fin 27) F4) =
      ((List.range n).map fun q => dec4 (CFSG.KD.Fi22KM.FIs (Nat.shiftRight (byte W q) 1))).prod := by
  rw [bval_map]
  unfold bval
  rw [← Units.coeHom_apply, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q hq
  have hc := h q (List.mem_range.mp hq)
  have h6 : wLet W q / 2 < 6 := by omega
  simp only [Function.comp_apply, Units.coeHom_apply]
  rw [show Nat.shiftRight (byte W q) 1 = wLet W q / 2 from Nat.shiftRight_eq_div_pow _ 1]
  unfold letV
  simp only [show ¬ wLet W q = 255 by omega, ↓reduceIte]
  split_ifs
  · rw [psiX_gX h6]
    rfl
  · rw [psiX_gX h6, uG_inv]
    rfl

theorem gX_ge {k : ℕ} (hk : ¬ k < 6) : gX k = 1 := by simp [gX, pgen, hk]

theorem par_bval (W n : ℕ) (h : ∀ q < n, wLet W q < 12) : parX (bval gX W n) = one2 ^ n := by
  rw [bval_map, bval_congr (gen' := fun k => if _h : k < 6 then one2 else 1) fun k => by
    by_cases hk : k < 6
    · simp [parX_gX hk, hk]
    · simp [gX_ge hk, hk]]
  exact bval_par W n h

theorem one2_pow (n : ℕ) : one2 ^ n = Multiplicative.ofAdd ((n : ℕ) : ZMod 2) := by
  rw [one2, ← ofAdd_nsmul, nsmul_one]

theorem lab_h {j : ℕ} {R : Bool}
    (hlet : andB (Nat.beq (lX (CFSG.KD.Fi22KC.LETs j)) (evalE CFSG.KD.Fi22KM.FIs (CFSG.KD.Fi22KM.WJs j))) R = true)
    (hj : j < 7) (hST : CFSG.KD.Fi22KC.selST j = CFSG.KC.Fi22B.sub j)
    (hp : lP (CFSG.KD.Fi22KC.LETs j) % 2 = wLen (CFSG.KD.Fi22KM.WJs j) % 2)
    (hn : decN (lN (CFSG.KD.Fi22KC.LETs j)) = Pi.single ⟨j, hj⟩ 1)
    (hN : nOK (lN (CFSG.KD.Fi22KC.LETs j)) = true) :
    nOK (lN (CFSG.KD.Fi22KC.LETs j)) = true ∧ ∃ t : LG,
      piL t = bval tg (wWord (CFSG.KD.Fi22KC.selST j)) (wLen (CFSG.KD.Fi22KC.selST j)) ∧
      ((psiL t : GL4) : Matrix (Fin 27) (Fin 27) F4) = dec4 (lX (CFSG.KD.Fi22KC.LETs j)) ∧
      parL t = Multiplicative.ofAdd ((lP (CFSG.KD.Fi22KC.LETs j) : ℕ) : ZMod 2) ∧
      nvL t = Multiplicative.ofAdd (decN (lN (CFSG.KD.Fi22KC.LETs j))) := by
  have hX := Nat.eq_of_beq_eq_true (KB.andB_true hlet).1
  have hl := fun q (_ : q < wLen (CFSG.KD.Fi22KM.WJs j)) => letters_all (wj_ok j hj) (by norm_num) q
  refine ⟨hN, (xw j, Multiplicative.ofAdd (Pi.single (M := fun _ : Fin 7 => ℤ) ⟨j, hj⟩ 1)), ?_, ?_, ?_, ?_⟩
  · rw [piL_wj hj, hST]
  · change ((psiX (xw j) : GL4) : Matrix (Fin 27) (Fin 27) F4) = _
    rw [psi_mat _ _ hl, hX]
    refine ((evalE_dec _ _ fun q hq => ?_).2).symm
    rw [show Nat.shiftRight (byte (wWord (CFSG.KD.Fi22KM.WJs j)) q) 1 = wLet (wWord (CFSG.KD.Fi22KM.WJs j)) q / 2 from
      Nat.shiftRight_eq_div_pow _ 1]
    have := hl q hq
    change wLet (wWord (CFSG.KD.Fi22KM.WJs j)) q < 12 at this
    exact (fi_ok ⟨wLet (wWord (CFSG.KD.Fi22KM.WJs j)) q / 2, by omega⟩).1
  · change parX (xw j) = _
    rw [par_bval _ _ hl, one2_pow, ← ZMod.natCast_mod (wLen _), ← hp, ZMod.natCast_mod]
  · change Multiplicative.ofAdd (Pi.single (M := fun _ : Fin 7 => ℤ) ⟨j, hj⟩ 1) = _
    rw [hn]

theorem lab_e {j : ℕ} (g : ℕ) (hg : g < 6) (hj : j = 7 + g) (hST : CFSG.KD.Fi22KC.selST j = subY (7 + g))
    (hX : Nat.beq (lX (CFSG.KD.Fi22KC.LETs j)) (CFSG.KD.Fi22KM.FIs g) = true)
    (hp : lP (CFSG.KD.Fi22KC.LETs j) = 1) (hn : decN (lN (CFSG.KD.Fi22KC.LETs j)) = 0)
    (hN : nOK (lN (CFSG.KD.Fi22KC.LETs j)) = true) :
    nOK (lN (CFSG.KD.Fi22KC.LETs j)) = true ∧ ∃ t : LG,
      piL t = bval tg (wWord (CFSG.KD.Fi22KC.selST j)) (wLen (CFSG.KD.Fi22KC.selST j)) ∧
      ((psiL t : GL4) : Matrix (Fin 27) (Fin 27) F4) = dec4 (lX (CFSG.KD.Fi22KC.LETs j)) ∧
      parL t = Multiplicative.ofAdd ((lP (CFSG.KD.Fi22KC.LETs j) : ℕ) : ZMod 2) ∧
      nvL t = Multiplicative.ofAdd (decN (lN (CFSG.KD.Fi22KC.LETs j))) := by
  refine ⟨hN, (gX g, 1), ?_, ?_, ?_, ?_⟩
  · change piX (gX g) * (czPow 1 : PG) = _
    rw [czPow_zero, Subgroup.coe_one, mul_one, piX_gX hg, hST]
  · change ((psiX (gX g) : GL4) : Matrix (Fin 27) (Fin 27) F4) = _
    rw [psiX_gX hg, uG_val, Nat.eq_of_beq_eq_true hX]
  · change parX (gX g) = _
    rw [parX_gX hg, hp]
    rfl
  · change (1 : Multiplicative (Fin 7 → ℤ)) = _
    rw [hn]
    rfl

theorem dec_single (N : ℕ) (q0 : Fin 7)
    (h : ∀ q : Fin 7, Nat.land (Nat.shiftRight N (16 * q.val)) 65535 = if q = q0 then 32769 else 32768) :
    decN N = Pi.single q0 1 := by
  funext q
  simp only [decN, h q, Pi.single_apply]
  split_ifs <;> norm_num

theorem dec_zero (N : ℕ) (h : ∀ q : Fin 7, Nat.land (Nat.shiftRight N (16 * q.val)) 65535 = 32768) :
    decN N = 0 := by
  funext q
  simp only [decN, h q, Pi.zero_apply]
  norm_num

set_option maxRecDepth 100000 in
theorem hLET : ∀ j < 13, nOK (lN (CFSG.KD.Fi22KC.LETs j)) = true ∧ ∃ t : LG,
    piL t = bval tg (wWord (CFSG.KD.Fi22KC.selST j)) (wLen (CFSG.KD.Fi22KC.selST j)) ∧
    ((psiL t : GL4) : Matrix (Fin 27) (Fin 27) F4) = dec4 (lX (CFSG.KD.Fi22KC.LETs j)) ∧
    parL t = Multiplicative.ofAdd ((lP (CFSG.KD.Fi22KC.LETs j) : ℕ) : ZMod 2) ∧
    nvL t = Multiplicative.ofAdd (decN (lN (CFSG.KD.Fi22KC.LETs j))) := by
  intro j hj
  interval_cases j
  · exact lab_h CFSG.KD.Fi22KM.let0 (by decide) rfl (Nat.eq_of_beq_eq_true (by quickRfl))
      (dec_single _ _ (by decide +kernel)) (by quickRfl)
  · exact lab_h CFSG.KD.Fi22KM.let1 (by decide) rfl (Nat.eq_of_beq_eq_true (by quickRfl))
      (dec_single _ _ (by decide +kernel)) (by quickRfl)
  · exact lab_h CFSG.KD.Fi22KM.let2 (by decide) rfl (Nat.eq_of_beq_eq_true (by quickRfl))
      (dec_single _ _ (by decide +kernel)) (by quickRfl)
  · exact lab_h CFSG.KD.Fi22KM.let3 (by decide) rfl (Nat.eq_of_beq_eq_true (by quickRfl))
      (dec_single _ _ (by decide +kernel)) (by quickRfl)
  · exact lab_h CFSG.KD.Fi22KM.let4 (by decide) rfl (Nat.eq_of_beq_eq_true (by quickRfl))
      (dec_single _ _ (by decide +kernel)) (by quickRfl)
  · exact lab_h CFSG.KD.Fi22KM.let5 (by decide) rfl (Nat.eq_of_beq_eq_true (by quickRfl))
      (dec_single _ _ (by decide +kernel)) (by quickRfl)
  · exact lab_h CFSG.KD.Fi22KM.let6 (by decide) rfl (Nat.eq_of_beq_eq_true (by quickRfl))
      (dec_single _ _ (by decide +kernel)) (by quickRfl)
  · exact lab_e 0 (by norm_num) rfl rfl (by quickRfl) (Nat.eq_of_beq_eq_true (by quickRfl))
      (dec_zero _ (by decide +kernel)) (by quickRfl)
  · exact lab_e 1 (by norm_num) rfl rfl (by quickRfl) (Nat.eq_of_beq_eq_true (by quickRfl))
      (dec_zero _ (by decide +kernel)) (by quickRfl)
  · exact lab_e 2 (by norm_num) rfl rfl (by quickRfl) (Nat.eq_of_beq_eq_true (by quickRfl))
      (dec_zero _ (by decide +kernel)) (by quickRfl)
  · exact lab_e 3 (by norm_num) rfl rfl (by quickRfl) (Nat.eq_of_beq_eq_true (by quickRfl))
      (dec_zero _ (by decide +kernel)) (by quickRfl)
  · exact lab_e 4 (by norm_num) rfl rfl (by quickRfl) (Nat.eq_of_beq_eq_true (by quickRfl))
      (dec_zero _ (by decide +kernel)) (by quickRfl)
  · exact lab_e 5 (by norm_num) rfl rfl (by quickRfl) (Nat.eq_of_beq_eq_true (by quickRfl))
      (dec_zero _ (by decide +kernel)) (by quickRfl)

theorem cone_cycle {c wid R V : ℕ}
    (hcyc : cycOK CFSG.KD.Fi22KC.blk CFSG.KD.Fi22KC.selWT CFSG.KD.Fi22KC.LB (nat_lit 11135) c wid R V = true)
    (hc : c < 2 ^ 20) (hVX : Nat.blt (nat_lit 0) (aX V) = true) (hVN : nOK (aN V) = true)
    (hwid : wid < 512) :
    ∃ ν : LG, piL ν = 1 ∧ ((psiL ν : GL4) : Matrix (Fin 27) (Fin 27) F4) = dec4 (aX V) ∧
      parL ν = Multiplicative.ofAdd ((aP V : ℕ) : ZMod 2) ∧ nvL ν = Multiplicative.ofAdd (decN (aN V)) := by
  have hC := coneOk_intro (nf := nat_lit 11135) CFSG.KD.Fi22KC.sH0 CFSG.KD.Fi22KC.sH1 (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KC.sH6
    (by quickRfl) Cfacts Clab
  exact lab_sound tg piL psiL parL nvL hC (fun r => rel_all r) hLET rfl hc hcyc hVX hVN hwid

end CertificateChecks.KernelFi22

end
