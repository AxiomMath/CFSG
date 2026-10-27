module

public import Certificates.Kernel.Fi22.Lattice

public section

namespace CertificateChecks.KernelFi22

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.KC.Fi22K CFSG.KC.Fi22B.Cov CFSG.Certificates
  CFSG.Certificates.LCE CFSG.Certificates.Fi22Kill CertificateChecks.KernelCo2

theorem th_parts {x : LG} {v : Fin 10 → ℤ} (h : ThL x = Phi (Multiplicative.ofAdd v)) :
    psiL x = Wu ^ v 0 * Au ^ v 1 ∧ parL x = Multiplicative.ofAdd ((v 2 : ℤ) : ZMod 2) ∧
      nvL x = Multiplicative.ofAdd (fun q : Fin 7 => v ⟨q.val + 3, by omega⟩) :=
  ⟨congrArg Prod.fst h, congrArg (fun p => p.2.1) h, congrArg (fun p => p.2.2) h⟩

theorem piL_eq (x : LG) : piL x = piX x.1 * (czPow x.2 : PG) := rfl

theorem cz_mem {q : Fin 7} {x : LG} (h1 : piL x = 1)
    (h2 : x.2 = Multiplicative.ofAdd (Pi.single (M := fun _ : Fin 7 => ℤ) q 1)) :
    (cz q : PG) ∈ piX.range := by
  rw [piL_eq, h2, czPow_single] at h1
  refine ⟨x.1⁻¹, ?_⟩
  rw [map_inv, inv_eq_of_mul_eq_one_right h1]

theorem cz_range (q : Fin 7) : (cz q : PG) ∈ piX.range := by
  obtain ⟨l, hl⟩ := lam
  have h := hl ⟨q.val + 3, by omega⟩
  refine cz_mem h.1 ?_
  have := (th_parts h.2).2.2
  change (l ⟨q.val + 3, _⟩).2 = _ at this
  rw [this]
  congr 1
  funext q'
  simp only [ev10, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> omega

theorem hb_range : HB ≤ piX.range := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  change j < 7 at hj
  have e := piL_wj hj
  rw [piL_eq] at e
  change bval tg (wWord (CFSG.KC.Fi22B.sub j)) (wLen (CFSG.KC.Fi22B.sub j)) ∈ piX.range
  rw [← e, czPow_single]
  exact piX.range.mul_mem ⟨_, rfl⟩ (cz_range _)

@[expose] noncomputable def code (i : Fin 3) (j : Fin 2) : ℕ :=
  mul4 (omK i.val) (if j.val = 0 then one4 else CFSG.KD.Fi22BC3.A)

theorem code_wf (i : Fin 3) (j : Fin 2) : wf4 (code i j) = true := by
  fin_cases i <;> fin_cases j <;> quickRfl

theorem code_mat (i : Fin 3) (j : Fin 2) :
    ((Wu ^ (i.val : ℤ) * Au ^ (j.val : ℤ) : GL4) : Matrix (Fin 27) (Fin 27) F4) = dec4 (code i j) := by
  obtain ⟨m1, m2⟩ := omK_mat i.val i.isLt
  have hA : wf4 (if j.val = 0 then one4 else CFSG.KD.Fi22BC3.A) = true := by
    split_ifs
    · exact wf4_one
    · exact A_wf
  rw [code, (mul4_sound m2 hA).2, Units.val_mul, m1]
  congr 1
  fin_cases j
  · simp [dec4_one]
  · simp [Au_val]

theorem code_inj : ∀ a b : Fin 3 × Fin 2, code a.1 a.2 = code b.1 b.2 → a = b := by decide +kernel

theorem ker_card : 12 ≤ Nat.card piX.ker := by
  obtain ⟨l, hl⟩ := lam
  have hfin : Finite XT := xt_card.1
  let y : Fin 3 × Fin 2 × Fin 2 → LG := fun a => l 0 ^ a.1.val * l 1 ^ a.2.1.val * l 2 ^ a.2.2.val
  have hy : ∀ a, piL (y a) = 1 ∧ ThL (y a) =
      Phi (Multiplicative.ofAdd (a.1.val • ev10 0 + a.2.1.val • ev10 1 + a.2.2.val • ev10 2)) := by
    intro a
    constructor
    · simp only [y, map_mul, map_pow, (hl 0).1, (hl 1).1, (hl 2).1, one_pow, mul_one]
    · have e : Multiplicative.ofAdd (a.1.val • ev10 0 + a.2.1.val • ev10 1 + a.2.2.val • ev10 2) =
          Multiplicative.ofAdd (ev10 0) ^ a.1.val * Multiplicative.ofAdd (ev10 1) ^ a.2.1.val *
            Multiplicative.ofAdd (ev10 2) ^ a.2.2.val := by
        simp only [ofAdd_add, ofAdd_nsmul]
      rw [e, map_mul, map_mul, map_pow, map_pow, map_pow]
      simp only [y, map_mul, map_pow, (hl 0).2, (hl 1).2, (hl 2).2]
  have hy2 : ∀ a, (y a).2 = 1 := by
    intro a
    have := (th_parts (hy a).2).2.2
    change (y a).2 = _ at this
    rw [this]
    rw [show (1 : Multiplicative (Fin 7 → ℤ)) = Multiplicative.ofAdd 0 from rfl]
    congr 1
    all_goals
      funext q
      simp [ev10, Fin.ext_iff]
  have hker : ∀ a, (y a).1 ∈ piX.ker := by
    intro a
    have := (hy a).1
    rw [piL_eq, hy2, czPow_zero, Subgroup.coe_one, mul_one] at this
    exact this
  have hpsi : ∀ a, psiX (y a).1 = Wu ^ (a.1.val : ℤ) * Au ^ (a.2.1.val : ℤ) := by
    intro a
    have := (th_parts (hy a).2).1
    change psiX (y a).1 = _ at this
    rw [this]
    simp [ev10]
  have hpar : ∀ a, parX (y a).1 = Multiplicative.ofAdd (((a.2.2.val : ℤ)) : ZMod 2) := by
    intro a
    have := (th_parts (hy a).2).2.1
    change parX (y a).1 = _ at this
    rw [this]
    simp [ev10]
  let f : Fin 3 × Fin 2 × Fin 2 → piX.ker := fun a => ⟨(y a).1, hker a⟩
  have hf : Function.Injective f := by
    intro a b hab
    have e : (y a).1 = (y b).1 := congrArg Subtype.val hab
    have hmat : dec4 (code a.1 a.2.1) = dec4 (code b.1 b.2.1) := by
      rw [← code_mat, ← code_mat, ← hpsi a, ← hpsi b, e]
    have hc := code_inj (a.1, a.2.1) (b.1, b.2.1) (dec4_inj (code_wf _ _) (code_wf _ _) hmat)
    have hl : ((a.2.2.val : ℤ) : ZMod 2) = ((b.2.2.val : ℤ) : ZMod 2) := by
      have h1 := hpar a
      rw [e, hpar b] at h1
      exact (Multiplicative.ofAdd.injective h1).symm
    have hl' : a.2.2 = b.2.2 := by
      revert hl
      generalize a.2.2 = u
      generalize b.2.2 = v
      fin_cases u <;> fin_cases v <;> decide
    obtain ⟨a1, a2, a3⟩ := a
    obtain ⟨b1, b2, b3⟩ := b
    simp only [Prod.mk.injEq] at hc hl' ⊢
    exact ⟨hc.1, hc.2, hl'⟩
  have := Nat.card_le_card_of_injective f hf
  simpa using this

theorem range_card : Nat.card piX.range ≤ 18393661440 := by
  obtain ⟨hfin, hcard⟩ := xt_card
  have hmul : Nat.card XT = Nat.card piX.range * Nat.card piX.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup piX.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange piX).toEquiv]
  have := ker_card
  have h12 : Nat.card piX.range * 12 ≤ 12 * 18393661440 :=
    (Nat.mul_le_mul_left _ this).trans (hmul ▸ hcard)
  omega

theorem fi22_bound : Finite PG ∧ Nat.card PG ≤ 64561751654400 := by
  have hfx : Finite XT := xt_card.1
  have hfr : Finite piX.range := Finite.of_surjective _ piX.rangeRestrict_surjective
  have hi := Subgroup.relIndex_le_of_le_left hb_range bray_index.1
  have hi0 : piX.range.relIndex ⊤ ≠ 0 := by
    intro h0
    have := Subgroup.relIndex_dvd_of_le_left (⊤ : Subgroup PG) hb_range
    rw [h0, zero_dvd_iff] at this
    exact bray_index.1 this
  have c := KB.card_le_step ⟨le_top, hi0, hi.trans bray_index.2⟩ ⟨Nat.card_pos.ne', range_card⟩
  rw [Subgroup.card_top] at c
  exact ⟨Nat.finite_of_card_ne_zero c.1, c.2.trans (by norm_num)⟩

end CertificateChecks.KernelFi22

end
