module

public import Certificates.Kernel.Fi22.Cone
public import Certificates.Kernel.Fi22.Bray
public import CFSG.Certificates.Kernel.Fi22.Bound.Data.Cov
import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.C_L
import CFSG.Certificates.Kernel.Fi22.Bound2.Checks.M
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelFi22

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.KC.Fi22K CFSG.KC.Fi22B.Cov CFSG.Certificates
  CFSG.Certificates.LCE CFSG.Certificates.Fi22Kill CertificateChecks.KernelCo2

theorem omI_wf : wf4 omI = true := by quickRfl
theorem om2I_wf : wf4 om2I = true := by quickRfl
theorem A_wf : wf4 CFSG.KD.Fi22BC3.A = true := by quickRfl

theorem dec4_mul {X Y Z : ℕ} (hX : wf4 X = true) (hY : wf4 Y = true) (h : Nat.beq (mul4 X Y) Z = true) :
    dec4 X * dec4 Y = dec4 Z := by
  rw [← (mul4_sound hX hY).2, Nat.eq_of_beq_eq_true h]

@[expose] noncomputable def Wu : GL4 :=
  ⟨dec4 omI, dec4 om2I, by rw [dec4_mul omI_wf om2I_wf (by quickRfl), dec4_one],
    by rw [dec4_mul om2I_wf omI_wf (by quickRfl), dec4_one]⟩

@[expose] noncomputable def Au : GL4 := unit4 CFSG.KD.Fi22BC3.A A_wf (by quickRfl)

theorem Wu_val : ((Wu : GL4) : Matrix (Fin 27) (Fin 27) F4) = dec4 omI := rfl
theorem Au_val : ((Au : GL4) : Matrix (Fin 27) (Fin 27) F4) = dec4 CFSG.KD.Fi22BC3.A := rfl

theorem Wu_sq : ((Wu ^ 2 : GL4) : Matrix (Fin 27) (Fin 27) F4) = dec4 om2I := by
  rw [show Wu ^ 2 = Wu * Wu from pow_two Wu, Units.val_mul, Wu_val, dec4_mul omI_wf omI_wf (by quickRfl)]

theorem Wu_cube : Wu ^ 3 = 1 := by
  apply Units.ext
  rw [show Wu ^ 3 = Wu ^ 2 * Wu from pow_succ Wu 2, Units.val_mul, Wu_sq, Wu_val,
    dec4_mul om2I_wf omI_wf (by quickRfl), dec4_one, Units.val_one]

theorem Au_sq : Au ^ 2 = 1 := by
  apply Units.ext
  rw [show Au ^ 2 = Au * Au from pow_two Au, Units.val_mul, Au_val, dec4_mul A_wf A_wf (by quickRfl),
    dec4_one, Units.val_one]

theorem Wu_comm : Commute Wu Au := by
  change Wu * Au = Au * Wu
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Wu_val, Au_val,
    dec4_mul omI_wf A_wf (Z := mul4 CFSG.KD.Fi22BC3.A omI) (by quickRfl),
    dec4_mul A_wf omI_wf (Z := mul4 CFSG.KD.Fi22BC3.A omI) (by quickRfl)]

abbrev TT : Type := GL4 × Multiplicative (ZMod 2) × Multiplicative (Fin 7 → ℤ)

@[expose] noncomputable def Phi : Multiplicative (Fin 10 → ℤ) →* TT where
  toFun v := (Wu ^ (Multiplicative.toAdd v 0) * Au ^ (Multiplicative.toAdd v 1),
    Multiplicative.ofAdd (((Multiplicative.toAdd v 2 : ℤ)) : ZMod 2),
    Multiplicative.ofAdd (fun q : Fin 7 => Multiplicative.toAdd v ⟨q.val + 3, by omega⟩))
  map_one' := by
    simp only [toAdd_one, Pi.zero_apply, zpow_zero, mul_one, Int.cast_zero, ofAdd_zero]
    rfl
  map_mul' a b := by
    simp only [toAdd_mul, Pi.add_apply, zpow_add, Int.cast_add, ofAdd_add, Prod.mk_mul_mk]
    refine Prod.ext ?_ (Prod.ext rfl rfl)
    change Wu ^ _ * Wu ^ _ * (Au ^ _ * Au ^ _) = Wu ^ _ * Au ^ _ * (Wu ^ _ * Au ^ _)
    calc Wu ^ (Multiplicative.toAdd a 0) * Wu ^ (Multiplicative.toAdd b 0) *
          (Au ^ (Multiplicative.toAdd a 1) * Au ^ (Multiplicative.toAdd b 1))
        = Wu ^ (Multiplicative.toAdd a 0) * (Wu ^ (Multiplicative.toAdd b 0) * Au ^ (Multiplicative.toAdd a 1)) *
          Au ^ (Multiplicative.toAdd b 1) := by group
      _ = Wu ^ (Multiplicative.toAdd a 0) * (Au ^ (Multiplicative.toAdd a 1) * Wu ^ (Multiplicative.toAdd b 0)) *
          Au ^ (Multiplicative.toAdd b 1) := by rw [(Wu_comm.zpow_zpow _ _).eq]
      _ = _ := by group

@[expose] noncomputable def ThL : LG →* TT := psiL.prod (parL.prod nvL)

theorem Phi_congr {v w : Fin 10 → ℤ} (h0 : v 0 % 3 = w 0 % 3) (h1 : v 1 % 2 = w 1 % 2)
    (h2 : v 2 % 2 = w 2 % 2) (h3 : ∀ q : Fin 7, v ⟨q.val + 3, by omega⟩ = w ⟨q.val + 3, by omega⟩) :
    Phi (Multiplicative.ofAdd v) = Phi (Multiplicative.ofAdd w) := by
  simp only [Phi, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change Wu ^ v 0 * Au ^ v 1 = Wu ^ w 0 * Au ^ w 1
    rw [zpow_eq_zpow_emod (v 0) (n := 3) (by exact_mod_cast Wu_cube), h0,
      ← zpow_eq_zpow_emod (w 0) (n := 3) (by exact_mod_cast Wu_cube),
      zpow_eq_zpow_emod (v 1) (n := 2) (by exact_mod_cast Au_sq), h1,
      ← zpow_eq_zpow_emod (w 1) (n := 2) (by exact_mod_cast Au_sq)]
  · change Multiplicative.ofAdd ((v 2 : ℤ) : ZMod 2) = Multiplicative.ofAdd ((w 2 : ℤ) : ZMod 2)
    rw [← ZMod.intCast_mod (v 2) 2, ← ZMod.intCast_mod (w 2) 2]
    exact_mod_cast congrArg (fun z : ℤ => Multiplicative.ofAdd (z : ZMod 2)) h2
  · change Multiplicative.ofAdd _ = Multiplicative.ofAdd _
    congr 1
    funext q
    exact h3 q

theorem rowOK_spec {V r : ℕ} (h : rowOK CFSG.KD.Fi22BC3.A V r = true) :
    Nat.land r 3 < 3 ∧ aX V = mul4 (omK (Nat.land r 3))
      (Bool.rec (motive := fun _ => Nat) CFSG.KD.Fi22BC3.A one4 (Nat.beq (Nat.land (Nat.shiftRight r 2) 1) 0)) ∧
      aP V = Nat.land (Nat.shiftRight r 3) 1 ∧ aN V = Nat.shiftRight r 4 := by
  obtain ⟨h1, h2⟩ := KB.andB_true h
  obtain ⟨h3, h4⟩ := KB.andB_true h2
  obtain ⟨h5, h6⟩ := KB.andB_true h4
  exact ⟨by simpa using h1, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6⟩

theorem omK_mat (k : ℕ) (hk : k < 3) :
    ((Wu ^ (k : ℤ) : GL4) : Matrix (Fin 27) (Fin 27) F4) = dec4 (omK k) ∧ wf4 (omK k) = true := by
  interval_cases k
  · exact ⟨by simp only [Nat.cast_zero, zpow_zero, Units.val_one, show omK 0 = one4 from rfl, dec4_one],
      by quickRfl⟩
  · exact ⟨by simp only [Nat.cast_one, zpow_one, Wu_val]; rfl, by quickRfl⟩
  · exact ⟨by rw [zpow_natCast, Wu_sq]; rfl, by quickRfl⟩

@[expose] def vecR (k e p : ℕ) (n : Fin 7 → ℤ) : Fin 10 → ℤ := ![k, e, p, n 0, n 1, n 2, n 3, n 4, n 5, n 6]

theorem Phi_vecR (k e p : ℕ) (n : Fin 7 → ℤ) :
    Phi (Multiplicative.ofAdd (vecR k e p n)) = (Wu ^ (k : ℤ) * Au ^ (e : ℤ),
      Multiplicative.ofAdd (((p : ℤ)) : ZMod 2), Multiplicative.ofAdd n) := by
  simp only [Phi, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
  refine Prod.ext rfl (Prod.ext rfl ?_)
  change Multiplicative.ofAdd _ = Multiplicative.ofAdd n
  congr 1
  funext q
  fin_cases q <;> rfl

theorem cyc_of {c wid R V r : ℕ}
    (hcyc : cycOK CFSG.KD.Fi22KC.blk CFSG.KD.Fi22KC.selWT CFSG.KD.Fi22KC.LB (nat_lit 11135) c wid R V = true)
    (hc : c < 2 ^ 20) (hVX : Nat.blt (nat_lit 0) (aX V) = true) (hVN : nOK (aN V) = true)
    (hrow : rowOK CFSG.KD.Fi22BC3.A V r = true) (k e p : ℕ) (n : Fin 7 → ℤ)
    (hk : Nat.land r 3 = k) (he : Nat.land (Nat.shiftRight r 2) 1 = e) (he2 : e < 2)
    (hp : Nat.land (Nat.shiftRight r 3) 1 = p) (hn : decN (Nat.shiftRight r 4) = n)
    (hwid : wid < 512 := by decide) :
    ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR k e p n)) := by
  obtain ⟨ν, h1, h2, h3, h4⟩ := cone_cycle hcyc hc hVX hVN hwid
  obtain ⟨r1, r2, r3, r4⟩ := rowOK_spec hrow
  rw [hk] at r1 r2
  rw [he] at r2
  rw [hp] at r3
  refine ⟨ν, h1, ?_⟩
  rw [Phi_vecR]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change psiL ν = Wu ^ (k : ℤ) * Au ^ (e : ℤ)
    apply Units.ext
    rw [h2, r2]
    obtain ⟨m1, m2⟩ := omK_mat _ r1
    have hA : wf4 (Bool.rec (motive := fun _ => Nat) CFSG.KD.Fi22BC3.A one4 (Nat.beq e 0)) = true := by
      cases Nat.beq e 0
      · exact A_wf
      · exact wf4_one
    rw [(mul4_sound m2 hA).2, Units.val_mul, ← m1]
    congr 1
    rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl
    · simp [dec4_one]
    · simp only [Nat.cast_one, zpow_one, Au_val]
      rfl
  · change parL ν = _
    rw [h3, r3]
    simp
  · change nvL ν = _
    rw [h4, r4, hn]

theorem cyc0 : ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR 0 0 0 ![2, 0, 0, 0, 0, 0, 0])) :=
  cyc_of CFSG.KD.Fi22KC.sY0 (by norm_num) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KM.row0 0 0 0 _
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) (by norm_num)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (by funext q; fin_cases q <;> decide +kernel)

theorem cyc1 : ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR 2 0 0 ![0, 0, 2, 0, 0, 0, 0])) :=
  cyc_of CFSG.KD.Fi22KC.sY1 (by norm_num) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KM.row1 2 0 0 _
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) (by norm_num)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (by funext q; fin_cases q <;> decide +kernel)

theorem cyc2 : ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR 1 0 0 ![0, 2, 0, 0, 0, 0, 0])) :=
  cyc_of CFSG.KD.Fi22KC.sY2 (by norm_num) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KM.row2 1 0 0 _
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) (by norm_num)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (by funext q; fin_cases q <;> decide +kernel)

theorem cyc3 : ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR 2 0 0 ![(-2), 0, 0, 2, 2, (-2), 0])) :=
  cyc_of CFSG.KD.Fi22KC.sY3 (by norm_num) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KM.row3 2 0 0 _
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) (by norm_num)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (by funext q; fin_cases q <;> decide +kernel)

theorem cyc4 : ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR 0 0 1 ![3, 3, 0, (-3), (-3), 3, 0])) :=
  cyc_of CFSG.KD.Fi22KC.sY4 (by norm_num) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KM.row4 0 0 1 _
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) (by norm_num)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (by funext q; fin_cases q <;> decide +kernel)

theorem cyc5 : ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR 0 0 0 ![0, (-3), 3, 0, 0, 0, 0])) :=
  cyc_of CFSG.KD.Fi22KC.sY5 (by norm_num) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KM.row5 0 0 0 _
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) (by norm_num)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (by funext q; fin_cases q <;> decide +kernel)

theorem cyc6 : ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR 0 0 0 ![2, 0, 0, 3, 3, (-3), 0])) :=
  cyc_of CFSG.KD.Fi22KC.sY6 (by norm_num) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KM.row6 0 0 0 _
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) (by norm_num)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (by funext q; fin_cases q <;> decide +kernel)

theorem cyc7 : ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR 0 1 1 ![0, 3, 0, 0, 0, 0, 0])) :=
  cyc_of CFSG.KD.Fi22KC.sY7 (by norm_num) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KM.row7 0 1 1 _
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) (by norm_num)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (by funext q; fin_cases q <;> decide +kernel)

theorem cyc8 : ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR 0 0 0 ![(-6), 0, 0, 0, 0, (-2), (-4)])) :=
  cyc_of CFSG.KD.Fi22KC.sY8 (by norm_num) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KM.row8 0 0 0 _
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) (by norm_num)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (by funext q; fin_cases q <;> decide +kernel)

theorem cyc9 : ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR 0 0 0 ![(-12), 0, 0, 3, 3, (-6), (-6)])) :=
  cyc_of CFSG.KD.Fi22KC.sY9 (by norm_num) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KM.row9 0 0 0 _
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) (by norm_num)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (by funext q; fin_cases q <;> decide +kernel)

theorem cyc10 : ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR 2 0 0 ![(-4), 0, 0, (-2), 2, 2, 8])) :=
  cyc_of CFSG.KD.Fi22KC.sY10 (by norm_num) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KM.row10 2 0 0 _
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) (by norm_num)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (by funext q; fin_cases q <;> decide +kernel)

theorem cyc11 : ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR 0 0 0 ![(-6), 3, (-6), (-3), 3, 3, 12])) :=
  cyc_of CFSG.KD.Fi22KC.sY11 (by norm_num) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KM.row11 0 0 0 _
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) (by norm_num)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (by funext q; fin_cases q <;> decide +kernel)

theorem cyc12 : ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR 0 0 0 ![6, (-4), (-2), 4, 6, (-3), 2])) :=
  cyc_of CFSG.KD.Fi22KC.sY12 (by norm_num) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KM.row12 0 0 0 _
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) (by norm_num)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (by funext q; fin_cases q <;> decide +kernel)

theorem cyc13 : ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR 1 1 1 ![(-84), 95, (-29), (-63), (-95), 40, (-61)])) :=
  cyc_of CFSG.KD.Fi22KC.sY13 (by norm_num) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KM.row13 1 1 1 _
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) (by norm_num)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (by funext q; fin_cases q <;> decide +kernel)

theorem cyc14 : ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR 2 0 0 ![74, (-82), 32, 32, 51, 0, 48])) :=
  cyc_of CFSG.KD.Fi22KC.sY14 (by norm_num) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KM.row14 2 0 0 _
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) (by norm_num)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (by funext q; fin_cases q <;> decide +kernel)

theorem cyc15 : ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (vecR 0 0 1 ![14, 14, (-28), 14, (-7), 0, 14])) :=
  cyc_of CFSG.KD.Fi22KC.sY15 (by norm_num) (by quickRfl) (by quickRfl) CFSG.KD.Fi22KM.row15 0 0 1 _
    (Nat.eq_of_beq_eq_true (by quickRfl)) (Nat.eq_of_beq_eq_true (by quickRfl)) (by norm_num)
    (Nat.eq_of_beq_eq_true (by quickRfl)) (by funext q; fin_cases q <;> decide +kernel)

@[expose] def rowV : Fin 16 → Fin 10 → ℤ := ![vecR 0 0 0 ![2, 0, 0, 0, 0, 0, 0],
  vecR 2 0 0 ![0, 0, 2, 0, 0, 0, 0],
  vecR 1 0 0 ![0, 2, 0, 0, 0, 0, 0],
  vecR 2 0 0 ![(-2), 0, 0, 2, 2, (-2), 0],
  vecR 0 0 1 ![3, 3, 0, (-3), (-3), 3, 0],
  vecR 0 0 0 ![0, (-3), 3, 0, 0, 0, 0],
  vecR 0 0 0 ![2, 0, 0, 3, 3, (-3), 0],
  vecR 0 1 1 ![0, 3, 0, 0, 0, 0, 0],
  vecR 0 0 0 ![(-6), 0, 0, 0, 0, (-2), (-4)],
  vecR 0 0 0 ![(-12), 0, 0, 3, 3, (-6), (-6)],
  vecR 2 0 0 ![(-4), 0, 0, (-2), 2, 2, 8],
  vecR 0 0 0 ![(-6), 3, (-6), (-3), 3, 3, 12],
  vecR 0 0 0 ![6, (-4), (-2), 4, 6, (-3), 2],
  vecR 1 1 1 ![(-84), 95, (-29), (-63), (-95), 40, (-61)],
  vecR 2 0 0 ![74, (-82), 32, 32, 51, 0, 48],
  vecR 0 0 1 ![14, 14, (-28), 14, (-7), 0, 14]]

theorem cycles : ∃ ν : Fin 16 → LG, ∀ k, piL (ν k) = 1 ∧ ThL (ν k) = Phi (Multiplicative.ofAdd (rowV k)) := by
  have h : ∀ k : Fin 16, ∃ ν : LG, piL ν = 1 ∧ ThL ν = Phi (Multiplicative.ofAdd (rowV k)) := by
    intro k
    fin_cases k
    · exact cyc0
    · exact cyc1
    · exact cyc2
    · exact cyc3
    · exact cyc4
    · exact cyc5
    · exact cyc6
    · exact cyc7
    · exact cyc8
    · exact cyc9
    · exact cyc10
    · exact cyc11
    · exact cyc12
    · exact cyc13
    · exact cyc14
    · exact cyc15
  choose ν hν using h
  exact ⟨ν, hν⟩

theorem comb_pi {ν : Fin 16 → LG} (h : ∀ k, piL (ν k) = 1) (c : Fin 16 → ℤ) :
    piL (List.ofFn fun k => ν k ^ c k).prod = 1 := by
  rw [map_list_prod, List.map_ofFn]
  simp [Function.comp_def, map_zpow, h]

theorem comb_th {ν : Fin 16 → LG} (h : ∀ k, ThL (ν k) = Phi (Multiplicative.ofAdd (rowV k))) (c : Fin 16 → ℤ) :
    ThL (List.ofFn fun k => ν k ^ c k).prod = Phi (Multiplicative.ofAdd (∑ k, c k • rowV k)) := by
  rw [map_list_prod, List.map_ofFn]
  have e : (⇑ThL ∘ fun k => ν k ^ c k) = ⇑Phi ∘ fun k => Multiplicative.ofAdd (c k • rowV k) := by
    funext k
    simp only [Function.comp_apply, map_zpow, h, ofAdd_zsmul]
  rw [e, ← List.map_ofFn, ← map_list_prod, List.prod_ofFn, ofAdd_sum]

@[expose] def cf : Fin 10 → Fin 16 → ℤ := ![![37110549203734648674415294, 18975332718796902345969058, (-10234535429679453921991781), (-8734448915654015000252971), (-416883930197861296899258), 9845507857915795029713312, 20150367564640070365216996, (-1804505463490251210375468), 1853583662158563437436614, 6646753075750394480350756, (-7879452482206849427344544), 10466409618942969727496984, 0, 1804505463490251210375468, 1853583662158563437436614, 416883930197861296899258],
  ![105654529044931468345196996, 54023178985279154306654313, (-29137941744813306462175098), (-24867163285138533556862580), (-1186877485149762990247498), 28030371909224716590588186, 57368528378180347513634803, (-5137465733998936298202617), 5277192417595208191460337, 18923448479325797582871618, (-22432970112328643859265830), 29798092531852767356166355, 0, 5137465733998936298202618, 5277192417595208191460337, 1186877485149762990247497],
  ![(-87625092493940037998841611), (-44804383666209300655587069), 24165692313923452490811660, 20623701630391259580393237, 984342558291987363975178, (-23247123936739398957595628), (-47578865296361205212191132), 4260781948445022661158054, (-4376664946407069566445363), (-15694253131354796294126042), 18604891799485895726812392, (-24713191548430286824220686), 0, (-4260781948445022661158054), (-4376664946407069566445363), (-984342558291987363975177)],
  ![21130892233117309901389560, 10804628855454683986848681, (-5827584604940676053967870), (-4973429461770922088062167), (-237375344524486113744579), 5606070780137945560493370, 11473698304180892957266136, (-1027492486671325717734246), 1055437805436677247293079, 3784687264334210501109606, (-4486591139985763977962781), 5959614677523803261569109, 0, 1027492486671325717734246, 1055437805436677247293079, 237375344524486113744579],
  ![(-2575640257698291843598312), (-1316974065391477604667788), 710323130137591157083896, 606210329371888960119596, 28933633601332939136484, (-683322854025044308343826), (-1398526807619485350425679), 125240855140302682390308, (-128647104494669513573086), (-461314779010594953375424), 546869703015613920774484, (-726416249463568747260887), 0, (-125240855140302682390308), (-128647104494669513573086), (-28933633601332939136484)],
  ![13466773890250795108969, 6885818741550708269419, (-3713935187178090305674), (-3169579839880720261592), (-151279939179361863858), 3572763836755518719563, 7312218482908973856063, (-654823697896119736176), 672633323961703690012, 2411991271917140954108, (-2859316480990706413090), 3798078304022147706797, 0, 654823697896119736176, 672633323961703690012, 151279939179361863858],
  ![(-22642096154783625437), (-11577336288646840502), 6244352085067538754, 5329110898401401797, 254351558666077808, (-6006996403846622954), (-12294255130745920102), 1100974981315202578, (-1130918846798057499), (-4055354218339051663), 4807455685167328116, (-6385824464263389408), 0, (-1100974981315202578), (-1130918846798057499), (-254351558666077808)],
  ![15647665451870671, 8000950257879469, (-4315392520324788), (-3682880945476666), (-175779135905126), 4151359019740034, 8496403775991078, (-760869844414124), 781563670030289, 2802603860685194, (-3322371644477760), 4413162287099194, 0, 760869844414124, 781563670030289, 175779135905126],
  ![(-183052338367), (-93598157397), 50483102050, 43083741216, 2056331148, (-48564175808), (-99394160983), 8900944658, (-9143028896), (-32785925273), 38866366381, (-51626849944), 0, (-8900944658), (-9143028896), (-2056331148)],
  ![4576995, 2340305, (-1262267), (-1077255), (-51416), 1214287, 2485227, (-222557), 228610, 819771, (-971805), 1290865, 0, 222557, 228610, 51416]]

@[expose] def ev10 : Fin 10 → Fin 10 → ℤ := fun t i => if i = t then 1 else 0

theorem lam : ∃ l : Fin 10 → LG, ∀ t, piL (l t) = 1 ∧ ThL (l t) = Phi (Multiplicative.ofAdd (ev10 t)) := by
  obtain ⟨ν, hν⟩ := cycles
  refine ⟨fun t => (List.ofFn fun k => ν k ^ cf t k).prod, fun t => ⟨comb_pi (fun k => (hν k).1) _, ?_⟩⟩
  rw [comb_th (fun k => (hν k).2)]
  fin_cases t <;> exact Phi_congr (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

end CertificateChecks.KernelFi22

end
