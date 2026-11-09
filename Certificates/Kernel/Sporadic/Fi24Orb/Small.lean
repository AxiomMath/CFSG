module

import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
public import Certificates.Kernel.Sporadic.Fi24Orb.Data
public import Certificates.Data.Kernel.Spor.Fi24OrbP

#kc_repo #kc_ktree CFSG.KD.Fi24Orb MAB "Certificates/Kernel/Sporadic/Fi24Orb/data/abpow.bin" 152491 4 1067437
  8636394970179043979

public section

namespace CFSG.KD.Fi24Orb

open CFSG.KC.Fi24Orb CFSG.KC.Fi24FixK

open CFSG.KC.Ord (notB)

theorem a_sq : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 23) (CFSG.KD.BrFi24.RB 23))
    CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem b_cube : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 24)
    (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 24) (CFSG.KD.BrFi24.RB 24))) CFSG.KD.BrFi24.ONE = true := by
  quickRfl

theorem beq_pow29 {mul : Nat → Nat → Nat} {X0 X X2 X4 X8 X16 U V Z : Nat}
    (h1 : Nat.beq X0 X = true) (h2 : Nat.beq (mul X X) X2 = true)
    (h4 : Nat.beq (mul X2 X2) X4 = true) (h8 : Nat.beq (mul X4 X4) X8 = true)
    (h16 : Nat.beq (mul X8 X8) X16 = true) (hu : Nat.beq (mul X4 X) U = true)
    (hv : Nat.beq (mul X8 U) V = true) (hz : Nat.beq (mul X16 V) Z = true) :
    Nat.beq (pow29 mul X0) Z = true := by
  have hs : ∀ (y : Nat) (k : Nat → Nat), CFSG.KC.Loop.strictN y k = k y := by
    intro y k; cases y <;> rfl
  rw [Nat.eq_of_beq_eq_true h1]
  simp only [pow29, hs]
  rw [Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h8,
    Nat.eq_of_beq_eq_true h16, Nat.eq_of_beq_eq_true hu, Nat.eq_of_beq_eq_true hv]
  exact hz

theorem ab_pow_x : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 23) (CFSG.KD.BrFi24.RB 24))
    (MAB (nat_lit 0)) = true := by quickRfl

theorem ab_pow_2 : Nat.beq (CFSG.KD.BrFi24.MUL (MAB (nat_lit 0)) (MAB (nat_lit 0)))
    (MAB (nat_lit 1)) = true := by quickRfl

theorem ab_pow_4 : Nat.beq (CFSG.KD.BrFi24.MUL (MAB (nat_lit 1)) (MAB (nat_lit 1)))
    (MAB (nat_lit 2)) = true := by quickRfl

theorem ab_pow_8 : Nat.beq (CFSG.KD.BrFi24.MUL (MAB (nat_lit 2)) (MAB (nat_lit 2)))
    (MAB (nat_lit 3)) = true := by quickRfl

theorem ab_pow_16 : Nat.beq (CFSG.KD.BrFi24.MUL (MAB (nat_lit 3)) (MAB (nat_lit 3)))
    (MAB (nat_lit 4)) = true := by quickRfl

theorem ab_pow_u : Nat.beq (CFSG.KD.BrFi24.MUL (MAB (nat_lit 2)) (MAB (nat_lit 0)))
    (MAB (nat_lit 5)) = true := by quickRfl

theorem ab_pow_v : Nat.beq (CFSG.KD.BrFi24.MUL (MAB (nat_lit 3)) (MAB (nat_lit 5)))
    (MAB (nat_lit 6)) = true := by quickRfl

theorem ab_pow_z : Nat.beq (CFSG.KD.BrFi24.MUL (MAB (nat_lit 4)) (MAB (nat_lit 6)))
    CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem ab_pow : Nat.beq (pow29 CFSG.KD.BrFi24.MUL
    (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 23) (CFSG.KD.BrFi24.RB 24))) CFSG.KD.BrFi24.ONE = true :=
  beq_pow29 ab_pow_x ab_pow_2 ab_pow_4 ab_pow_8 ab_pow_16 ab_pow_u ab_pow_v ab_pow_z

theorem a_ne : notB (Nat.beq (CFSG.KD.BrFi24.RB 23) CFSG.KD.BrFi24.ONE) = true := by quickRfl

theorem b_ne : notB (Nat.beq (CFSG.KD.BrFi24.RB 24) CFSG.KD.BrFi24.ONE) = true := by quickRfl

theorem ab_ne : notB (Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 23) (CFSG.KD.BrFi24.RB 24))
    CFSG.KD.BrFi24.ONE) = true := by quickRfl

theorem b_state : Nat.beq (CFSG.KD.BrFi24.RB 24) (CFSG.KD.BrFi24.RS 12) = true := by quickRfl

theorem n0 : Nat.beq (NM 0) (walk CFSG.KD.Fi24Fix.TG CFSG.KD.Fi24Fix.PW 0) = true := by quickRfl

theorem t10 : Nat.beq (tk CFSG.KD.Fi24Fix.TG 10 0) 0 = true := by quickRfl

theorem t5 : Nat.beq (tk CFSG.KD.Fi24Fix.TG 5 1) 2 = true := by quickRfl

theorem e1 : andB (Nat.beq (fComp (FD 2)) 1) (Nat.beq (tk CFSG.KD.Fi24Fix.TG 8 2) 2) = true := by
  quickRfl

theorem e2 : andB (Nat.beq (fComp (FD 718)) 2)
    (Nat.beq (fComp (FD (tk CFSG.KD.Fi24Fix.TG 8 718))) 2) = true := by
  quickRfl

theorem pc_inv : andB (VLD3 (RS 120)) (andB (VLD3 (RS 121))
    (Nat.beq (MUL3 (RS 120) (RS 121)) CFSG.KD.Fi23M.ONE)) = true := by quickRfl

theorem pc_a : Nat.beq (MUL3 (RS 120) (RS 31)) (MUL3 (CFSG.KD.Fi23M.RB 1) (RS 120)) = true := by
  quickRfl

theorem pc_b : Nat.beq (MUL3 (RS 120) (RS 119)) (MUL3 (CFSG.KD.Fi23M.RB 2) (RS 120)) = true := by
  quickRfl

end CFSG.KD.Fi24Orb

end
