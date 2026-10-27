module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Orb.Data
public import Certificates.Data.Kernel.Spor.Fi24OrbP

public section

namespace CFSG.KD.Fi24Orb

open CFSG.KC.Fi24Orb CFSG.KC.Fi24FixK

open CFSG.KC.Ord (notB)

theorem a_sq : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 23) (CFSG.KD.BrFi24.RB 23))
    CFSG.KD.BrFi24.ONE = true := by quickRfl

theorem b_cube : Nat.beq (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 24)
    (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 24) (CFSG.KD.BrFi24.RB 24))) CFSG.KD.BrFi24.ONE = true := by
  quickRfl

theorem ab_pow : Nat.beq (pow29 CFSG.KD.BrFi24.MUL
    (CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 23) (CFSG.KD.BrFi24.RB 24))) CFSG.KD.BrFi24.ONE = true := by
  quickRfl

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
