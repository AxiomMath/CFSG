module

public import Certificates.Kernel.Sporadic.Fi24G2e.OData
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo
import Certificates.Kernel.Sporadic.Fi24Fix.Split

#kc_repo #kc_ktree CFSG.KD.Fi24G2e OWS "Certificates/Kernel/Sporadic/Fi24G2e/data/ows.bin" 152491 4 1219928
  18352582156736510332

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public noncomputable section

namespace CFSG.KD.Fi24G2e.OW

open CFSG.KD.Fi24G2e CFSG.KD.BrFi24 CFSG.KC.Fi24FixK CFSG.KC.Fi24Fix

theorem p2 : Nat.beq (walk CFSG.KD.Fi24Fix.TG OQ2 37886) 22978 = true := by quickRfl

theorem m2 : Nat.beq (wordMul MUL LG OQ2 ONE) MQ2 = true := by quickRfl

theorem c2 : Nat.beq (MUL (LG 0) MQ2) (MUL MQ2 (LG 2)) = true := by quickRfl

theorem p4 : Nat.beq (walk CFSG.KD.Fi24Fix.TG OQ4 37886) 22975 = true := by quickRfl

theorem m4_3 : Nat.beq (wordMul MUL LG [4, 3] ONE) (OWS (nat_lit 0)) = true := by
  quickRfl

theorem m4_2 : Nat.beq (wordMul MUL LG [3, 2] (OWS (nat_lit 0))) (OWS (nat_lit 1)) = true := by
  quickRfl

theorem m4_1 : Nat.beq (wordMul MUL LG [2, 1] (OWS (nat_lit 1))) (OWS (nat_lit 2)) = true := by
  quickRfl

theorem m4_0 : Nat.beq (wordMul MUL LG [1, 0] (OWS (nat_lit 2))) MQ4 = true := by
  quickRfl

theorem m4 : Nat.beq (wordMul MUL LG OQ4 ONE) MQ4 = true :=
  beq_wordMul_of_eq (w' := [1, 0] ++ ([2, 1] ++ ([3, 2] ++ ([4, 3])))) rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append m4_3 m4_2) m4_1) m4_0)

theorem c4 : Nat.beq (MUL (LG 0) MQ4) (MUL MQ4 (LG 4)) = true := by quickRfl

theorem p6 : Nat.beq (walk CFSG.KD.Fi24Fix.TG OQ6 37886) 22973 = true := by quickRfl

theorem m6_5 : Nat.beq (wordMul MUL LG [6, 5] ONE) (OWS (nat_lit 3)) = true := by
  quickRfl

theorem m6_4 : Nat.beq (wordMul MUL LG [5, 4] (OWS (nat_lit 3))) (OWS (nat_lit 4)) = true := by
  quickRfl

theorem m6_3 : Nat.beq (wordMul MUL LG [4, 3] (OWS (nat_lit 4))) (OWS (nat_lit 5)) = true := by
  quickRfl

theorem m6_2 : Nat.beq (wordMul MUL LG [3, 2] (OWS (nat_lit 5))) (OWS (nat_lit 6)) = true := by
  quickRfl

theorem m6_1 : Nat.beq (wordMul MUL LG [2, 1] (OWS (nat_lit 6))) (OWS (nat_lit 7)) = true := by
  quickRfl

theorem m6_0 : Nat.beq (wordMul MUL LG [1, 0] (OWS (nat_lit 7))) MQ6 = true := by
  quickRfl

theorem m6 : Nat.beq (wordMul MUL LG OQ6 ONE) MQ6 = true :=
  beq_wordMul_of_eq (w' := [1, 0] ++ ([2, 1] ++ ([3, 2] ++ ([4, 3] ++ ([5, 4] ++ ([6, 5])))))) rfl
    (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append (beq_wordMul_append m6_5 m6_4) m6_3) m6_2) m6_1) m6_0)

theorem c6 : Nat.beq (MUL (LG 0) MQ6) (MUL MQ6 (LG 6)) = true := by quickRfl

end CFSG.KD.Fi24G2e.OW

end
