module

public import Certificates.Kernel.Sporadic.Fi24KM.Split
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.NatVal

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.KMFi24

#kc_natval sC0_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 0, nat_lit 28, nat_lit 2, nat_lit 32, nat_lit 2, nat_lit 12, nat_lit 2] [])

theorem sC0_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 0, nat_lit 28, nat_lit 2, nat_lit 32, nat_lit 2, nat_lit 12, nat_lit 2] []) sC0_v = true := by
  quickRfl

theorem sC0_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 20, nat_lit 2, nat_lit 24, nat_lit 2, nat_lit 68, nat_lit 2] [sC0_v])) (RS (nat_lit 0)) = true := by
  quickRfl

theorem sC0 : sC (nat_lit 0) = true :=
  progOK_split [nat_lit 0, nat_lit 28, nat_lit 2, nat_lit 32, nat_lit 2, nat_lit 12, nat_lit 2]
    [nat_lit 20, nat_lit 2, nat_lit 24, nat_lit 2, nat_lit 68, nat_lit 2] rfl sC0_a sC0_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC1_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 1, nat_lit 24, nat_lit 2, nat_lit 60, nat_lit 2, nat_lit 64, nat_lit 2] [])

theorem sC1_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 1, nat_lit 24, nat_lit 2, nat_lit 60, nat_lit 2, nat_lit 64, nat_lit 2] []) sC1_v = true := by
  quickRfl

theorem sC1_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 44, nat_lit 2, nat_lit 64, nat_lit 2, nat_lit 4, nat_lit 2] [sC1_v])) (RS (nat_lit 1)) = true := by
  quickRfl

theorem sC1 : sC (nat_lit 1) = true :=
  progOK_split [nat_lit 1, nat_lit 24, nat_lit 2, nat_lit 60, nat_lit 2, nat_lit 64, nat_lit 2]
    [nat_lit 44, nat_lit 2, nat_lit 64, nat_lit 2, nat_lit 4, nat_lit 2] rfl sC1_a sC1_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC2_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 5, nat_lit 4, nat_lit 2, nat_lit 12, nat_lit 2, nat_lit 16, nat_lit 2] [])

theorem sC2_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 5, nat_lit 4, nat_lit 2, nat_lit 12, nat_lit 2, nat_lit 16, nat_lit 2] []) sC2_v = true := by
  quickRfl

theorem sC2_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 52, nat_lit 2, nat_lit 40, nat_lit 2, nat_lit 12, nat_lit 2] [sC2_v])) (RS (nat_lit 2)) = true := by
  quickRfl

theorem sC2 : sC (nat_lit 2) = true :=
  progOK_split [nat_lit 5, nat_lit 4, nat_lit 2, nat_lit 12, nat_lit 2, nat_lit 16, nat_lit 2]
    [nat_lit 52, nat_lit 2, nat_lit 40, nat_lit 2, nat_lit 12, nat_lit 2] rfl sC2_a sC2_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC3_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 9, nat_lit 36, nat_lit 2, nat_lit 48, nat_lit 2, nat_lit 44, nat_lit 2] [])

theorem sC3_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 9, nat_lit 36, nat_lit 2, nat_lit 48, nat_lit 2, nat_lit 44, nat_lit 2] []) sC3_v = true := by
  quickRfl

theorem sC3_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 0, nat_lit 2, nat_lit 28, nat_lit 2, nat_lit 36, nat_lit 2] [sC3_v])) (RS (nat_lit 3)) = true := by
  quickRfl

theorem sC3 : sC (nat_lit 3) = true :=
  progOK_split [nat_lit 9, nat_lit 36, nat_lit 2, nat_lit 48, nat_lit 2, nat_lit 44, nat_lit 2]
    [nat_lit 0, nat_lit 2, nat_lit 28, nat_lit 2, nat_lit 36, nat_lit 2] rfl sC3_a sC3_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC4_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 13, nat_lit 40, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 8, nat_lit 2] [])

theorem sC4_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 13, nat_lit 40, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 8, nat_lit 2] []) sC4_v = true := by
  quickRfl

theorem sC4_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 52, nat_lit 2, nat_lit 32, nat_lit 2, nat_lit 20, nat_lit 2] [sC4_v])) (RS (nat_lit 4)) = true := by
  quickRfl

theorem sC4 : sC (nat_lit 4) = true :=
  progOK_split [nat_lit 13, nat_lit 40, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 8, nat_lit 2]
    [nat_lit 52, nat_lit 2, nat_lit 32, nat_lit 2, nat_lit 20, nat_lit 2] rfl sC4_a sC4_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC5_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 17, nat_lit 64, nat_lit 2, nat_lit 52, nat_lit 2, nat_lit 56, nat_lit 2] [])

theorem sC5_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 17, nat_lit 64, nat_lit 2, nat_lit 52, nat_lit 2, nat_lit 56, nat_lit 2] []) sC5_v = true := by
  quickRfl

theorem sC5_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 28, nat_lit 2, nat_lit 16, nat_lit 2, nat_lit 28, nat_lit 2] [sC5_v])) (RS (nat_lit 5)) = true := by
  quickRfl

theorem sC5 : sC (nat_lit 5) = true :=
  progOK_split [nat_lit 17, nat_lit 64, nat_lit 2, nat_lit 52, nat_lit 2, nat_lit 56, nat_lit 2]
    [nat_lit 28, nat_lit 2, nat_lit 16, nat_lit 2, nat_lit 28, nat_lit 2] rfl sC5_a sC5_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC6_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 21, nat_lit 32, nat_lit 2, nat_lit 28, nat_lit 2, nat_lit 16, nat_lit 2] [])

theorem sC6_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 21, nat_lit 32, nat_lit 2, nat_lit 28, nat_lit 2, nat_lit 16, nat_lit 2] []) sC6_v = true := by
  quickRfl

theorem sC6_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 52, nat_lit 2, nat_lit 20, nat_lit 2, nat_lit 64, nat_lit 2] [sC6_v])) (RS (nat_lit 6)) = true := by
  quickRfl

theorem sC6 : sC (nat_lit 6) = true :=
  progOK_split [nat_lit 21, nat_lit 32, nat_lit 2, nat_lit 28, nat_lit 2, nat_lit 16, nat_lit 2]
    [nat_lit 52, nat_lit 2, nat_lit 20, nat_lit 2, nat_lit 64, nat_lit 2] rfl sC6_a sC6_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC7_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 25, nat_lit 60, nat_lit 2, nat_lit 32, nat_lit 2, nat_lit 44, nat_lit 2] [])

theorem sC7_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 25, nat_lit 60, nat_lit 2, nat_lit 32, nat_lit 2, nat_lit 44, nat_lit 2] []) sC7_v = true := by
  quickRfl

theorem sC7_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 48, nat_lit 2, nat_lit 44, nat_lit 2, nat_lit 8, nat_lit 2] [sC7_v])) (RS (nat_lit 7)) = true := by
  quickRfl

theorem sC7 : sC (nat_lit 7) = true :=
  progOK_split [nat_lit 25, nat_lit 60, nat_lit 2, nat_lit 32, nat_lit 2, nat_lit 44, nat_lit 2]
    [nat_lit 48, nat_lit 2, nat_lit 44, nat_lit 2, nat_lit 8, nat_lit 2] rfl sC7_a sC7_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC8_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 29, nat_lit 52, nat_lit 2, nat_lit 56, nat_lit 2, nat_lit 32, nat_lit 2] [])

theorem sC8_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 29, nat_lit 52, nat_lit 2, nat_lit 56, nat_lit 2, nat_lit 32, nat_lit 2] []) sC8_v = true := by
  quickRfl

theorem sC8_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 4, nat_lit 2, nat_lit 48, nat_lit 2, nat_lit 44, nat_lit 2] [sC8_v])) (RS (nat_lit 8)) = true := by
  quickRfl

theorem sC8 : sC (nat_lit 8) = true :=
  progOK_split [nat_lit 29, nat_lit 52, nat_lit 2, nat_lit 56, nat_lit 2, nat_lit 32, nat_lit 2]
    [nat_lit 4, nat_lit 2, nat_lit 48, nat_lit 2, nat_lit 44, nat_lit 2] rfl sC8_a sC8_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC9_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 33, nat_lit 64, nat_lit 2, nat_lit 44, nat_lit 2, nat_lit 0, nat_lit 2] [])

theorem sC9_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 33, nat_lit 64, nat_lit 2, nat_lit 44, nat_lit 2, nat_lit 0, nat_lit 2] []) sC9_v = true := by
  quickRfl

theorem sC9_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 52, nat_lit 2] [sC9_v])) (RS (nat_lit 9)) = true := by
  quickRfl

theorem sC9 : sC (nat_lit 9) = true :=
  progOK_split [nat_lit 33, nat_lit 64, nat_lit 2, nat_lit 44, nat_lit 2, nat_lit 0, nat_lit 2]
    [nat_lit 0, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 52, nat_lit 2] rfl sC9_a sC9_b

end CFSG.KD.KMFi24

end
