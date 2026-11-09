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

#kc_natval sC10_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 37, nat_lit 56, nat_lit 2, nat_lit 52, nat_lit 2, nat_lit 56, nat_lit 2] [])

theorem sC10_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 37, nat_lit 56, nat_lit 2, nat_lit 52, nat_lit 2, nat_lit 56, nat_lit 2] []) sC10_v = true := by
  quickRfl

theorem sC10_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 36, nat_lit 2, nat_lit 40, nat_lit 2, nat_lit 36, nat_lit 2] [sC10_v])) (RS (nat_lit 10)) = true := by
  quickRfl

theorem sC10 : sC (nat_lit 10) = true :=
  progOK_split [nat_lit 37, nat_lit 56, nat_lit 2, nat_lit 52, nat_lit 2, nat_lit 56, nat_lit 2]
    [nat_lit 36, nat_lit 2, nat_lit 40, nat_lit 2, nat_lit 36, nat_lit 2] rfl sC10_a sC10_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC11_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 41, nat_lit 8, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 48, nat_lit 2] [])

theorem sC11_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 41, nat_lit 8, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 48, nat_lit 2] []) sC11_v = true := by
  quickRfl

theorem sC11_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 28, nat_lit 2, nat_lit 16, nat_lit 2, nat_lit 28, nat_lit 2] [sC11_v])) (RS (nat_lit 11)) = true := by
  quickRfl

theorem sC11 : sC (nat_lit 11) = true :=
  progOK_split [nat_lit 41, nat_lit 8, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 48, nat_lit 2]
    [nat_lit 28, nat_lit 2, nat_lit 16, nat_lit 2, nat_lit 28, nat_lit 2] rfl sC11_a sC11_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC12_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 45, nat_lit 40, nat_lit 2, nat_lit 20, nat_lit 2, nat_lit 48, nat_lit 2] [])

theorem sC12_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 45, nat_lit 40, nat_lit 2, nat_lit 20, nat_lit 2, nat_lit 48, nat_lit 2] []) sC12_v = true := by
  quickRfl

theorem sC12_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 12, nat_lit 2, nat_lit 16, nat_lit 2, nat_lit 60, nat_lit 2] [sC12_v])) (RS (nat_lit 12)) = true := by
  quickRfl

theorem sC12 : sC (nat_lit 12) = true :=
  progOK_split [nat_lit 45, nat_lit 40, nat_lit 2, nat_lit 20, nat_lit 2, nat_lit 48, nat_lit 2]
    [nat_lit 12, nat_lit 2, nat_lit 16, nat_lit 2, nat_lit 60, nat_lit 2] rfl sC12_a sC12_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC13_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 49, nat_lit 16, nat_lit 2, nat_lit 28, nat_lit 2, nat_lit 32, nat_lit 2] [])

theorem sC13_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 49, nat_lit 16, nat_lit 2, nat_lit 28, nat_lit 2, nat_lit 32, nat_lit 2] []) sC13_v = true := by
  quickRfl

theorem sC13_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 68, nat_lit 2, nat_lit 52, nat_lit 2, nat_lit 0, nat_lit 2] [sC13_v])) (RS (nat_lit 13)) = true := by
  quickRfl

theorem sC13 : sC (nat_lit 13) = true :=
  progOK_split [nat_lit 49, nat_lit 16, nat_lit 2, nat_lit 28, nat_lit 2, nat_lit 32, nat_lit 2]
    [nat_lit 68, nat_lit 2, nat_lit 52, nat_lit 2, nat_lit 0, nat_lit 2] rfl sC13_a sC13_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC14_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 53, nat_lit 44, nat_lit 2, nat_lit 20, nat_lit 2, nat_lit 8, nat_lit 2] [])

theorem sC14_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 53, nat_lit 44, nat_lit 2, nat_lit 20, nat_lit 2, nat_lit 8, nat_lit 2] []) sC14_v = true := by
  quickRfl

theorem sC14_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 60, nat_lit 2, nat_lit 24, nat_lit 2, nat_lit 20, nat_lit 2] [sC14_v])) (RS (nat_lit 14)) = true := by
  quickRfl

theorem sC14 : sC (nat_lit 14) = true :=
  progOK_split [nat_lit 53, nat_lit 44, nat_lit 2, nat_lit 20, nat_lit 2, nat_lit 8, nat_lit 2]
    [nat_lit 60, nat_lit 2, nat_lit 24, nat_lit 2, nat_lit 20, nat_lit 2] rfl sC14_a sC14_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC15_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 57, nat_lit 8, nat_lit 2, nat_lit 20, nat_lit 2, nat_lit 0, nat_lit 2] [])

theorem sC15_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 57, nat_lit 8, nat_lit 2, nat_lit 20, nat_lit 2, nat_lit 0, nat_lit 2] []) sC15_v = true := by
  quickRfl

theorem sC15_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 52, nat_lit 2, nat_lit 68, nat_lit 2, nat_lit 32, nat_lit 2] [sC15_v])) (RS (nat_lit 15)) = true := by
  quickRfl

theorem sC15 : sC (nat_lit 15) = true :=
  progOK_split [nat_lit 57, nat_lit 8, nat_lit 2, nat_lit 20, nat_lit 2, nat_lit 0, nat_lit 2]
    [nat_lit 52, nat_lit 2, nat_lit 68, nat_lit 2, nat_lit 32, nat_lit 2] rfl sC15_a sC15_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC16_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 61, nat_lit 40, nat_lit 2, nat_lit 68, nat_lit 2, nat_lit 16, nat_lit 2] [])

theorem sC16_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 61, nat_lit 40, nat_lit 2, nat_lit 68, nat_lit 2, nat_lit 16, nat_lit 2] []) sC16_v = true := by
  quickRfl

theorem sC16_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 56, nat_lit 2, nat_lit 44, nat_lit 2, nat_lit 64, nat_lit 2] [sC16_v])) (RS (nat_lit 16)) = true := by
  quickRfl

theorem sC16 : sC (nat_lit 16) = true :=
  progOK_split [nat_lit 61, nat_lit 40, nat_lit 2, nat_lit 68, nat_lit 2, nat_lit 16, nat_lit 2]
    [nat_lit 56, nat_lit 2, nat_lit 44, nat_lit 2, nat_lit 64, nat_lit 2] rfl sC16_a sC16_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC17_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 65, nat_lit 0, nat_lit 2, nat_lit 52, nat_lit 2, nat_lit 40, nat_lit 2] [])

theorem sC17_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 65, nat_lit 0, nat_lit 2, nat_lit 52, nat_lit 2, nat_lit 40, nat_lit 2] []) sC17_v = true := by
  quickRfl

theorem sC17_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 36, nat_lit 2, nat_lit 56, nat_lit 2, nat_lit 28, nat_lit 2] [sC17_v])) (RS (nat_lit 17)) = true := by
  quickRfl

theorem sC17 : sC (nat_lit 17) = true :=
  progOK_split [nat_lit 65, nat_lit 0, nat_lit 2, nat_lit 52, nat_lit 2, nat_lit 40, nat_lit 2]
    [nat_lit 36, nat_lit 2, nat_lit 56, nat_lit 2, nat_lit 28, nat_lit 2] rfl sC17_a sC17_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC18_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 69, nat_lit 0, nat_lit 2, nat_lit 20, nat_lit 2, nat_lit 40, nat_lit 2] [])

theorem sC18_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 69, nat_lit 0, nat_lit 2, nat_lit 20, nat_lit 2, nat_lit 40, nat_lit 2] []) sC18_v = true := by
  quickRfl

theorem sC18_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 12, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 8, nat_lit 2] [sC18_v])) (RS (nat_lit 18)) = true := by
  quickRfl

theorem sC18 : sC (nat_lit 18) = true :=
  progOK_split [nat_lit 69, nat_lit 0, nat_lit 2, nat_lit 20, nat_lit 2, nat_lit 40, nat_lit 2]
    [nat_lit 12, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 8, nat_lit 2] rfl sC18_a sC18_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC19_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 73, nat_lit 28, nat_lit 2, nat_lit 32, nat_lit 2, nat_lit 4, nat_lit 2] [])

theorem sC19_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 73, nat_lit 28, nat_lit 2, nat_lit 32, nat_lit 2, nat_lit 4, nat_lit 2] []) sC19_v = true := by
  quickRfl

theorem sC19_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 68, nat_lit 2, nat_lit 16, nat_lit 2, nat_lit 52, nat_lit 2] [sC19_v])) (RS (nat_lit 19)) = true := by
  quickRfl

theorem sC19 : sC (nat_lit 19) = true :=
  progOK_split [nat_lit 73, nat_lit 28, nat_lit 2, nat_lit 32, nat_lit 2, nat_lit 4, nat_lit 2]
    [nat_lit 68, nat_lit 2, nat_lit 16, nat_lit 2, nat_lit 52, nat_lit 2] rfl sC19_a sC19_b

end CFSG.KD.KMFi24

end
