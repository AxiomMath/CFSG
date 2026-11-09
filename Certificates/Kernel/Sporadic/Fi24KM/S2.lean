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

#kc_natval sC20_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 77, nat_lit 64, nat_lit 2, nat_lit 28, nat_lit 2, nat_lit 8, nat_lit 2] [])

theorem sC20_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 77, nat_lit 64, nat_lit 2, nat_lit 28, nat_lit 2, nat_lit 8, nat_lit 2] []) sC20_v = true := by
  quickRfl

theorem sC20_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 36, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 12, nat_lit 2] [sC20_v])) (RS (nat_lit 20)) = true := by
  quickRfl

theorem sC20 : sC (nat_lit 20) = true :=
  progOK_split [nat_lit 77, nat_lit 64, nat_lit 2, nat_lit 28, nat_lit 2, nat_lit 8, nat_lit 2]
    [nat_lit 36, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 12, nat_lit 2] rfl sC20_a sC20_b

end CFSG.KD.KMFi24

#kc_each CFSG.KD.KMFi24.sC 21 23

namespace CFSG.KD.KMFi24

#kc_natval sC23_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 16, nat_lit 12, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 20, nat_lit 2] [])

theorem sC23_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 16, nat_lit 12, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 20, nat_lit 2] []) sC23_v = true := by
  quickRfl

theorem sC23_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 24, nat_lit 2, nat_lit 36, nat_lit 2, nat_lit 16, nat_lit 2] [sC23_v])) (RS (nat_lit 23)) = true := by
  quickRfl

theorem sC23 : sC (nat_lit 23) = true :=
  progOK_split [nat_lit 16, nat_lit 12, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 20, nat_lit 2]
    [nat_lit 24, nat_lit 2, nat_lit 36, nat_lit 2, nat_lit 16, nat_lit 2] rfl sC23_a sC23_b

end CFSG.KD.KMFi24

namespace CFSG.KD.KMFi24

#kc_natval sC24_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 93, nat_lit 52, nat_lit 2, nat_lit 56, nat_lit 2, nat_lit 20, nat_lit 2] [])

theorem sC24_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 93, nat_lit 52, nat_lit 2, nat_lit 56, nat_lit 2, nat_lit 20, nat_lit 2] []) sC24_v = true := by
  quickRfl

theorem sC24_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 8, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 16, nat_lit 2] [sC24_v])) (RS (nat_lit 24)) = true := by
  quickRfl

theorem sC24 : sC (nat_lit 24) = true :=
  progOK_split [nat_lit 93, nat_lit 52, nat_lit 2, nat_lit 56, nat_lit 2, nat_lit 20, nat_lit 2]
    [nat_lit 8, nat_lit 2, nat_lit 4, nat_lit 2, nat_lit 16, nat_lit 2] rfl sC24_a sC24_b

end CFSG.KD.KMFi24

#kc_each CFSG.KD.KMFi24.sC 25 26

namespace CFSG.KD.KMFi24

#kc_natval sC26_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 16, nat_lit 12, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 24, nat_lit 2] [])

theorem sC26_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 16, nat_lit 12, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 24, nat_lit 2] []) sC26_v = true := by
  quickRfl

theorem sC26_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 36, nat_lit 2, nat_lit 48, nat_lit 2, nat_lit 20, nat_lit 2] [sC26_v])) (RS (nat_lit 26)) = true := by
  quickRfl

theorem sC26 : sC (nat_lit 26) = true :=
  progOK_split [nat_lit 16, nat_lit 12, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 24, nat_lit 2]
    [nat_lit 36, nat_lit 2, nat_lit 48, nat_lit 2, nat_lit 20, nat_lit 2] rfl sC26_a sC26_b

end CFSG.KD.KMFi24

#kc_each CFSG.KD.KMFi24.sC 27 28

namespace CFSG.KD.KMFi24

#kc_natval sC28_v := CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE
  (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 16, nat_lit 12, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 24, nat_lit 2] [])

theorem sC28_a : oneOK (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 16, nat_lit 12, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 24, nat_lit 2] []) sC28_v = true := by
  quickRfl

theorem sC28_b : Nat.beq (CFSG.KC.Ord.hdN CFSG.KD.BrFi24.ONE (CFSG.KC.Ord.progVal CFSG.KD.BrFi24.RB 11 RS CFSG.KD.BrFi24.MUL CFSG.KD.BrFi24.ONE
    [nat_lit 36, nat_lit 2, nat_lit 48, nat_lit 2, nat_lit 84, nat_lit 2] [sC28_v])) (RS (nat_lit 28)) = true := by
  quickRfl

theorem sC28 : sC (nat_lit 28) = true :=
  progOK_split [nat_lit 16, nat_lit 12, nat_lit 2, nat_lit 0, nat_lit 2, nat_lit 24, nat_lit 2]
    [nat_lit 36, nat_lit 2, nat_lit 48, nat_lit 2, nat_lit 84, nat_lit 2] rfl sC28_a sC28_b

end CFSG.KD.KMFi24

end
