module

public import Certificates.Kernel.Sporadic.Fi24Br.SPiece
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

#kc_each CFSG.KD.BrFi24.sC 0 3

namespace CFSG.KD.BrFi24

open CFSG.KC.Ord

theorem sC3_p0 : oneIs (MS (nat_lit 0)) (progVal RB 11 RS MUL ONE [16, 12, 2, 0, 2] []) = true := by
  quickRfl

theorem sC3_p1 :
    oneIs (MS (nat_lit 1)) (progVal RB 11 RS MUL ONE [72, 2, 84, 2] [MS (nat_lit 0)]) = true := by
  quickRfl

theorem sC3_p2 :
    oneIs (RS (nat_lit 3)) (progVal RB 11 RS MUL ONE [16, 2, 28, 2] [MS (nat_lit 1)]) = true := by
  quickRfl

theorem sC3 : sC (nat_lit 3) = true := sC_of_pieces sC3_p0 sC3_p1 sC3_p2 rfl

theorem sC4_p0 : oneIs (MS (nat_lit 2)) (progVal RB 11 RS MUL ONE [13, 32, 2, 44, 2] []) = true := by
  quickRfl

theorem sC4_p1 :
    oneIs (MS (nat_lit 3)) (progVal RB 11 RS MUL ONE [64, 2, 20, 2] [MS (nat_lit 2)]) = true := by
  quickRfl

theorem sC4_p2 :
    oneIs (RS (nat_lit 4)) (progVal RB 11 RS MUL ONE [48, 2, 60, 2] [MS (nat_lit 3)]) = true := by
  quickRfl

theorem sC4 : sC (nat_lit 4) = true := sC_of_pieces sC4_p0 sC4_p1 sC4_p2 rfl

theorem sC5_p0 : oneIs (MS (nat_lit 4)) (progVal RB 11 RS MUL ONE [20, 8, 2, 4, 2] []) = true := by
  quickRfl

theorem sC5_p1 :
    oneIs (MS (nat_lit 5)) (progVal RB 11 RS MUL ONE [76, 2, 80, 2] [MS (nat_lit 4)]) = true := by
  quickRfl

theorem sC5_p2 :
    oneIs (RS (nat_lit 5)) (progVal RB 11 RS MUL ONE [20, 2, 24, 2] [MS (nat_lit 5)]) = true := by
  quickRfl

theorem sC5 : sC (nat_lit 5) = true := sC_of_pieces sC5_p0 sC5_p1 sC5_p2 rfl

theorem sC6_p0 : oneIs (MS (nat_lit 6)) (progVal RB 11 RS MUL ONE [21, 36, 2, 40, 2] []) = true := by
  quickRfl

theorem sC6_p1 :
    oneIs (MS (nat_lit 7)) (progVal RB 11 RS MUL ONE [68, 2, 16, 2] [MS (nat_lit 6)]) = true := by
  quickRfl

theorem sC6_p2 :
    oneIs (RS (nat_lit 6)) (progVal RB 11 RS MUL ONE [52, 2, 56, 2] [MS (nat_lit 7)]) = true := by
  quickRfl

theorem sC6 : sC (nat_lit 6) = true := sC_of_pieces sC6_p0 sC6_p1 sC6_p2 rfl

end CFSG.KD.BrFi24

end
