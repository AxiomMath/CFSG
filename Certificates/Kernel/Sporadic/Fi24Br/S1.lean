module

public import Certificates.Kernel.Sporadic.Fi24Br.SPiece
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.BrFi24

open CFSG.KC.Ord

theorem sC7_p0 : oneIs (MS (nat_lit 8)) (progVal RB 11 RS MUL ONE [68, 60, 2, 28, 2] []) = true := by
  quickRfl

theorem sC7_p1 :
    oneIs (MS (nat_lit 9)) (progVal RB 11 RS MUL ONE [36, 2, 20, 2] [MS (nat_lit 8)]) = true := by
  quickRfl

theorem sC7_p2 :
    oneIs (RS (nat_lit 7)) (progVal RB 11 RS MUL ONE [36, 2, 44, 2] [MS (nat_lit 9)]) = true := by
  quickRfl

theorem sC7 : sC (nat_lit 7) = true := sC_of_pieces sC7_p0 sC7_p1 sC7_p2 rfl

theorem sC8_p0 : oneIs (MS (nat_lit 10)) (progVal RB 11 RS MUL ONE [29, 36, 2, 4, 2] []) = true := by
  quickRfl

theorem sC8_p1 :
    oneIs (MS (nat_lit 11)) (progVal RB 11 RS MUL ONE [84, 2, 60, 2] [MS (nat_lit 10)]) = true := by
  quickRfl

theorem sC8_p2 :
    oneIs (RS (nat_lit 8)) (progVal RB 11 RS MUL ONE [12, 2, 28, 2] [MS (nat_lit 11)]) = true := by
  quickRfl

theorem sC8 : sC (nat_lit 8) = true := sC_of_pieces sC8_p0 sC8_p1 sC8_p2 rfl

theorem sC9_p0 : oneIs (MS (nat_lit 12)) (progVal RB 11 RS MUL ONE [33, 72, 2, 36, 2] []) = true := by
  quickRfl

theorem sC9_p1 :
    oneIs (MS (nat_lit 13)) (progVal RB 11 RS MUL ONE [20, 2, 60, 2] [MS (nat_lit 12)]) = true := by
  quickRfl

theorem sC9_p2 :
    oneIs (RS (nat_lit 9)) (progVal RB 11 RS MUL ONE [52, 2, 36, 2] [MS (nat_lit 13)]) = true := by
  quickRfl

theorem sC9 : sC (nat_lit 9) = true := sC_of_pieces sC9_p0 sC9_p1 sC9_p2 rfl

theorem sC10_p0 : oneIs (MS (nat_lit 14)) (progVal RB 11 RS MUL ONE [37, 28, 2, 20, 2] []) = true := by
  quickRfl

theorem sC10_p1 :
    oneIs (MS (nat_lit 15)) (progVal RB 11 RS MUL ONE [4, 2, 60, 2] [MS (nat_lit 14)]) = true := by
  quickRfl

theorem sC10_p2 :
    oneIs (RS (nat_lit 10)) (progVal RB 11 RS MUL ONE [44, 2, 52, 2] [MS (nat_lit 15)]) = true := by
  quickRfl

theorem sC10 : sC (nat_lit 10) = true := sC_of_pieces sC10_p0 sC10_p1 sC10_p2 rfl

theorem sC11_p0 : oneIs (MS (nat_lit 16)) (progVal RB 11 RS MUL ONE [41, 44, 2, 0, 2] []) = true := by
  quickRfl

theorem sC11_p1 :
    oneIs (MS (nat_lit 17)) (progVal RB 11 RS MUL ONE [84, 2, 12, 2] [MS (nat_lit 16)]) = true := by
  quickRfl

theorem sC11_p2 :
    oneIs (RS (nat_lit 11)) (progVal RB 11 RS MUL ONE [60, 2, 36, 2] [MS (nat_lit 17)]) = true := by
  quickRfl

theorem sC11 : sC (nat_lit 11) = true := sC_of_pieces sC11_p0 sC11_p1 sC11_p2 rfl

end CFSG.KD.BrFi24

#kc_each CFSG.KD.BrFi24.sC 12 13

end
