module

public import Certificates.Kernel.TWDK.D77
public import Certificates.Kernel.TWDK.RSplit
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

namespace CFSG.KD.TWDK77

open Certificates.TWDK

theorem r0_p0 : kResPart (nat_lit 7) (nat_lit 7) F R (nat_lit 0) (0 * 168) 168 = true := by
  quickRfl

theorem r0_p1 : kResPart (nat_lit 7) (nat_lit 7) F R (nat_lit 0) (1 * 168) 168 = true := by
  quickRfl

theorem r0_p2 : kResPart (nat_lit 7) (nat_lit 7) F R (nat_lit 0) (2 * 168) 168 = true := by
  quickRfl

theorem r0_p3 : kResPart (nat_lit 7) (nat_lit 7) F R (nat_lit 0) (3 * 168) 168 = true := by
  quickRfl

theorem r0_p4 : kResPart (nat_lit 7) (nat_lit 7) F R (nat_lit 0) (4 * 168) 168 = true := by
  quickRfl

theorem r0_p5 : kResPart (nat_lit 7) (nat_lit 7) F R (nat_lit 0) (5 * 168) 168 = true := by
  quickRfl

theorem r0_p6 : kResPart (nat_lit 7) (nat_lit 7) F R (nat_lit 0) (6 * 168) 168 = true := by
  quickRfl

theorem r0_p7 : kResPart (nat_lit 7) (nat_lit 7) F R (nat_lit 0) (7 * 168) 168 = true := by
  quickRfl

theorem r0_p8 : kResPart (nat_lit 7) (nat_lit 7) F R (nat_lit 0) (8 * 168) 168 = true := by
  quickRfl

theorem r0_p9 : kResPart (nat_lit 7) (nat_lit 7) F R (nat_lit 0) (9 * 168) 168 = true := by
  quickRfl

theorem r0_p10 : kResPart (nat_lit 7) (nat_lit 7) F R (nat_lit 0) (10 * 168) 168 = true := by
  quickRfl

theorem r0_p11 : kResPart (nat_lit 7) (nat_lit 7) F R (nat_lit 0) (11 * 168) 168 = true := by
  quickRfl

theorem r0_p12 : kResPart (nat_lit 7) (nat_lit 7) F R (nat_lit 0) (12 * 168) 168 = true := by
  quickRfl

theorem r0_t : kResTail (nat_lit 7) (nat_lit 7) F R (nat_lit 0) (13 * 168) = true := by
  quickRfl

theorem r0 : kResAt (nat_lit 7) (nat_lit 7) F R (nat_lit 0) = true :=
  kResAt_of_parts _ _ F R _ 13 168 (fun j hj => match j, hj with
    | 0, _ => r0_p0
    | 1, _ => r0_p1
    | 2, _ => r0_p2
    | 3, _ => r0_p3
    | 4, _ => r0_p4
    | 5, _ => r0_p5
    | 6, _ => r0_p6
    | 7, _ => r0_p7
    | 8, _ => r0_p8
    | 9, _ => r0_p9
    | 10, _ => r0_p10
    | 11, _ => r0_p11
    | 12, _ => r0_p12
    | _ + 13, h => absurd h (by omega)) r0_t

end CFSG.KD.TWDK77

end
