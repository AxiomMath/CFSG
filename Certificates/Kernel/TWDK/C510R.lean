module

public import Certificates.Kernel.TWDK.D510
public import Certificates.Kernel.TWDK.RSplit
import CFSG.Certificates.Kernel.Common.EachTrue

set_option maxRecDepth 100000
set_option maxHeartbeats 0

public section

#kc_each CFSG.KD.TWDK510 r (Certificates.TWDK.kResAt 5 10 CFSG.KD.TWDK510.F CFSG.KD.TWDK510.R) 0 1

#kc_each CFSG.KD.TWDK510 r (Certificates.TWDK.kResAt 5 10 CFSG.KD.TWDK510.F CFSG.KD.TWDK510.R) 3 4

namespace CFSG.KD.TWDK510

open Certificates.TWDK

theorem r1_p0 : kResPart (nat_lit 5) (nat_lit 10) F R (nat_lit 1) (0 * 150) 150 = true := by
  quickRfl

theorem r1_p1 : kResPart (nat_lit 5) (nat_lit 10) F R (nat_lit 1) (1 * 150) 150 = true := by
  quickRfl

theorem r1_p2 : kResPart (nat_lit 5) (nat_lit 10) F R (nat_lit 1) (2 * 150) 150 = true := by
  quickRfl

theorem r1_t : kResTail (nat_lit 5) (nat_lit 10) F R (nat_lit 1) (3 * 150) = true := by
  quickRfl

theorem r1 : kResAt (nat_lit 5) (nat_lit 10) F R (nat_lit 1) = true :=
  kResAt_of_parts _ _ F R _ 3 150 (fun j hj => match j, hj with
    | 0, _ => r1_p0
    | 1, _ => r1_p1
    | 2, _ => r1_p2
    | _ + 3, h => absurd h (by omega)) r1_t

theorem r2_p0 : kResPart (nat_lit 5) (nat_lit 10) F R (nat_lit 2) (0 * 150) 150 = true := by
  quickRfl

theorem r2_p1 : kResPart (nat_lit 5) (nat_lit 10) F R (nat_lit 2) (1 * 150) 150 = true := by
  quickRfl

theorem r2_p2 : kResPart (nat_lit 5) (nat_lit 10) F R (nat_lit 2) (2 * 150) 150 = true := by
  quickRfl

theorem r2_t : kResTail (nat_lit 5) (nat_lit 10) F R (nat_lit 2) (3 * 150) = true := by
  quickRfl

theorem r2 : kResAt (nat_lit 5) (nat_lit 10) F R (nat_lit 2) = true :=
  kResAt_of_parts _ _ F R _ 3 150 (fun j hj => match j, hj with
    | 0, _ => r2_p0
    | 1, _ => r2_p1
    | 2, _ => r2_p2
    | _ + 3, h => absurd h (by omega)) r2_t

end CFSG.KD.TWDK510

end
