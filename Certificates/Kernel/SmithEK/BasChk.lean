module

public import Certificates.Data.Kernel.SmithEKI
public import Certificates.Kernel.SmithEK.Bas
public import Certificates.Kernel.SmithEK.Pts
public import Certificates.Kernel.SmithEK.Tab
public import Certificates.Kernel.SmithEK.SplitGlue
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem bs_ok_p0 : basOKp cT.L (CFSG.KC.SliceGlue.slice pts.L (0 * 99) 99) (bs.L.drop (0 * 99)) =
    true := by
  quickRfl

theorem bs_ok_p1 : basOKp cT.L (CFSG.KC.SliceGlue.slice pts.L (1 * 99) 99) (bs.L.drop (1 * 99)) =
    true := by
  quickRfl

theorem bs_ok_p2 : basOKp cT.L (CFSG.KC.SliceGlue.slice pts.L (2 * 99) 99) (bs.L.drop (2 * 99)) =
    true := by
  quickRfl

theorem bs_ok_p3 : basOKp cT.L (CFSG.KC.SliceGlue.slice pts.L (3 * 99) 99) (bs.L.drop (3 * 99)) =
    true := by
  quickRfl

theorem bs_ok_p4 : basOKp cT.L (CFSG.KC.SliceGlue.slice pts.L (4 * 99) 99) (bs.L.drop (4 * 99)) =
    true := by
  quickRfl

theorem bs_ok_p5 : basOKp cT.L (CFSG.KC.SliceGlue.slice pts.L (5 * 99) 99) (bs.L.drop (5 * 99)) =
    true := by
  quickRfl

theorem bs_ok_p6 : basOKp cT.L (CFSG.KC.SliceGlue.slice pts.L (6 * 99) 99) (bs.L.drop (6 * 99)) =
    true := by
  quickRfl

theorem bs_ok : basOK cT.L pts.L bs.L = true :=
  basOK_of_slices cT.L 99 7 pts.L bs.L (Nat.eq_of_beq_eq_true (by quickRfl))
    (fun j hj => match j, hj with
    | 0, _ => bs_ok_p0
    | 1, _ => bs_ok_p1
    | 2, _ => bs_ok_p2
    | 3, _ => bs_ok_p3
    | 4, _ => bs_ok_p4
    | 5, _ => bs_ok_p5
    | 6, _ => bs_ok_p6
    | _ + 7, h => absurd h (by omega)) (by quickRfl)

theorem c21107neg_bas : basRow cT.L (pts.L.getD 5 0) ((bs.L.getD 5 []).set 2 0) = false := by
  decide +kernel

end CertificateChecks.KernelSmithEK
