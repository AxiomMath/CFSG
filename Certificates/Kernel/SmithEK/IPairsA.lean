module

public import Certificates.Data.Kernel.SmithEKI
public import Certificates.Kernel.SmithEK.Bas
public import Certificates.Kernel.SmithEK.Pts
public import Certificates.Kernel.SmithEK.WData
public import CFSG.Certificates.Kernel.Common.EachTrue
public import Certificates.Kernel.SmithEK.SplitGlue
import CFSG.Certificates.Kernel.Common.Harness


set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem c21107pair_0_t : rowsI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 0) 87) (CFSG.KC.SliceGlue.slice pts.L (87 * 0 + 1) (87 - 1))
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 0 + 1) (87 - 1)) = true := by
  quickRfl

theorem c21107pair_0_r0 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 0 + 87)) (0 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 0 + 87)) (0 * 44) 44) = true := by
  quickRfl

theorem c21107pair_0_r1 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 0 + 87)) (1 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 0 + 87)) (1 * 44) 44) = true := by
  quickRfl

theorem c21107pair_0_r2 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 0 + 87)) (2 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 0 + 87)) (2 * 44) 44) = true := by
  quickRfl

theorem c21107pair_0_r3 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 0 + 87)) (3 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 0 + 87)) (3 * 44) 44) = true := by
  quickRfl

theorem c21107pair_0_r4 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 0 + 87)) (4 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 0 + 87)) (4 * 44) 44) = true := by
  quickRfl

theorem c21107pair_0_r5 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 0 + 87)) (5 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 0 + 87)) (5 * 44) 44) = true := by
  quickRfl

theorem c21107pair_0_r6 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 0 + 87)) (6 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 0 + 87)) (6 * 44) 44) = true := by
  quickRfl

theorem c21107pair_0_r7 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 0 + 87)) (7 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 0 + 87)) (7 * 44) 44) = true := by
  quickRfl

theorem c21107pair_0_r8 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 0 + 87)) (8 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 0 + 87)) (8 * 44) 44) = true := by
  quickRfl

theorem c21107pair_0_r9 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 0 + 87)) (9 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 0 + 87)) (9 * 44) 44) = true := by
  quickRfl

theorem c21107pair_0_r10 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 0 + 87)) (10 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 0 + 87)) (10 * 44) 44) = true := by
  quickRfl

theorem c21107pair_0_r11 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 0 + 87)) (11 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 0 + 87)) (11 * 44) 44) = true := by
  quickRfl

theorem c21107pair_0_r12 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 0 + 87)) (12 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 0 + 87)) (12 * 44) 44) = true := by
  quickRfl

theorem c21107pair_0_r13 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 0) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 0 + 87)) (13 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 0 + 87)) (13 * 44) 44) = true := by
  quickRfl

theorem c21107pair_0 : chunkI (wBits wd.W ||| 1) pts.L (bs.L.map spanM) (87 * 0) 87 = true :=
  chunkI_of_parts _ _ _ (87 * 0) 87 (by decide) (Nat.eq_of_beq_eq_true (by quickRfl)) c21107pair_0_t
    (rectI_of_slices _ _ _ _ _ 44 14 (Nat.le_of_ble_eq_true (by quickRfl))
      (Nat.eq_of_beq_eq_true (by quickRfl)) fun k hk => match k, hk with
      | 0, _ => c21107pair_0_r0
      | 1, _ => c21107pair_0_r1
      | 2, _ => c21107pair_0_r2
      | 3, _ => c21107pair_0_r3
      | 4, _ => c21107pair_0_r4
      | 5, _ => c21107pair_0_r5
      | 6, _ => c21107pair_0_r6
      | 7, _ => c21107pair_0_r7
      | 8, _ => c21107pair_0_r8
      | 9, _ => c21107pair_0_r9
      | 10, _ => c21107pair_0_r10
      | 11, _ => c21107pair_0_r11
      | 12, _ => c21107pair_0_r12
      | 13, _ => c21107pair_0_r13
      | _ + 14, h => absurd h (by omega))

theorem c21107pair_1_t : rowsI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 1) 87) (CFSG.KC.SliceGlue.slice pts.L (87 * 1 + 1) (87 - 1))
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 1 + 1) (87 - 1)) = true := by
  quickRfl

theorem c21107pair_1_r0 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 1 + 87)) (0 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 1 + 87)) (0 * 44) 44) = true := by
  quickRfl

theorem c21107pair_1_r1 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 1 + 87)) (1 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 1 + 87)) (1 * 44) 44) = true := by
  quickRfl

theorem c21107pair_1_r2 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 1 + 87)) (2 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 1 + 87)) (2 * 44) 44) = true := by
  quickRfl

theorem c21107pair_1_r3 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 1 + 87)) (3 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 1 + 87)) (3 * 44) 44) = true := by
  quickRfl

theorem c21107pair_1_r4 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 1 + 87)) (4 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 1 + 87)) (4 * 44) 44) = true := by
  quickRfl

theorem c21107pair_1_r5 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 1 + 87)) (5 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 1 + 87)) (5 * 44) 44) = true := by
  quickRfl

theorem c21107pair_1_r6 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 1 + 87)) (6 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 1 + 87)) (6 * 44) 44) = true := by
  quickRfl

theorem c21107pair_1_r7 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 1 + 87)) (7 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 1 + 87)) (7 * 44) 44) = true := by
  quickRfl

theorem c21107pair_1_r8 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 1 + 87)) (8 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 1 + 87)) (8 * 44) 44) = true := by
  quickRfl

theorem c21107pair_1_r9 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 1 + 87)) (9 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 1 + 87)) (9 * 44) 44) = true := by
  quickRfl

theorem c21107pair_1_r10 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 1 + 87)) (10 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 1 + 87)) (10 * 44) 44) = true := by
  quickRfl

theorem c21107pair_1_r11 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 1) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 1 + 87)) (11 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 1 + 87)) (11 * 44) 44) = true := by
  quickRfl

theorem c21107pair_1 : chunkI (wBits wd.W ||| 1) pts.L (bs.L.map spanM) (87 * 1) 87 = true :=
  chunkI_of_parts _ _ _ (87 * 1) 87 (by decide) (Nat.eq_of_beq_eq_true (by quickRfl)) c21107pair_1_t
    (rectI_of_slices _ _ _ _ _ 44 12 (Nat.le_of_ble_eq_true (by quickRfl))
      (Nat.eq_of_beq_eq_true (by quickRfl)) fun k hk => match k, hk with
      | 0, _ => c21107pair_1_r0
      | 1, _ => c21107pair_1_r1
      | 2, _ => c21107pair_1_r2
      | 3, _ => c21107pair_1_r3
      | 4, _ => c21107pair_1_r4
      | 5, _ => c21107pair_1_r5
      | 6, _ => c21107pair_1_r6
      | 7, _ => c21107pair_1_r7
      | 8, _ => c21107pair_1_r8
      | 9, _ => c21107pair_1_r9
      | 10, _ => c21107pair_1_r10
      | 11, _ => c21107pair_1_r11
      | _ + 12, h => absurd h (by omega))

theorem c21107pair_2_t : rowsI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 2) 87) (CFSG.KC.SliceGlue.slice pts.L (87 * 2 + 1) (87 - 1))
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 2 + 1) (87 - 1)) = true := by
  quickRfl

theorem c21107pair_2_r0 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 2 + 87)) (0 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 2 + 87)) (0 * 44) 44) = true := by
  quickRfl

theorem c21107pair_2_r1 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 2 + 87)) (1 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 2 + 87)) (1 * 44) 44) = true := by
  quickRfl

theorem c21107pair_2_r2 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 2 + 87)) (2 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 2 + 87)) (2 * 44) 44) = true := by
  quickRfl

theorem c21107pair_2_r3 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 2 + 87)) (3 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 2 + 87)) (3 * 44) 44) = true := by
  quickRfl

theorem c21107pair_2_r4 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 2 + 87)) (4 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 2 + 87)) (4 * 44) 44) = true := by
  quickRfl

theorem c21107pair_2_r5 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 2 + 87)) (5 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 2 + 87)) (5 * 44) 44) = true := by
  quickRfl

theorem c21107pair_2_r6 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 2 + 87)) (6 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 2 + 87)) (6 * 44) 44) = true := by
  quickRfl

theorem c21107pair_2_r7 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 2 + 87)) (7 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 2 + 87)) (7 * 44) 44) = true := by
  quickRfl

theorem c21107pair_2_r8 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 2 + 87)) (8 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 2 + 87)) (8 * 44) 44) = true := by
  quickRfl

theorem c21107pair_2_r9 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 2) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 2 + 87)) (9 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 2 + 87)) (9 * 44) 44) = true := by
  quickRfl

theorem c21107pair_2 : chunkI (wBits wd.W ||| 1) pts.L (bs.L.map spanM) (87 * 2) 87 = true :=
  chunkI_of_parts _ _ _ (87 * 2) 87 (by decide) (Nat.eq_of_beq_eq_true (by quickRfl)) c21107pair_2_t
    (rectI_of_slices _ _ _ _ _ 44 10 (Nat.le_of_ble_eq_true (by quickRfl))
      (Nat.eq_of_beq_eq_true (by quickRfl)) fun k hk => match k, hk with
      | 0, _ => c21107pair_2_r0
      | 1, _ => c21107pair_2_r1
      | 2, _ => c21107pair_2_r2
      | 3, _ => c21107pair_2_r3
      | 4, _ => c21107pair_2_r4
      | 5, _ => c21107pair_2_r5
      | 6, _ => c21107pair_2_r6
      | 7, _ => c21107pair_2_r7
      | 8, _ => c21107pair_2_r8
      | 9, _ => c21107pair_2_r9
      | _ + 10, h => absurd h (by omega))

theorem c21107pair_3_t : rowsI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 3) 87) (CFSG.KC.SliceGlue.slice pts.L (87 * 3 + 1) (87 - 1))
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 3 + 1) (87 - 1)) = true := by
  quickRfl

theorem c21107pair_3_r0 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 3 + 87)) (0 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 3 + 87)) (0 * 44) 44) = true := by
  quickRfl

theorem c21107pair_3_r1 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 3 + 87)) (1 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 3 + 87)) (1 * 44) 44) = true := by
  quickRfl

theorem c21107pair_3_r2 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 3 + 87)) (2 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 3 + 87)) (2 * 44) 44) = true := by
  quickRfl

theorem c21107pair_3_r3 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 3 + 87)) (3 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 3 + 87)) (3 * 44) 44) = true := by
  quickRfl

theorem c21107pair_3_r4 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 3 + 87)) (4 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 3 + 87)) (4 * 44) 44) = true := by
  quickRfl

theorem c21107pair_3_r5 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 3 + 87)) (5 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 3 + 87)) (5 * 44) 44) = true := by
  quickRfl

theorem c21107pair_3_r6 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 3 + 87)) (6 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 3 + 87)) (6 * 44) 44) = true := by
  quickRfl

theorem c21107pair_3_r7 : rectI (wBits wd.W ||| 1) (CFSG.KC.SliceGlue.slice pts.L (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (bs.L.map spanM) (87 * 3) 87)
    (CFSG.KC.SliceGlue.slice (pts.L.drop (87 * 3 + 87)) (7 * 44) 44)
    (CFSG.KC.SliceGlue.slice ((bs.L.map spanM).drop (87 * 3 + 87)) (7 * 44) 44) = true := by
  quickRfl

theorem c21107pair_3 : chunkI (wBits wd.W ||| 1) pts.L (bs.L.map spanM) (87 * 3) 87 = true :=
  chunkI_of_parts _ _ _ (87 * 3) 87 (by decide) (Nat.eq_of_beq_eq_true (by quickRfl)) c21107pair_3_t
    (rectI_of_slices _ _ _ _ _ 44 8 (Nat.le_of_ble_eq_true (by quickRfl))
      (Nat.eq_of_beq_eq_true (by quickRfl)) fun k hk => match k, hk with
      | 0, _ => c21107pair_3_r0
      | 1, _ => c21107pair_3_r1
      | 2, _ => c21107pair_3_r2
      | 3, _ => c21107pair_3_r3
      | 4, _ => c21107pair_3_r4
      | 5, _ => c21107pair_3_r5
      | 6, _ => c21107pair_3_r6
      | 7, _ => c21107pair_3_r7
      | _ + 8, h => absurd h (by omega))

theorem c21107neg_pair : pairI (wBits wd.W ||| 1) (pts.L.getD 0 0) (spanM (bs.L.getD 0 []))
    (pts.L.getD 1 0) (spanM (bs.L.getD 0 [])) = false := by
  decide +kernel

end CertificateChecks.KernelSmithEK
