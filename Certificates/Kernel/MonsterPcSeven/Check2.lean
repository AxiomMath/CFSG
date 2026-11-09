module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcSeven
public import Certificates.Kernel.MonsterPcSeven.Data

public section

namespace CFSG.KC.MonPcSevenD

open CFSG.KC.MonPcSeven

theorem m7census2_0 : chunkOK rep 432 (2401 * (14 + 0)) (chunks.getD (14 + 0) []) = true := by
  quickRfl

theorem m7census2_1 : chunkOK rep 432 (2401 * (14 + 1)) (chunks.getD (14 + 1) []) = true := by
  quickRfl

theorem m7census2_2 : chunkOK rep 432 (2401 * (14 + 2)) (chunks.getD (14 + 2) []) = true := by
  quickRfl

theorem m7census2_3 : chunkOK rep 432 (2401 * (14 + 3)) (chunks.getD (14 + 3) []) = true := by
  quickRfl

theorem m7census2_4 : chunkOK rep 432 (2401 * (14 + 4)) (chunks.getD (14 + 4) []) = true := by
  quickRfl

theorem m7census2_5 : chunkOK rep 432 (2401 * (14 + 5)) (chunks.getD (14 + 5) []) = true := by
  quickRfl

theorem m7census2_6 : chunkOK rep 432 (2401 * (14 + 6)) (chunks.getD (14 + 6) []) = true := by
  quickRfl

theorem m7census2 :
    ∀ k < 7, chunkOK rep 432 (2401 * (14 + k)) (chunks.getD (14 + k) []) = true :=
  fun k hk => match k, hk with
  | 0, _ => m7census2_0
  | 1, _ => m7census2_1
  | 2, _ => m7census2_2
  | 3, _ => m7census2_3
  | 4, _ => m7census2_4
  | 5, _ => m7census2_5
  | 6, _ => m7census2_6
  | _ + 7, h => absurd h (by omega)

end CFSG.KC.MonPcSevenD

end
