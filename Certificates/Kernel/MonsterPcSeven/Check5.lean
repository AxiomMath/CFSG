module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcSeven
public import Certificates.Kernel.MonsterPcSeven.Data

public section

namespace CFSG.KC.MonPcSevenD

open CFSG.KC.MonPcSeven

theorem m7census5_0 : chunkOK rep 432 (2401 * (35 + 0)) (chunks.getD (35 + 0) []) = true := by
  quickRfl

theorem m7census5_1 : chunkOK rep 432 (2401 * (35 + 1)) (chunks.getD (35 + 1) []) = true := by
  quickRfl

theorem m7census5_2 : chunkOK rep 432 (2401 * (35 + 2)) (chunks.getD (35 + 2) []) = true := by
  quickRfl

theorem m7census5_3 : chunkOK rep 432 (2401 * (35 + 3)) (chunks.getD (35 + 3) []) = true := by
  quickRfl

theorem m7census5_4 : chunkOK rep 432 (2401 * (35 + 4)) (chunks.getD (35 + 4) []) = true := by
  quickRfl

theorem m7census5_5 : chunkOK rep 432 (2401 * (35 + 5)) (chunks.getD (35 + 5) []) = true := by
  quickRfl

theorem m7census5_6 : chunkOK rep 432 (2401 * (35 + 6)) (chunks.getD (35 + 6) []) = true := by
  quickRfl

theorem m7census5 :
    ∀ k < 7, chunkOK rep 432 (2401 * (35 + k)) (chunks.getD (35 + k) []) = true :=
  fun k hk => match k, hk with
  | 0, _ => m7census5_0
  | 1, _ => m7census5_1
  | 2, _ => m7census5_2
  | 3, _ => m7census5_3
  | 4, _ => m7census5_4
  | 5, _ => m7census5_5
  | 6, _ => m7census5_6
  | _ + 7, h => absurd h (by omega)

end CFSG.KC.MonPcSevenD

end
