module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcSeven
public import Certificates.Kernel.MonsterPcSeven.Data

public section

namespace CFSG.KC.MonPcSevenD

open CFSG.KC.MonPcSeven

theorem m7census1_0 : chunkOK rep 432 (2401 * (7 + 0)) (chunks.getD (7 + 0) []) = true := by
  quickRfl

theorem m7census1_1 : chunkOK rep 432 (2401 * (7 + 1)) (chunks.getD (7 + 1) []) = true := by
  quickRfl

theorem m7census1_2 : chunkOK rep 432 (2401 * (7 + 2)) (chunks.getD (7 + 2) []) = true := by
  quickRfl

theorem m7census1_3 : chunkOK rep 432 (2401 * (7 + 3)) (chunks.getD (7 + 3) []) = true := by
  quickRfl

theorem m7census1_4 : chunkOK rep 432 (2401 * (7 + 4)) (chunks.getD (7 + 4) []) = true := by
  quickRfl

theorem m7census1_5 : chunkOK rep 432 (2401 * (7 + 5)) (chunks.getD (7 + 5) []) = true := by
  quickRfl

theorem m7census1_6 : chunkOK rep 432 (2401 * (7 + 6)) (chunks.getD (7 + 6) []) = true := by
  quickRfl

theorem m7census1 :
    ∀ k < 7, chunkOK rep 432 (2401 * (7 + k)) (chunks.getD (7 + k) []) = true :=
  fun k hk => match k, hk with
  | 0, _ => m7census1_0
  | 1, _ => m7census1_1
  | 2, _ => m7census1_2
  | 3, _ => m7census1_3
  | 4, _ => m7census1_4
  | 5, _ => m7census1_5
  | 6, _ => m7census1_6
  | _ + 7, h => absurd h (by omega)

end CFSG.KC.MonPcSevenD

end
