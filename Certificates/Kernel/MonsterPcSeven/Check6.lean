module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcSeven
public import Certificates.Kernel.MonsterPcSeven.Data

public section

namespace CFSG.KC.MonPcSevenD

open CFSG.KC.MonPcSeven

theorem m7census6_0 : chunkOK rep 432 (2401 * (42 + 0)) (chunks.getD (42 + 0) []) = true := by
  quickRfl

theorem m7census6_1 : chunkOK rep 432 (2401 * (42 + 1)) (chunks.getD (42 + 1) []) = true := by
  quickRfl

theorem m7census6_2 : chunkOK rep 432 (2401 * (42 + 2)) (chunks.getD (42 + 2) []) = true := by
  quickRfl

theorem m7census6_3 : chunkOK rep 432 (2401 * (42 + 3)) (chunks.getD (42 + 3) []) = true := by
  quickRfl

theorem m7census6_4 : chunkOK rep 432 (2401 * (42 + 4)) (chunks.getD (42 + 4) []) = true := by
  quickRfl

theorem m7census6_5 : chunkOK rep 432 (2401 * (42 + 5)) (chunks.getD (42 + 5) []) = true := by
  quickRfl

theorem m7census6_6 : chunkOK rep 432 (2401 * (42 + 6)) (chunks.getD (42 + 6) []) = true := by
  quickRfl

theorem m7census6 :
    ∀ k < 7, chunkOK rep 432 (2401 * (42 + k)) (chunks.getD (42 + k) []) = true :=
  fun k hk => match k, hk with
  | 0, _ => m7census6_0
  | 1, _ => m7census6_1
  | 2, _ => m7census6_2
  | 3, _ => m7census6_3
  | 4, _ => m7census6_4
  | 5, _ => m7census6_5
  | 6, _ => m7census6_6
  | _ + 7, h => absurd h (by omega)

end CFSG.KC.MonPcSevenD

end
