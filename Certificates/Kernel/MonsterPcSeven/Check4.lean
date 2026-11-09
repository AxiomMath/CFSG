module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcSeven
public import Certificates.Kernel.MonsterPcSeven.Data

public section

namespace CFSG.KC.MonPcSevenD

open CFSG.KC.MonPcSeven

theorem m7census4_0 : chunkOK rep 432 (2401 * (28 + 0)) (chunks.getD (28 + 0) []) = true := by
  quickRfl

theorem m7census4_1 : chunkOK rep 432 (2401 * (28 + 1)) (chunks.getD (28 + 1) []) = true := by
  quickRfl

theorem m7census4_2 : chunkOK rep 432 (2401 * (28 + 2)) (chunks.getD (28 + 2) []) = true := by
  quickRfl

theorem m7census4_3 : chunkOK rep 432 (2401 * (28 + 3)) (chunks.getD (28 + 3) []) = true := by
  quickRfl

theorem m7census4_4 : chunkOK rep 432 (2401 * (28 + 4)) (chunks.getD (28 + 4) []) = true := by
  quickRfl

theorem m7census4_5 : chunkOK rep 432 (2401 * (28 + 5)) (chunks.getD (28 + 5) []) = true := by
  quickRfl

theorem m7census4_6 : chunkOK rep 432 (2401 * (28 + 6)) (chunks.getD (28 + 6) []) = true := by
  quickRfl

theorem m7census4 :
    ∀ k < 7, chunkOK rep 432 (2401 * (28 + k)) (chunks.getD (28 + k) []) = true :=
  fun k hk => match k, hk with
  | 0, _ => m7census4_0
  | 1, _ => m7census4_1
  | 2, _ => m7census4_2
  | 3, _ => m7census4_3
  | 4, _ => m7census4_4
  | 5, _ => m7census4_5
  | 6, _ => m7census4_6
  | _ + 7, h => absurd h (by omega)

end CFSG.KC.MonPcSevenD

end
