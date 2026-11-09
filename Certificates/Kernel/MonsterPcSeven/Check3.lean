module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.MonsterPcSeven
public import Certificates.Kernel.MonsterPcSeven.Data

public section

namespace CFSG.KC.MonPcSevenD

open CFSG.KC.MonPcSeven

theorem m7census3_0 : chunkOK rep 432 (2401 * (21 + 0)) (chunks.getD (21 + 0) []) = true := by
  quickRfl

theorem m7census3_1 : chunkOK rep 432 (2401 * (21 + 1)) (chunks.getD (21 + 1) []) = true := by
  quickRfl

theorem m7census3_2 : chunkOK rep 432 (2401 * (21 + 2)) (chunks.getD (21 + 2) []) = true := by
  quickRfl

theorem m7census3_3 : chunkOK rep 432 (2401 * (21 + 3)) (chunks.getD (21 + 3) []) = true := by
  quickRfl

theorem m7census3_4 : chunkOK rep 432 (2401 * (21 + 4)) (chunks.getD (21 + 4) []) = true := by
  quickRfl

theorem m7census3_5 : chunkOK rep 432 (2401 * (21 + 5)) (chunks.getD (21 + 5) []) = true := by
  quickRfl

theorem m7census3_6 : chunkOK rep 432 (2401 * (21 + 6)) (chunks.getD (21 + 6) []) = true := by
  quickRfl

theorem m7census3 :
    ∀ k < 7, chunkOK rep 432 (2401 * (21 + k)) (chunks.getD (21 + k) []) = true :=
  fun k hk => match k, hk with
  | 0, _ => m7census3_0
  | 1, _ => m7census3_1
  | 2, _ => m7census3_2
  | 3, _ => m7census3_3
  | 4, _ => m7census3_4
  | 5, _ => m7census3_5
  | 6, _ => m7census3_6
  | _ + 7, h => absurd h (by omega)

end CFSG.KC.MonPcSevenD

end
