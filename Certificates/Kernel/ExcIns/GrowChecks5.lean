module

public import Certificates.Data.Kernel.ExcIns.Grow
public import Certificates.Kernel.ExcExt.Data
public import Certificates.Kernel.ExcIns.Data5
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.ExcInsK

open CFSG.ExcExtK

set_option maxRecDepth 100000

theorem ch712573gm : Nat.beq D5.gm 255 = true := by quickRfl
theorem ch712573nr : Nat.beq D5.nr 14 = true := by quickRfl
theorem ch712573pl : planesOK D.T5 6561 D5.PL = true := by quickRfl
theorem ch712573rp : repsOK D5.R 14 120 = true := by quickRfl
theorem ch712573s : recsK D.T5 D5.PL 6561 D5.gm D5.R D5.nr false 0 D5.S = true := by quickRfl
theorem ch712573g_0 : recsK D.T5 D5.PL 6561 D5.gm D5.R D5.nr true (ln128 D5.R 0) D5.G0 = true := by
  quickRfl
theorem ch712573g_1 : recsK D.T5 D5.PL 6561 D5.gm D5.R D5.nr true (ln128 D5.R 1) D5.G1 = true := by
  quickRfl
theorem ch712573g_2 : recsK D.T5 D5.PL 6561 D5.gm D5.R D5.nr true (ln128 D5.R 2) D5.G2 = true := by
  quickRfl
theorem ch712573g_3 : recsK D.T5 D5.PL 6561 D5.gm D5.R D5.nr true (ln128 D5.R 3) D5.G3 = true := by
  quickRfl
theorem ch712573g_4 : recsK D.T5 D5.PL 6561 D5.gm D5.R D5.nr true (ln128 D5.R 4) D5.G4 = true := by
  quickRfl
theorem ch712573g_5 : recsK D.T5 D5.PL 6561 D5.gm D5.R D5.nr true (ln128 D5.R 5) D5.G5 = true := by
  quickRfl
theorem ch712573g_6 : recsK D.T5 D5.PL 6561 D5.gm D5.R D5.nr true (ln128 D5.R 6) D5.G6 = true := by
  quickRfl
theorem ch712573g_7 : recsK D.T5 D5.PL 6561 D5.gm D5.R D5.nr true (ln128 D5.R 7) D5.G7 = true := by
  quickRfl
theorem ch712573g_8 : recsK D.T5 D5.PL 6561 D5.gm D5.R D5.nr true (ln128 D5.R 8) D5.G8 = true := by
  quickRfl
theorem ch712573g_9 : recsK D.T5 D5.PL 6561 D5.gm D5.R D5.nr true (ln128 D5.R 9) D5.G9 = true := by
  quickRfl
theorem ch712573g_10 : recsK D.T5 D5.PL 6561 D5.gm D5.R D5.nr true (ln128 D5.R 10) D5.G10 = true := by
  quickRfl
theorem ch712573g_11 : recsK D.T5 D5.PL 6561 D5.gm D5.R D5.nr true (ln128 D5.R 11) D5.G11 = true := by
  quickRfl
theorem ch712573g_12 : recsK D.T5 D5.PL 6561 D5.gm D5.R D5.nr true (ln128 D5.R 12) D5.G12 = true := by
  quickRfl
theorem ch712573g_13 : recsK D.T5 D5.PL 6561 D5.gm D5.R D5.nr true (ln128 D5.R 13) D5.G13 = true := by
  quickRfl

end CFSG.ExcInsK

end
