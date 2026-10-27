module

public import Certificates.Data.Kernel.ExcIns.A8
public import Certificates.Kernel.ExcExt.Data
public import Certificates.Kernel.ExcIns.Data5
public import Certificates.Kernel.ExcIns.DataA8
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.ExcInsK

open CFSG.ExcExtK

set_option maxRecDepth 100000

theorem ch712573a8r : Nat.beq (ln128 D5.R 12) (ln128 A5.AP 0) = true := by quickRfl
theorem ch712573a8_0 : chunkK D.T5 D.fx5 8 8 A5.AP 960 60 A5.C0 0 = true := by quickRfl
theorem ch712573a8_1 : chunkK D.T5 D.fx5 8 8 A5.AP 960 120 A5.C1 60 = true := by quickRfl
theorem ch712573a8_2 : chunkK D.T5 D.fx5 8 8 A5.AP 960 180 A5.C2 120 = true := by quickRfl
theorem ch712573a8_3 : chunkK D.T5 D.fx5 8 8 A5.AP 960 240 A5.C3 180 = true := by quickRfl
theorem ch712573a8_4 : chunkK D.T5 D.fx5 8 8 A5.AP 960 300 A5.C4 240 = true := by quickRfl
theorem ch712573a8_5 : chunkK D.T5 D.fx5 8 8 A5.AP 960 360 A5.C5 300 = true := by quickRfl
theorem ch712573a8_6 : chunkK D.T5 D.fx5 8 8 A5.AP 960 420 A5.C6 360 = true := by quickRfl
theorem ch712573a8_7 : chunkK D.T5 D.fx5 8 8 A5.AP 960 480 A5.C7 420 = true := by quickRfl
theorem ch712573a8_8 : chunkK D.T5 D.fx5 8 8 A5.AP 960 540 A5.C8 480 = true := by quickRfl
theorem ch712573a8_9 : chunkK D.T5 D.fx5 8 8 A5.AP 960 600 A5.C9 540 = true := by quickRfl
theorem ch712573a8_10 : chunkK D.T5 D.fx5 8 8 A5.AP 960 660 A5.C10 600 = true := by quickRfl
theorem ch712573a8_11 : chunkK D.T5 D.fx5 8 8 A5.AP 960 720 A5.C11 660 = true := by quickRfl
theorem ch712573a8_12 : chunkK D.T5 D.fx5 8 8 A5.AP 960 780 A5.C12 720 = true := by quickRfl
theorem ch712573a8_13 : chunkK D.T5 D.fx5 8 8 A5.AP 960 840 A5.C13 780 = true := by quickRfl
theorem ch712573a8_14 : chunkK D.T5 D.fx5 8 8 A5.AP 960 900 A5.C14 840 = true := by quickRfl
theorem ch712573a8_15 : chunkK D.T5 D.fx5 8 8 A5.AP 960 960 A5.C15 900 = true := by quickRfl

end CFSG.ExcInsK

end
