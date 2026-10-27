module

public import Certificates.Kernel.G24B.Recs
import CFSG.Certificates.Kernel.Common.Cover
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.G24B

open CFSG.KC.F2BfsRec CFSG.KLie.CT

@[expose] noncomputable def pinsK (lb ng : Nat) (CF : Nat → Nat) (ws : List (List (Fin 6 × Bool))) :
    Bool :=
  andB (Nat.beq (List.length ws) ng)
    (allN ng fun j => Nat.beq (genR 28 12 lb ng CF j) (blowW (ws.getD j [])))

theorem ch733008_q1Head : headK 28 12 6 10 EQ1.CF = true := by quickRfl
theorem ch733008_q1Pins : pinsK 6 10 EQ1.CF wQ1 = true := by quickRfl
theorem ch733008_q1Recs : ∀ t < 1024, recK2 28 12 6 10 EQ1.CF (genR 28 12 6 10 EQ1.CF) 1024 t = true := by
  kc_cover 64

theorem ch733008_q2Head : headK 28 12 6 10 EQ2.CF = true := by quickRfl
theorem ch733008_q2Pins : pinsK 6 10 EQ2.CF wQ2 = true := by quickRfl
theorem ch733008_q2Recs : ∀ t < 1024, recK2 28 12 6 10 EQ2.CF (genR 28 12 6 10 EQ2.CF) 1024 t = true := by
  kc_cover 64

theorem ch733008_a1Head : headK 28 12 6 3 EA1.CF = true := by quickRfl
theorem ch733008_a1Pins : pinsK 6 3 EA1.CF wA1 = true := by quickRfl
theorem ch733008_a1Recs : ∀ t < 180, recK2 28 12 6 3 EA1.CF (genR 28 12 6 3 EA1.CF) 180 t = true := by
  kc_cover 64

theorem ch733008_a2Head : headK 28 12 6 3 EA2.CF = true := by quickRfl
theorem ch733008_a2Pins : pinsK 6 3 EA2.CF wA2 = true := by quickRfl
theorem ch733008_a2Recs : ∀ t < 180, recK2 28 12 6 3 EA2.CF (genR 28 12 6 3 EA2.CF) 180 t = true := by
  kc_cover 64

theorem ch733008_hHead : headK 28 12 6 2 EH.CF = true := by quickRfl
theorem ch733008_hPins : pinsK 6 2 EH.CF wH = true := by quickRfl
theorem ch733008_hRecs : ∀ t < 9, recK2 28 12 6 2 EH.CF (genR 28 12 6 2 EH.CF) 9 t = true := by
  kc_cover 64

theorem ch733008_negCount : (!recK2 28 12 6 3 EA1.CF (genR 28 12 6 3 EA1.CF) 179 178) = true := by
  quickRfl

theorem ch733008_negPin : (!pinsK 6 3 EA1.CF wA2) = true := by quickRfl

end CFSG.KD.G24B

end
