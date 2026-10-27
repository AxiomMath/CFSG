module

public import Certificates.Data.Kernel.Misc.SylowG2K
public import Certificates.Data.Kernel.Misc.OmegaSixO
public import Certificates.Kernel.Misc.SylowG2.Rec
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.SylowG2

open CFSG.KD.YamakiRep CFSG.KD.YamakiAut CFSG.KD.OmegaSix CFSG.KD.BfsK
open CFSG.KD.Sp62 (MULF ONE)

@[expose] def tl0 : List Nat := [1, 0, 2, 3, 4, 5, 6, 7, 9, 8]

@[expose] def tl1 : List Nat := [2, 3, 0, 1, 4, 5, 6, 7, 8, 9]

@[expose] def tl2 : List Nat := [4, 5, 6, 7, 0, 1, 2, 3, 8, 9]

@[expose] def ul0 : List Nat := [1, 0, 2, 3, 5, 4, 6, 7]

@[expose] def ul1 : List Nat := [2, 3, 0, 1, 4, 5, 6, 7]

@[expose] def ul2 : List Nat := [4, 5, 6, 7, 0, 1, 2, 3]

@[expose] def tOne : Nat := 654820258320

@[expose] def uOne : Nat := 1985229328

theorem sg919101_headP : headK RPP 3 128 3 = true := by quickRfl

theorem sg919101_headQ : headK RQQ 3 64 3 = true := by quickRfl

theorem sg919101_tabP : chunkF3 RPP (rstG RPP 0) 3 128 128 0 = true := by quickRfl

theorem sg919101_tabQ : chunkF3 RQQ (rstG RQQ 0) 3 64 64 0 = true := by quickRfl

theorem sg919101_autP : autChunk3 RPP RT 3 tl0 tl1 tl2 tOne 128 128 0 = true := by quickRfl

theorem sg919101_autQ : autChunk3 RQQ RU 3 ul0 ul1 ul2 uOne 64 64 0 = true := by quickRfl

theorem sg919101_invP : invPos3 RPP 3 128 [(1, 0), (2, 1), (3, 2)] = true := by quickRfl

theorem sg919101_invQ : invPos3 RQQ 3 64 [(1, 0), (2, 1), (3, 2)] = true := by quickRfl

theorem sg919101_comm0 : RQQ 0 = MULF (MULF (MULF (HQ 0) (HQ 1)) (HQ 0)) (HQ 2) :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem sg919101_comm1 : RQQ 1 = MULF (MULF (MULF (HQ 3) (HQ 4)) (HQ 3)) (HQ 5) :=
  Nat.eq_of_beq_eq_true (by quickRfl)

theorem sg919101_comm2 : RQQ 2 = MULF (MULF (MULF (HQ 6) (HQ 7)) (HQ 6)) (HQ 8) :=
  Nat.eq_of_beq_eq_true (by quickRfl)

end CFSG.KD.SylowG2

end
