module

public import Certificates.Data.Kernel.Misc.OmegaSixMx
public import Certificates.Kernel.Misc.OmegaSix.Rec
public import Certificates.Kernel.Misc.OmegaSix.MaxRec
public import Certificates.Kernel.Misc.OmegaSix.MaxRec1
public import Certificates.Kernel.Misc.OmegaSix.MaxRec2
import CFSG.Certificates.Kernel.Common.Harness
public meta import Certificates.Kernel.Co1B.GenTri2045
public import Certificates.Kernel.Co1B.GenTri2045

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.BfsK CFSG.KD.YamakiRep CFSG.KD.YamakiRepF
open CFSG.KD.Sp62 (MULF)

theorem mcHead : headK RMC 2 720 2 = true := by quickRfl

@[expose] noncomputable def ch919005C (q : Nat) : Bool := chunkF RMC (rstG RMC 0) 2 720 256 q

theorem m1Head : headK RM1 3 25920 3 = true := by quickRfl

theorem m2Head : headK RM2 3 25920 3 = true := by quickRfl

theorem m1Gen0 : RM1 0 = RMC 0 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem m1Gen1 : RM1 1 = RMC 1 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem m1Gen2 : RM1 2 = RMH 0 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem m2Gen0 : RM2 0 = RMC 0 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem m2Gen1 : RM2 1 = RMC 1 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem m2Gen2 : RM2 2 = RMH 1 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem mS1 : RMH 2 = MULF (MULF (RMH 0) (RO 2)) (RMH 0) := Nat.eq_of_beq_eq_true (by quickRfl)

theorem mS2 : RMH 3 = MULF (MULF (RMH 1) (RO 2)) (RMH 1) := Nat.eq_of_beq_eq_true (by quickRfl)

theorem mPos0 : posAt RO 10 25920 (RMH 4) (RMC 0) = true := by quickRfl

theorem mPos1 : posAt RO 10 25920 (RMH 5) (RMC 1) = true := by quickRfl

theorem mPos2 : posAt RO 10 25920 (RMH 6) (RMH 0) = true := by quickRfl

theorem mPos3 : posAt RO 10 25920 (RMH 7) (RMH 1) = true := by quickRfl

theorem mcLt : ∀ j < 2, RMC j < 2 ^ 36 := by decide +kernel

theorem mhLt : ∀ j < 4, RMH j < 2 ^ 36 := by decide +kernel

end CFSG.KD.OmegaSix

#kc_slices CFSG.KD.OmegaSix.ch919005CK CFSG.KD.OmegaSix.ch919005C 3

end
