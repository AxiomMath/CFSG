module

public import Certificates.Kernel.HS3850.S9Orbit
public import Certificates.Data.Kernel.HS3850.S9Sets
import all Init.Data.List.SplitOn.Basic

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CFSG.KD.HS3850.S9

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.HSAutN CertificateChecks.KernelSporSch

@[expose] noncomputable def s9Blk (k : Nat) : Nat :=
  Nat.land (Nat.shiftRight (setsN.getD (k / 125) 0) (504 * (k % 125))) (2 ^ 504 - 1)

@[expose] def s9Fd (b i : Nat) : Nat := Nat.land (Nat.shiftRight b (12 * i)) 4095

@[expose] def s9Dec (b : Nat) : List Nat :=
  [s9Fd b 0, s9Fd b 1, s9Fd b 2, s9Fd b 3, s9Fd b 4, s9Fd b 5,
   s9Fd b 6, s9Fd b 7, s9Fd b 8, s9Fd b 9, s9Fd b 10, s9Fd b 11,
   s9Fd b 12, s9Fd b 13, s9Fd b 14, s9Fd b 15, s9Fd b 16, s9Fd b 17,
   s9Fd b 18, s9Fd b 19, s9Fd b 20, s9Fd b 21, s9Fd b 22, s9Fd b 23,
   s9Fd b 24, s9Fd b 25, s9Fd b 26, s9Fd b 27, s9Fd b 28, s9Fd b 29,
   s9Fd b 30, s9Fd b 31, s9Fd b 32, s9Fd b 33, s9Fd b 34, s9Fd b 35,
   s9Fd b 36, s9Fd b 37, s9Fd b 38, s9Fd b 39, s9Fd b 40, s9Fd b 41]

@[expose] noncomputable def s9Set (k : Nat) : List Nat := s9Dec (s9Blk k)

@[expose] noncomputable def s9Eq (X b c : Nat) : Bool :=
  s9Fd b 0 == imgK X (s9Fd c 0) && s9Fd b 1 == imgK X (s9Fd c 1) &&
  s9Fd b 2 == imgK X (s9Fd c 2) && s9Fd b 3 == imgK X (s9Fd c 3) &&
  s9Fd b 4 == imgK X (s9Fd c 4) && s9Fd b 5 == imgK X (s9Fd c 5) &&
  s9Fd b 6 == imgK X (s9Fd c 6) && s9Fd b 7 == imgK X (s9Fd c 7) &&
  s9Fd b 8 == imgK X (s9Fd c 8) && s9Fd b 9 == imgK X (s9Fd c 9) &&
  s9Fd b 10 == imgK X (s9Fd c 10) && s9Fd b 11 == imgK X (s9Fd c 11) &&
  s9Fd b 12 == imgK X (s9Fd c 12) && s9Fd b 13 == imgK X (s9Fd c 13) &&
  s9Fd b 14 == imgK X (s9Fd c 14) && s9Fd b 15 == imgK X (s9Fd c 15) &&
  s9Fd b 16 == imgK X (s9Fd c 16) && s9Fd b 17 == imgK X (s9Fd c 17) &&
  s9Fd b 18 == imgK X (s9Fd c 18) && s9Fd b 19 == imgK X (s9Fd c 19) &&
  s9Fd b 20 == imgK X (s9Fd c 20) && s9Fd b 21 == imgK X (s9Fd c 21) &&
  s9Fd b 22 == imgK X (s9Fd c 22) && s9Fd b 23 == imgK X (s9Fd c 23) &&
  s9Fd b 24 == imgK X (s9Fd c 24) && s9Fd b 25 == imgK X (s9Fd c 25) &&
  s9Fd b 26 == imgK X (s9Fd c 26) && s9Fd b 27 == imgK X (s9Fd c 27) &&
  s9Fd b 28 == imgK X (s9Fd c 28) && s9Fd b 29 == imgK X (s9Fd c 29) &&
  s9Fd b 30 == imgK X (s9Fd c 30) && s9Fd b 31 == imgK X (s9Fd c 31) &&
  s9Fd b 32 == imgK X (s9Fd c 32) && s9Fd b 33 == imgK X (s9Fd c 33) &&
  s9Fd b 34 == imgK X (s9Fd c 34) && s9Fd b 35 == imgK X (s9Fd c 35) &&
  s9Fd b 36 == imgK X (s9Fd c 36) && s9Fd b 37 == imgK X (s9Fd c 37) &&
  s9Fd b 38 == imgK X (s9Fd c 38) && s9Fd b 39 == imgK X (s9Fd c 39) &&
  s9Fd b 40 == imgK X (s9Fd c 40) && s9Fd b 41 == imgK X (s9Fd c 41)

@[expose] def s9Lt (b : Nat) : Bool :=
  decide (s9Fd b 0 < 3850) && decide (s9Fd b 1 < 3850) && decide (s9Fd b 2 < 3850) &&
  decide (s9Fd b 3 < 3850) && decide (s9Fd b 4 < 3850) && decide (s9Fd b 5 < 3850) &&
  decide (s9Fd b 6 < 3850) && decide (s9Fd b 7 < 3850) && decide (s9Fd b 8 < 3850) &&
  decide (s9Fd b 9 < 3850) && decide (s9Fd b 10 < 3850) && decide (s9Fd b 11 < 3850) &&
  decide (s9Fd b 12 < 3850) && decide (s9Fd b 13 < 3850) && decide (s9Fd b 14 < 3850) &&
  decide (s9Fd b 15 < 3850) && decide (s9Fd b 16 < 3850) && decide (s9Fd b 17 < 3850) &&
  decide (s9Fd b 18 < 3850) && decide (s9Fd b 19 < 3850) && decide (s9Fd b 20 < 3850) &&
  decide (s9Fd b 21 < 3850) && decide (s9Fd b 22 < 3850) && decide (s9Fd b 23 < 3850) &&
  decide (s9Fd b 24 < 3850) && decide (s9Fd b 25 < 3850) && decide (s9Fd b 26 < 3850) &&
  decide (s9Fd b 27 < 3850) && decide (s9Fd b 28 < 3850) && decide (s9Fd b 29 < 3850) &&
  decide (s9Fd b 30 < 3850) && decide (s9Fd b 31 < 3850) && decide (s9Fd b 32 < 3850) &&
  decide (s9Fd b 33 < 3850) && decide (s9Fd b 34 < 3850) && decide (s9Fd b 35 < 3850) &&
  decide (s9Fd b 36 < 3850) && decide (s9Fd b 37 < 3850) && decide (s9Fd b 38 < 3850) &&
  decide (s9Fd b 39 < 3850) && decide (s9Fd b 40 < 3850) && decide (s9Fd b 41 < 3850)

@[expose] def s9Mask (l : List Nat) : Nat := l.foldr (fun p acc => acc ||| 2 ^ p) 0

@[expose] def s9MaskN (b : Nat) : Nat :=
  ((((((((((((((((((((((((((((((((((((((((((0 ||| 2 ^ s9Fd b 41) ||| 2 ^ s9Fd b 40) |||
  2 ^ s9Fd b 39) ||| 2 ^ s9Fd b 38) ||| 2 ^ s9Fd b 37) |||
  2 ^ s9Fd b 36) ||| 2 ^ s9Fd b 35) ||| 2 ^ s9Fd b 34) |||
  2 ^ s9Fd b 33) ||| 2 ^ s9Fd b 32) ||| 2 ^ s9Fd b 31) |||
  2 ^ s9Fd b 30) ||| 2 ^ s9Fd b 29) ||| 2 ^ s9Fd b 28) |||
  2 ^ s9Fd b 27) ||| 2 ^ s9Fd b 26) ||| 2 ^ s9Fd b 25) |||
  2 ^ s9Fd b 24) ||| 2 ^ s9Fd b 23) ||| 2 ^ s9Fd b 22) |||
  2 ^ s9Fd b 21) ||| 2 ^ s9Fd b 20) ||| 2 ^ s9Fd b 19) |||
  2 ^ s9Fd b 18) ||| 2 ^ s9Fd b 17) ||| 2 ^ s9Fd b 16) |||
  2 ^ s9Fd b 15) ||| 2 ^ s9Fd b 14) ||| 2 ^ s9Fd b 13) |||
  2 ^ s9Fd b 12) ||| 2 ^ s9Fd b 11) ||| 2 ^ s9Fd b 10) |||
  2 ^ s9Fd b 9) ||| 2 ^ s9Fd b 8) ||| 2 ^ s9Fd b 7) |||
  2 ^ s9Fd b 6) ||| 2 ^ s9Fd b 5) ||| 2 ^ s9Fd b 4) |||
  2 ^ s9Fd b 3) ||| 2 ^ s9Fd b 2) ||| 2 ^ s9Fd b 1) |||
  2 ^ s9Fd b 0)

@[expose] noncomputable def s9Step (k : Nat) : Nat :=
  strictN (s9Blk k) fun b => strictN (gen k) fun g => strictN (s9Blk (par k)) fun c =>
    if s9Eq (HX g) b c then 1 else 0

@[expose] noncomputable def s9Ok (k : Nat) : Nat := strictN (s9Blk k) fun b => if s9Lt b then 1 else 0

@[expose] noncomputable def s9Key (k : Nat) : Nat := strictN (s9Blk k) fun b => s9MaskN b

theorem kSigma : (s9Set 0 == sigmaC) = true := by
  decide +kernel

theorem kSets0 : ((List.range' 1 688).all fun k => s9Step k == 1) = true := by
  decide +kernel

theorem kSets1 : ((List.range' 689 688).all fun k => s9Step k == 1) = true := by
  decide +kernel

theorem kSets2 : ((List.range' 1377 688).all fun k => s9Step k == 1) = true := by
  decide +kernel

theorem kSets3 : ((List.range' 2065 688).all fun k => s9Step k == 1) = true := by
  decide +kernel

theorem kSets4 : ((List.range' 2753 688).all fun k => s9Step k == 1) = true := by
  decide +kernel

theorem kSets5 : ((List.range' 3441 684).all fun k => s9Step k == 1) = true := by
  decide +kernel

theorem kOk : ((List.range 4125).all fun k => s9Ok k == 1) = true := by
  decide +kernel

theorem kKeys : CFSG.Sporadic.Schreier.Native.strictlyIncreasing
    (msortK ((List.range 4125).map s9Key)) = true := by
  decide +kernel

end CFSG.KD.HS3850.S9
