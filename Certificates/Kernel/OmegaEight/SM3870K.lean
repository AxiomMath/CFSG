module

public import Certificates.Data.Kernel.O8.SA
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSTabData
public import Certificates.Kernel.OmegaEight.SM3870Data
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] noncomputable def actK (i e : Nat) : Nat :=
  fld(sActRow i, Nat.mul (nat_lit 7) e, nat_lit 127)

@[expose] noncomputable def mtK (i j : Nat) : Nat :=
  fld(sMtRow i, Nat.mul (nat_lit 9) j, nat_lit 511)

@[expose] noncomputable def ginvK (i : Nat) : Nat := fld(sGinvLit, Nat.mul (nat_lit 9) i, nat_lit 511)

@[expose] noncomputable def dK (i : Nat) : Nat := saAtK dLit i

@[expose] noncomputable def ix9 (T i : Nat) : Nat := fld(T, Nat.mul (nat_lit 9) i, nat_lit 511)

@[expose] noncomputable def dAppAt (k : Nat) : Bool :=
  Nat.beq (matAppK (dK (Nat.shiftRight k (nat_lit 7))) (Nat.land k (nat_lit 127)))
    (actK (Nat.shiftRight k (nat_lit 7)) (Nat.land k (nat_lit 127)))

@[expose] noncomputable def dMulAt (k : Nat) : Bool :=
  strictB (Nat.shiftRight k (nat_lit 9)) fun i => strictB (Nat.land k (nat_lit 511)) fun j =>
    Nat.beq (matMulK (dK i) (dK j)) (dK (mtK i j))

@[expose] noncomputable def dInvAt (i : Nat) : Bool :=
  Nat.beq (matMulK (dK (ginvK i)) (dK i)) idK

@[expose] noncomputable def dSortAt (i : Nat) : Bool :=
  bAnd(Nat.blt (ix9 dSPI i) (nat_lit 512), bAnd(Nat.beq (ix9 dSP (ix9 dSPI i)) i,
    bIf(Nat.blt i (nat_lit 511), Nat.blt (dK (ix9 dSP i)) (dK (ix9 dSP (Nat.succ i))), true)))

theorem kA : allN 65536 dAppAt = true := by quickRfl
theorem kI : bAnd(Nat.beq (dK 0) idK, allN 512 dInvAt) = true := by quickRfl
theorem kSort : allN 512 dSortAt = true := by quickRfl

theorem kM0 : allBlk 0 dMulAt 16384 = true := by quickRfl
theorem kM1 : allBlk 16384 dMulAt 16384 = true := by quickRfl
theorem kM2 : allBlk 32768 dMulAt 16384 = true := by quickRfl
theorem kM3 : allBlk 49152 dMulAt 16384 = true := by quickRfl
theorem kM4 : allBlk 65536 dMulAt 16384 = true := by quickRfl
theorem kM5 : allBlk 81920 dMulAt 16384 = true := by quickRfl
theorem kM6 : allBlk 98304 dMulAt 16384 = true := by quickRfl
theorem kM7 : allBlk 114688 dMulAt 16384 = true := by quickRfl
theorem kM8 : allBlk 131072 dMulAt 16384 = true := by quickRfl
theorem kM9 : allBlk 147456 dMulAt 16384 = true := by quickRfl
theorem kM10 : allBlk 163840 dMulAt 16384 = true := by quickRfl
theorem kM11 : allBlk 180224 dMulAt 16384 = true := by quickRfl
theorem kM12 : allBlk 196608 dMulAt 16384 = true := by quickRfl
theorem kM13 : allBlk 212992 dMulAt 16384 = true := by quickRfl
theorem kM14 : allBlk 229376 dMulAt 16384 = true := by quickRfl
theorem kM15 : allBlk 245760 dMulAt 16384 = true := by quickRfl

end CertificateChecks.KernelO8

end
