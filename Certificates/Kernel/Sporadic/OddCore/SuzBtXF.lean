module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtXD
public import Certificates.Data.Kernel.Spor.BTupI
public import Certificates.Data.Kernel.Spor.Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtXF

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor

local notation "pg4" => pg 4 (mask 4)

@[expose] noncomputable def TB (j : Nat) : Nat :=
  nIf(Nat.beq j 0, 17274361803683611920, 9929781798390354960)

@[expose] noncomputable def pw (y e p : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) p (fun _ q => pg4 y q) e

@[expose] noncomputable def isOne (y e : Nat) : Bool :=
  allN 16 (fun p => Nat.beq (pw y e p) p)

@[expose] noncomputable def fxK (y : Nat) : Bool :=
  bIf(bAnd(Bool.not (isOne y 1), Bool.rec (motive := fun _ => Bool) (isOne y 5) true (isOne y 3)),
    allN 15 (fun p => Bool.not (Nat.beq (pg4 y (Nat.succ p)) (Nat.succ p))), true)

@[expose] noncomputable def memK (K : Nat → Nat) (cnt T : Nat) : Bool :=
  Bool.not (allN cnt (fun s => Bool.not (Nat.beq (btKey 64 (mask 64) K s) T)))

theorem kX0Hd : btHdK SuzBtX0.cnt = true := by quickRfl
theorem kX0Cnt : SuzBtX0.cnt = 60 := by decide
theorem kX0Sl : btSlK 16 4 (mask 4) 16 64 (mask 64) 2 SuzBtX0.cnt SuzBtX0.B SuzBtX0.G
    SuzBtX0.K SuzBtX0.R SuzBtX0.POS 0 60 = true := by quickRfl
theorem kX0Tb : allN 2 (fun j => memK SuzBtX0.K 60 (TB j)) = true := by quickRfl
theorem kX0Fx : allN 60 (fun s => fxK (btKey 64 (mask 64) SuzBtX0.K s)) = true := by quickRfl

theorem kX1Hd : btHdK SuzBtX1.cnt = true := by quickRfl
theorem kX1Cnt : SuzBtX1.cnt = 60 := by decide
theorem kX1Sl : btSlK 16 4 (mask 4) 16 64 (mask 64) 2 SuzBtX1.cnt SuzBtX1.B SuzBtX1.G
    SuzBtX1.K SuzBtX1.R SuzBtX1.POS 0 60 = true := by quickRfl
theorem kX1Tb : allN 2 (fun j => memK SuzBtX1.K 60 (TB j)) = true := by quickRfl
theorem kX1Fx : allN 60 (fun s => fxK (btKey 64 (mask 64) SuzBtX1.K s)) = true := by quickRfl

theorem kX2Hd : btHdK SuzBtX2.cnt = true := by quickRfl
theorem kX2Cnt : SuzBtX2.cnt = 60 := by decide
theorem kX2Sl : btSlK 16 4 (mask 4) 16 64 (mask 64) 2 SuzBtX2.cnt SuzBtX2.B SuzBtX2.G
    SuzBtX2.K SuzBtX2.R SuzBtX2.POS 0 60 = true := by quickRfl
theorem kX2Tb : allN 2 (fun j => memK SuzBtX2.K 60 (TB j)) = true := by quickRfl
theorem kX2Fx : allN 60 (fun s => fxK (btKey 64 (mask 64) SuzBtX2.K s)) = true := by quickRfl

theorem kX3Hd : btHdK SuzBtX3.cnt = true := by quickRfl
theorem kX3Cnt : SuzBtX3.cnt = 60 := by decide
theorem kX3Sl : btSlK 16 4 (mask 4) 16 64 (mask 64) 2 SuzBtX3.cnt SuzBtX3.B SuzBtX3.G
    SuzBtX3.K SuzBtX3.R SuzBtX3.POS 0 60 = true := by quickRfl
theorem kX3Tb : allN 2 (fun j => memK SuzBtX3.K 60 (TB j)) = true := by quickRfl
theorem kX3Fx : allN 60 (fun s => fxK (btKey 64 (mask 64) SuzBtX3.K s)) = true := by quickRfl

end CertificateChecks.KernelSpor.SuzBtXF

end
