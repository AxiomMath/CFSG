module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtVD
public import Certificates.Kernel.Sporadic.OddCore.SuzBtZD
public import Certificates.Data.Kernel.Spor.BTupO
public import Certificates.Data.Kernel.Spor.BTupI
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtVF

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor

@[expose] noncomputable def wV (i p : Nat) : Nat := btWalk 11 (mask 11) SuzBtV0.G SuzBtV0.R i p

@[expose] noncomputable def kyV (i t : Nat) : Nat :=
  pg 11 (mask 11) (btKey 33 (mask 33) SuzBtV0.K i) t

@[expose] noncomputable def czV (L : Nat → Nat) (i : Nat) : Bool :=
  allN 4 (fun j => allN 3 (fun t => Nat.beq (wV i (pg 11 (mask 11) (L j)
    (pg 11 (mask 11) SuzBtV0.B t))) (pg 11 (mask 11) (L j) (kyV i t))))

@[expose] noncomputable def nrV (L : Nat → Nat) (i : Nat) : Bool :=
  allN 4 (fun j => Bool.not (allN 16 (fun p => Bool.not (allN 3 (fun t =>
    Nat.beq (wV i (pg 11 (mask 11) (L j) (pg 11 (mask 11) SuzBtV0.B t)))
      (btWalk 11 (mask 11) SuzBtL1.G SuzBtL1.R p (kyV i t)))))))

theorem kV0Hd : btHdK SuzBtV0.cnt = true := by quickRfl

theorem kV0Cnt : SuzBtV0.cnt = 512 := by decide

theorem kV0Sl : btSlK 1782 11 (mask 11) 3 33 (mask 33) 7 SuzBtV0.cnt SuzBtV0.B SuzBtV0.G
    SuzBtV0.K SuzBtV0.R SuzBtV0.POS 0 512 = true := by quickRfl

theorem kCz : Nat.beq (btCntN 512 (czV SuzBtL1.G)) 64 = true := by quickRfl

theorem kNr : Nat.beq (btCntN 512 (nrV SuzBtL1.G)) 256 = true := by quickRfl

end CertificateChecks.KernelSpor.SuzBtVF

end
