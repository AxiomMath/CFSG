module

public import Certificates.Kernel.Sporadic.OddCore.SuzBtTD
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EG
public import Certificates.Data.Kernel.Spor.BTupI
public import CFSG.Sporadic.SuzRecog.SuzL34.Facts
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzBtWF

open CFSG.KC.Enum CFSG.KS CFSG.KS.BTup CertificateChecks.KernelSpor
  CertificateChecks.KernelSpor.SuzC1EG CFSG.Sporadic.SuzRecog.SuzL34Cert

@[expose] noncomputable def agB (f g : Nat → Nat) : Bool :=
  allN 3 (fun t => Nat.beq (f (pg 11 (mask 11) SuzBtT0.B t)) (g (pg 11 (mask 11) SuzBtT0.B t)))

@[expose] noncomputable def pW (p : Nat) : Nat := pg 11 (mask 11) (SuzTwG 6) p

@[expose] noncomputable def fxN (y : Nat → Nat) : Nat := btCntN 1782 (fun p => Nat.beq (y p) p)

@[expose] noncomputable def bad (y : Nat → Nat) : Bool :=
  bAnd(agB (fun p => y (y p)) (fun p => p), bAnd(Bool.not (agB y (fun p => p)),
    bAnd(Bool.not (agB y pW), bAnd(Nat.beq (fxN y) 42, Nat.beq (fxN (fun p => y (pW p))) 42))))

@[expose] noncomputable def inT11 (y : Nat → Nat) : Bool :=
  Bool.not (allN 64 (fun q => Bool.not (bIf(agB (fun p => pg 11 (mask 11) (SuzC1ET.T q) p) y, true,
    agB (fun p => pW (pg 11 (mask 11) (SuzC1ET.T q) p)) y))))

theorem kSq : allN 512 (fun k => inT11 (fun p => pg 11 (mask 11) (SuzC1EV.T k)
    (pg 11 (mask 11) (SuzC1EV.T k) p))) = true := by quickRfl

theorem kRt : allN 512 (fun k => bIf(agB (fun p => pg 11 (mask 11) (SuzC1EV.T k)
    (pg 11 (mask 11) (SuzC1EV.T k) p)) pW,
    Bool.not (allN 64 (fun q => Bool.not (bIf(agB (fun p => pg 11 (mask 11) (SuzC1ET.T q)
      (pg 11 (mask 11) (decK lam0Dec) p)) (fun p => pg 11 (mask 11) (SuzC1EV.T k) p), true,
      agB (fun p => pW (pg 11 (mask 11) (SuzC1ET.T q) (pg 11 (mask 11) (decK lam0Dec) p)))
        (fun p => pg 11 (mask 11) (SuzC1EV.T k) p))))), true)) = true := by quickRfl

theorem kD : allN 64 (fun q => bAnd(Bool.not (bad (fun p => pg 11 (mask 11) (SuzC1ET.T q)
    (pg 11 (mask 11) (decK lam0Dec) p))), Bool.not (bad (fun p => pW (pg 11 (mask 11)
      (SuzC1ET.T q) (pg 11 (mask 11) (decK lam0Dec) p)))))) = true := by quickRfl

theorem kA : bAnd(agB (fun p => pg 11 (mask 11) (decK aDec) (pW p))
    (fun p => pW (pg 11 (mask 11) (decK aDec) p)),
    bAnd(Bool.not (agB (fun p => pg 11 (mask 11) (decK aDec) p) pW),
      bad (fun p => pg 11 (mask 11) (decK aDec) p))) = true := by quickRfl

theorem kL : bAnd(agB (fun p => pg 11 (mask 11) (decK lam0Dec) (pW p))
    (fun p => pW (pg 11 (mask 11) (decK lam0Dec) p)),
    agB (fun p => pg 11 (mask 11) (decK lam0Dec) (pg 11 (mask 11) (decK lam0Dec) p)) pW) = true := by
  quickRfl

end CertificateChecks.KernelSpor.SuzBtWF

end
