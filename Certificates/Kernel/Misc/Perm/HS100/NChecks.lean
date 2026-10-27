module

public import Certificates.Kernel.Misc.Perm.HS100.NData
public import Certificates.Kernel.Misc.Perm.HS100.S0Checks
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.BfsPinBase
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.HS100.N

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.BfsPin
open CFSG.KC.Misc.ArrEnum (permB memK)
open CertificateChecks.KernelMisc.HS100
open CertificateChecks.KernelMisc.HS100.S0 (cK)
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus

@[expose] noncomputable def pZ (a x : Nat) : Nat :=
  pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) a x) (pinvS 100 7 (mask 7) a)

@[expose] noncomputable def selK (e : Nat) (b : ZMod 2) : Nat := if b = 0 then pidn 100 7 else e

@[expose] noncomputable def vecEK (v : Fin 4 → ZMod 2) : Nat :=
  pcomp 100 7 (mask 7) (selK (S0.EX.F 0) (v 0)) (pcomp 100 7 (mask 7) (selK (S0.EX.F 1) (v 1))
    (pcomp 100 7 (mask 7) (selK (S0.EX.F 2) (v 2)) (pcomp 100 7 (mask 7) (selK (S0.EX.F 3) (v 3))
      (pidn 100 7))))

@[expose] noncomputable def centPt (t : Nat) : Bool :=
  !(allN 4 fun i => cK (NN.T t) (S0.EX.F i)) || memK S0.E0.N S0.E0.T (NN.T t)

theorem perms : (allN 2 (fun k => permB 100 7 (NX.F k)) && allN 2 (fun k => permB 100 7 (RX k))) =
    true := by quickRfl

theorem rx_eq : ∀ k : Fin 2, unpack 100 7 (RX k.1) = I2.i2R[k.1]! := by decide +kernel

theorem nums :(Nat.beq NN.ng 2 && Nat.beq NN.N 11520 && allN 2 (fun k => Nat.beq (NN.G k) (NX.F k))) =
    true := by quickRfl

theorem keys : keysSK 100 7 zasNKeys NN.N NN.T ((List.range 11520).map NNK) = true := by quickRfl

theorem rhoK : ∀ j : Fin 2, ∀ i : Fin 4,
    Nat.beq (pZ (NX.F j.1) (S0.EX.F i.1)) (vecEK (I2.rho j i)) = true := by decide +kernel

theorem kxK : ∀ i : Fin 4, Nat.beq (pZ (RX 0) (S0.EX.F i.1)) (vecEK (I2.kx i)) = true := by
  decide +kernel

theorem kyK : ∀ i : Fin 4, Nat.beq (pZ (RX 1) (S0.EX.F i.1)) (vecEK (I2.ky i)) = true := by
  decide +kernel

theorem mems : (memK S0.E0.N S0.E0.T (pcomp 100 7 (mask 7) (RX 0) (RX 0)) &&
    memK S0.E0.N S0.E0.T (pcomp 100 7 (mask 7) (RX 1) (RX 1)) &&
    memK S0.E0.N S0.E0.T (pcomp 100 7 (mask 7) (pcomp 100 7 (mask 7) (RX 0) (RX 1))
      (pcomp 100 7 (mask 7) (RX 0) (RX 1))) &&
    memK NN.N NN.T (RX 0) && memK NN.N NN.T (RX 1)) = true := by quickRfl

theorem npPerm : allN NN.N (fun t => permB 100 7 (NN.T t)) = true := by quickRfl

theorem cent : allN NN.N centPt = true := by quickRfl

end CertificateChecks.KernelMisc.HS100.N

end
