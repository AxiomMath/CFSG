module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1EF
public import Certificates.Kernel.Sporadic.OddCore.Suz2302

public section

namespace CertificateChecks.KernelSpor.SuzC1EV

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Sporadic.SuzOddCore CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore
  CertificateChecks.KernelSpor.SuzC1EF

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "Id" => pidn 1782 11

@[expose] noncomputable def slV (s : Nat) : Bool :=
  penumSlK 1782 11 (mask 11) (1782 * 11) false SuzC1EV.G SuzC1EV.GI 7 SuzC1EV.cnt SuzC1EV.T
    SuzC1EV.PL SuzC1EV.POS SuzC1EV.SRT SuzC1EV.SRI (64 * s) 64

@[expose] noncomputable def vK (k : Nat) : Bool :=
  strictB (SuzC1EV.T k) fun X =>
    !Nat.beq (pc X X) Id || Nat.beq X Id || Nat.beq (fixCntK 1782 11 (mask 11) X) 42 || memT X

@[expose] noncomputable def cK (X : Nat) : Bool :=
  allBelow 4 fun i => Nat.beq (pc X (SuzC1ET.G i)) (pc (SuzC1ET.G i) X)

@[expose] noncomputable def wg (F : Nat → Nat) (i : Nat) : Nat := CFSG.KS.Row.rg 32 (mask 32) F 0 i

@[expose] noncomputable def ccK (X c : Nat) : Bool :=
  bIf(Nat.beq c 0, cK X,
    strictB (Nat.div (Nat.sub c 1) 2048) fun j => strictB (Nat.mod (Nat.sub c 1) 2048) fun p =>
      bAnd(Nat.blt j 4, bAnd(Nat.blt p 1782,
        Bool.not (Nat.beq (pg 11 (mask 11) X (pg 11 (mask 11) (SuzC1ET.G j) p))
          (pg 11 (mask 11) (SuzC1ET.G j) (pg 11 (mask 11) X p))))))

end CertificateChecks.KernelSpor.SuzC1EV

end
