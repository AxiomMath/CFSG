module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1EE
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EVS
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue2
public import CFSG.Sporadic.SmallOddCore.ClassSimple

public section

namespace CertificateChecks.KernelSpor.SuzC1EZ

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum
open CFSG.Sporadic.SuzRecog.C1ModelData CFSG.Sporadic.SuzOddCore
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore
  CertificateChecks.KernelSpor.SuzC1EG

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "ie" => invEqK 1782 11 (mask 11) (1782 * 11)
local notation "Id" => pidn 1782 11

@[expose] noncomputable def slQ (lo len : Nat) : Bool :=
  penumSlK 1782 11 (mask 11) (1782 * 11) false SuzC1EQ.G SuzC1EQ.GI 3 SuzC1EQ.cnt SuzC1EQ.T
    SuzC1EQ.PL SuzC1EQ.POS SuzC1EQ.SRT SuzC1EQ.SRI lo len

@[expose] noncomputable def keyK (a : Nat) : Bool :=
  allN 4 fun i => Nat.beq (SuzC1EY (4 * a + i)) (pc (pc (SuzC1EJ a) (SuzC1ET.G i)) (SuzC1EJI a))

@[expose] noncomputable def cosK (a : Nat) : Bool :=
  Nat.beq (SuzC1EJ a) (wK SuzC1EH (cosWords.getD a [])) && ie (SuzC1EJ a) (SuzC1EJI a) &&
    cn (SuzC1EJI a) && Nat.beq (pc (SuzC1EJI a) (SuzC1EJ a)) Id

@[expose] noncomputable def a4q (i : Nat) : Bool :=
  strictB (SuzC1EQ.T i) fun X => Nat.beq (pc X (SuzC1BT 9)) (pc (SuzC1BT 9) X)

@[expose] noncomputable def yq (i : Nat) : Bool :=
  strictB (SuzC1EQ.T i) fun X =>
    Nat.beq (pc X X) Id && !Nat.beq X Id && Nat.beq (fixCntK 1782 11 (mask 11) X) 42

end CertificateChecks.KernelSpor.SuzC1EZ

end
