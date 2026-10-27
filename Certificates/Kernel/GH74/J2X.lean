module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.GH74EvSporData
public import Certificates.Data.Kernel.Spor.Prim
public import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import Certificates.Data.GH74EvSporData
public meta import Certificates.Data.CFSGNative.SmallOddCore.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelGH74.J2X

open CFSG.GH74.Generic.S45.EvSpor CFSG.Sporadic.SmallOddCore.Native

meta def xM : Array (Array Nat) :=
  #[natArr j2KbA, natArr j2KbB, natArr j2VA, natArr j2VB, natArr j2E0, natArr j2E1, natArr j2E2,
    natArr j2E3]

meta def xiM : Array (Array Nat) := xM.map (CFSG.Monster.B.Co2.Native.invCand 315)

end CertificateChecks.KernelGH74.J2X

#kmisc_packarrs CertificateChecks.KernelGH74.J2XT CertificateChecks.KernelGH74.J2X.xM 9
#kmisc_packarrs CertificateChecks.KernelGH74.J2XI CertificateChecks.KernelGH74.J2X.xiM 9

namespace CertificateChecks.KernelGH74.J2X

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.GH74.Generic.S45.EvSpor CFSG.Sporadic.SmallOddCore.Native

theorem x_eq : j2KbA.toList.map UInt32.toNat = (List.range 315).map (pg 9 (mask 9) (J2XT 0)) ∧
    j2KbB.toList.map UInt32.toNat = (List.range 315).map (pg 9 (mask 9) (J2XT 1)) ∧
    j2VA.toList.map UInt32.toNat = (List.range 315).map (pg 9 (mask 9) (J2XT 2)) ∧
    j2VB.toList.map UInt32.toNat = (List.range 315).map (pg 9 (mask 9) (J2XT 3)) ∧
    j2E0.toList.map UInt32.toNat = (List.range 315).map (pg 9 (mask 9) (J2XT 4)) ∧
    j2E1.toList.map UInt32.toNat = (List.range 315).map (pg 9 (mask 9) (J2XT 5)) ∧
    j2E2.toList.map UInt32.toNat = (List.range 315).map (pg 9 (mask 9) (J2XT 6)) ∧
    j2E3.toList.map UInt32.toNat = (List.range 315).map (pg 9 (mask 9) (J2XT 7)) := by
  decide +kernel

theorem x_perm : allN 8 (fun j => bAnd(canonK 315 9 (mask 9) (315 * 9) (J2XT j),
    bAnd(canonK 315 9 (mask 9) (315 * 9) (J2XI j), invEqK 315 9 (mask 9) (315 * 9) (J2XT j) (J2XI j))))
    = true := by
  quickRfl

end CertificateChecks.KernelGH74.J2X

end
