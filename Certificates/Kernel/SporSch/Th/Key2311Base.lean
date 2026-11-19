
module

public import Certificates.Kernel.SporSch.Th.Row2322
public import CFSG.Sporadic.ThSchreier.RowBase
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
import CFSG.Certificates.Kernel.Common.Harness

@[expose] public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.ThKey

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier
open CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.ThRow (sh1 lt_of ltFC bindFC)

def C1 : Nat := 0xb9318bc60b06215ff4eb15e228ba41526fe75848bd0133807208caa1fa8551

def C2 : Nat := 0x1e1057aa10c4abdf6972134ec61140ccf2027af03f80a7ed5002b65e4b1cca

theorem key_ok : Nat.beq (canonN (colK ThFC (v4N wKey.u)) (colK ThFC (v4N wKey.v))) (canonN C1 C2) =
    true := by quickRfl

theorem lts : allN 6 (fun k => Nat.blt (nIf(Nat.beq k 0, v4N wKey.u, nIf(Nat.beq k 1, v4N wKey.v,
    nIf(Nat.beq k 2, colK ThFC (v4N wKey.u), nIf(Nat.beq k 3, colK ThFC (v4N wKey.v),
    nIf(Nat.beq k 4, C1, C2)))))) (Nat.shiftLeft 1 248)) = true := by quickRfl

end CertificateChecks.KernelSporSch.ThKey

end
