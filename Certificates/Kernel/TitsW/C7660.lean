module

public import Certificates.Kernel.TitsW.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsW.C7660

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelTitsW

local notation "G1" => WD [2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, -4, 3, 3, -4, -4]
local notation "H1" => pm (pv G1) (WD [13])
local notation "G2" => WD [-4, 3, 3, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1]
local notation "H2" => pm (pv G2) (WD [-4, -4])
local notation "G3" => WD [13, 13, 4]
local notation "H3" => pm (pv G3) (WD [-4, 3, 3])

theorem g1 : Nat.beq (pm G1 (pm G1 G1)) pe = true := by quickRfl
theorem h1 : Nat.beq (pm H1 (pm H1 H1)) pe = true := by quickRfl
theorem g2 : Nat.beq (pm G2 (pm G2 G2)) pe = true := by quickRfl
theorem h2 : Nat.beq (pm H2 (pm H2 H2)) pe = true := by quickRfl
theorem g3 : Nat.beq (pm G3 (pm G3 (pm G3 (pm G3 G3)))) pe = true := by quickRfl
theorem h3 : Nat.beq (pm H3 (pm H3 (pm H3 (pm H3 H3)))) pe = true := by quickRfl

end CertificateChecks.KernelTitsW.C7660

end
