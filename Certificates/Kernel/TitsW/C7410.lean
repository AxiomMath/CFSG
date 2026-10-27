module

public import Certificates.Kernel.TitsW.Defs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsW.C7410

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CertificateChecks.KernelTitsW

local notation "RZ" => pm (pm (WD [1, -2]) (WD [-4, 3, 3, -4, 3, 3])) (pv (WD [1, -2]))
local notation "RT" =>
  pm (pm (WD [1, -2, -1]) (WD [-4, -4, 13, 13, -4, -4, -4, -4, 13, 13, -4, -4])) (pv (WD [1, -2, -1]))
local notation "CZ0" => pm (pm RZ (DS 0)) (pm RZ (pv (DS 0)))
local notation "CZ1" => pm (pm RZ (DS 1)) (pm RZ (pv (DS 1)))
local notation "CT0" => pm (pm RT (DS 0)) (pm RT (pv (DS 0)))
local notation "CT1" => pm (pm RT (DS 1)) (pm RT (pv (DS 1)))

theorem z2 : Nat.beq (pm RZ RZ) pe = true := by quickRfl
theorem z0p : Nat.beq (ppw CZ0 5) pe = true := by quickRfl
theorem z0n : (!Nat.beq CZ0 pe) = true := by quickRfl
theorem z1p : Nat.beq (ppw CZ1 5) pe = true := by quickRfl
theorem z1n : (!Nat.beq CZ1 pe) = true := by quickRfl
theorem t2 : Nat.beq (pm RT RT) pe = true := by quickRfl
theorem t0p : Nat.beq (ppw CT0 13) pe = true := by quickRfl
theorem t0n : (!Nat.beq CT0 pe) = true := by quickRfl
theorem t1p : Nat.beq (ppw CT1 13) pe = true := by quickRfl
theorem t1n : (!Nat.beq CT1 pe) = true := by quickRfl

end CertificateChecks.KernelTitsW.C7410

end
