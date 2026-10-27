module

public import Certificates.Kernel.Sporadic.OddCore.SuzTw
public import Certificates.Data.Kernel.CosetLog
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.SuzTwK

open CFSG.KC.Enum CFSG.KS.PEnum CFSG.KC.CLog CFSG.Sporadic.SuzRecog.B0TwistData
open CertificateChecks.KernelSpor

@[expose] noncomputable def sl (s : Nat) : Bool :=
  factSlK 7 32 (r32 SuzTwN 1) 1365 (r32 SuzTwN 0) SuzTwRL (r32 SuzTwRN) SuzTwFD SuzTwFS SuzTwFW
    SuzTwSD SuzTwDT (Nat.mul (nat_lit 4000) s) (nat_lit 4000)

theorem hd : hdK 7 32 (r32 SuzTwN 0) (r32 SuzTwN 2) 1365 12 twRels [0, 2, 4, 6, 8, 10] SuzTwRL
    (r32 SuzTwRN) SuzTwFD = true := by
  quickRfl

theorem defs : allN (r32 SuzTwN 1) (defK (r32 SuzTwN 0) SuzTwFD SuzTwDT) = true := by
  quickRfl

theorem sl0 : sl 0 = true := by quickRfl
theorem sl1 : sl 1 = true := by quickRfl
theorem sl2 : sl 2 = true := by quickRfl
theorem sl3 : sl 3 = true := by quickRfl
theorem sl4 : sl 4 = true := by quickRfl
theorem sl5 : sl 5 = true := by quickRfl
theorem sl6 : sl 6 = true := by quickRfl
theorem sl7 : sl 7 = true := by quickRfl
theorem sl8 : sl 8 = true := by quickRfl
theorem sl9 : sl 9 = true := by quickRfl

theorem nf : Nat.ble (r32 SuzTwN 0) 40000 = true := by quickRfl

end CertificateChecks.KernelSpor.SuzTwK

end
