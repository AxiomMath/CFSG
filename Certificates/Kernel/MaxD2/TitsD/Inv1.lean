module

public import Certificates.Kernel.MaxD2.TitsD.Enum
public import Certificates.Kernel.MaxD2.TitsD.TransData
public import Certificates.Data.Kernel.Spor.PEnum
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.TitsD

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum

theorem inv_sl600 : allN 100 (fun d => bAnd(Nat.blt (r32 INV (Nat.add 600 d)) NE.cnt,
    permOK 1755 11 (mask 11) (1755 * 11) (NE.T (Nat.add 600 d)) (NE.T (r32 INV (Nat.add 600 d))))) =
    true := by quickRfl
theorem inv_sl700 : allN 100 (fun d => bAnd(Nat.blt (r32 INV (Nat.add 700 d)) NE.cnt,
    permOK 1755 11 (mask 11) (1755 * 11) (NE.T (Nat.add 700 d)) (NE.T (r32 INV (Nat.add 700 d))))) =
    true := by quickRfl
theorem inv_sl800 : allN 100 (fun d => bAnd(Nat.blt (r32 INV (Nat.add 800 d)) NE.cnt,
    permOK 1755 11 (mask 11) (1755 * 11) (NE.T (Nat.add 800 d)) (NE.T (r32 INV (Nat.add 800 d))))) =
    true := by quickRfl
theorem inv_sl900 : allN 100 (fun d => bAnd(Nat.blt (r32 INV (Nat.add 900 d)) NE.cnt,
    permOK 1755 11 (mask 11) (1755 * 11) (NE.T (Nat.add 900 d)) (NE.T (r32 INV (Nat.add 900 d))))) =
    true := by quickRfl
theorem inv_sl1000 : allN 100 (fun d => bAnd(Nat.blt (r32 INV (Nat.add 1000 d)) NE.cnt,
    permOK 1755 11 (mask 11) (1755 * 11) (NE.T (Nat.add 1000 d))
      (NE.T (r32 INV (Nat.add 1000 d))))) = true := by quickRfl
theorem inv_sl1100 : allN 100 (fun d => bAnd(Nat.blt (r32 INV (Nat.add 1100 d)) NE.cnt,
    permOK 1755 11 (mask 11) (1755 * 11) (NE.T (Nat.add 1100 d))
      (NE.T (r32 INV (Nat.add 1100 d))))) = true := by quickRfl

end CertificateChecks.KernelMaxD2.TitsD

end
