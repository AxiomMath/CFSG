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

theorem inv_sl0 : allN 100 (fun d => bAnd(Nat.blt (r32 INV (Nat.add 0 d)) NE.cnt,
    permOK 1755 11 (mask 11) (1755 * 11) (NE.T (Nat.add 0 d)) (NE.T (r32 INV (Nat.add 0 d))))) =
    true := by quickRfl
theorem inv_sl100 : allN 100 (fun d => bAnd(Nat.blt (r32 INV (Nat.add 100 d)) NE.cnt,
    permOK 1755 11 (mask 11) (1755 * 11) (NE.T (Nat.add 100 d)) (NE.T (r32 INV (Nat.add 100 d))))) =
    true := by quickRfl
theorem inv_sl200 : allN 100 (fun d => bAnd(Nat.blt (r32 INV (Nat.add 200 d)) NE.cnt,
    permOK 1755 11 (mask 11) (1755 * 11) (NE.T (Nat.add 200 d)) (NE.T (r32 INV (Nat.add 200 d))))) =
    true := by quickRfl
theorem inv_sl300 : allN 100 (fun d => bAnd(Nat.blt (r32 INV (Nat.add 300 d)) NE.cnt,
    permOK 1755 11 (mask 11) (1755 * 11) (NE.T (Nat.add 300 d)) (NE.T (r32 INV (Nat.add 300 d))))) =
    true := by quickRfl
theorem inv_sl400 : allN 100 (fun d => bAnd(Nat.blt (r32 INV (Nat.add 400 d)) NE.cnt,
    permOK 1755 11 (mask 11) (1755 * 11) (NE.T (Nat.add 400 d)) (NE.T (r32 INV (Nat.add 400 d))))) =
    true := by quickRfl
theorem inv_sl500 : allN 100 (fun d => bAnd(Nat.blt (r32 INV (Nat.add 500 d)) NE.cnt,
    permOK 1755 11 (mask 11) (1755 * 11) (NE.T (Nat.add 500 d)) (NE.T (r32 INV (Nat.add 500 d))))) =
    true := by quickRfl

end CertificateChecks.KernelMaxD2.TitsD

end
