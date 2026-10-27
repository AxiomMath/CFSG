module

public import Certificates.Kernel.MaxD2.TitsD.Enum
public import Certificates.Kernel.MaxD2.TitsD.Data
public import Certificates.Data.Kernel.MaxD2.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option trace.profiler true
set_option trace.profiler.threshold 1000

namespace CertificateChecks.KernelMaxD2.TitsD

open CFSG.KC.Enum CFSG.KS CFSG.KS.MaxD2 CFSG.KS.PEnum

theorem rep_t0 : allN 3 (fun d => repK 1755 11 6 66 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 1 d)) = true := by quickRfl
theorem rep_t1 : allN 3 (fun d => repK 1755 11 6 66 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 4 d)) = true := by quickRfl
theorem rep_t2 : allN 3 (fun d => repK 1755 11 6 66 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 7 d)) = true := by quickRfl
theorem rep_t3 : allN 3 (fun d => repK 1755 11 6 66 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 10 d)) = true := by quickRfl
theorem rep_t4 : allN 3 (fun d => repK 1755 11 6 66 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 13 d)) = true := by quickRfl
theorem rep_t5 : allN 3 (fun d => repK 1755 11 6 66 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 16 d)) = true := by quickRfl
theorem rep_t6 : allN 3 (fun d => repK 1755 11 6 66 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 19 d)) = true := by quickRfl
theorem rep_t7 : allN 3 (fun d => repK 1755 11 6 66 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 22 d)) = true := by quickRfl

end CertificateChecks.KernelMaxD2.TitsD

end
