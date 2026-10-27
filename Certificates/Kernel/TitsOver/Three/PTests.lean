module

public import Certificates.Kernel.TitsOver.Three.Enum
public import Certificates.Kernel.TitsOver.Three.Data
public import Certificates.Data.Kernel.MaxD2.Check
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOver.Three

open CFSG.KC.Enum CFSG.KS CFSG.KS.MaxD2 CFSG.KS.PEnum

theorem p_t0 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 1 d)) = true := by quickRfl
theorem p_t1 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 25 d)) = true := by quickRfl
theorem p_t2 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 49 d)) = true := by quickRfl
theorem p_t3 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 73 d)) = true := by quickRfl
theorem p_t4 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 97 d)) = true := by quickRfl
theorem p_t5 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 121 d)) = true := by quickRfl
theorem p_t6 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 145 d)) = true := by quickRfl
theorem p_t7 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 169 d)) = true := by quickRfl
theorem p_t8 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 193 d)) = true := by quickRfl
theorem p_t9 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 217 d)) = true := by quickRfl
theorem p_t10 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 241 d)) = true := by quickRfl
theorem p_t11 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 265 d)) = true := by quickRfl
theorem p_t12 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 289 d)) = true := by quickRfl
theorem p_t13 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 313 d)) = true := by quickRfl
theorem p_t14 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 337 d)) = true := by quickRfl
theorem p_t15 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 361 d)) = true := by quickRfl
theorem p_t16 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 385 d)) = true := by quickRfl
theorem p_t17 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 409 d)) = true := by quickRfl
theorem p_t18 : allN 24 (fun d => repK 1755 11 2 22 NE.cnt (r32 PT) NE.T FS KS REP REPI RB H
    (Nat.add 433 d)) = true := by quickRfl

end CertificateChecks.KernelTitsOver.Three

end
