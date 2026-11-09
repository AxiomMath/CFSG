module

public import Certificates.Kernel.Sporadic.Fi24Alpha.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Alpha KV9 "Certificates/Kernel/Sporadic/Fi24Alpha/data/v9.bin" 152491 4 24398560 4531800003638748236

public section

open CFSG.KD.Fi24Alpha CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1293 : Nat := CFSG.KD.Fi24Alpha.KV9 0
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1294 : Nat := CFSG.KD.Fi24Alpha.KV9 1
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1295 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1293, CFSG.KD.Fi24Alpha.Pc.v1294]
theorem CFSG.KD.Fi24Alpha.Pc.p1293 : Nat.beq (runC AR SD 1293 (ckL CFSG.KD.Fi24Alpha.Pc.l1295) 2 1293 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1295 : Nat := CFSG.KD.Fi24Alpha.KV9 2
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1296 : Nat := CFSG.KD.Fi24Alpha.KV9 3
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1297 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1293, CFSG.KD.Fi24Alpha.Pc.v1294, CFSG.KD.Fi24Alpha.Pc.v1295, CFSG.KD.Fi24Alpha.Pc.v1296]
theorem CFSG.KD.Fi24Alpha.Pc.p1295 : Nat.beq (runC AR SD 1293 (ckL CFSG.KD.Fi24Alpha.Pc.l1297) 2 1295 CFSG.KD.Fi24Alpha.Pc.l1295) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1297 : Nat := CFSG.KD.Fi24Alpha.KV9 4
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1298 : Nat := CFSG.KD.Fi24Alpha.KV9 5
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1299 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1293, CFSG.KD.Fi24Alpha.Pc.v1294, CFSG.KD.Fi24Alpha.Pc.v1295, CFSG.KD.Fi24Alpha.Pc.v1296, CFSG.KD.Fi24Alpha.Pc.v1297, CFSG.KD.Fi24Alpha.Pc.v1298]
theorem CFSG.KD.Fi24Alpha.Pc.p1297 : Nat.beq (runC AR SD 1293 (ckL CFSG.KD.Fi24Alpha.Pc.l1299) 2 1297 CFSG.KD.Fi24Alpha.Pc.l1297) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1299 : Nat := CFSG.KD.Fi24Alpha.KV9 6
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1300 : Nat := CFSG.KD.Fi24Alpha.KV9 7
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1301 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1293, CFSG.KD.Fi24Alpha.Pc.v1294, CFSG.KD.Fi24Alpha.Pc.v1295, CFSG.KD.Fi24Alpha.Pc.v1296, CFSG.KD.Fi24Alpha.Pc.v1297, CFSG.KD.Fi24Alpha.Pc.v1298, CFSG.KD.Fi24Alpha.Pc.v1299, CFSG.KD.Fi24Alpha.Pc.v1300]
theorem CFSG.KD.Fi24Alpha.Pc.p1299 : Nat.beq (runC AR SD 1293 (ckL CFSG.KD.Fi24Alpha.Pc.l1301) 2 1299 CFSG.KD.Fi24Alpha.Pc.l1299) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1301 : Nat := CFSG.KD.Fi24Alpha.KV9 8
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1302 : Nat := CFSG.KD.Fi24Alpha.KV9 9
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1303 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1293, CFSG.KD.Fi24Alpha.Pc.v1294, CFSG.KD.Fi24Alpha.Pc.v1295, CFSG.KD.Fi24Alpha.Pc.v1296, CFSG.KD.Fi24Alpha.Pc.v1297, CFSG.KD.Fi24Alpha.Pc.v1298, CFSG.KD.Fi24Alpha.Pc.v1299, CFSG.KD.Fi24Alpha.Pc.v1300, CFSG.KD.Fi24Alpha.Pc.v1301, CFSG.KD.Fi24Alpha.Pc.v1302]
theorem CFSG.KD.Fi24Alpha.Pc.p1301 : Nat.beq (runC AR SD 1293 (ckL CFSG.KD.Fi24Alpha.Pc.l1303) 2 1301 CFSG.KD.Fi24Alpha.Pc.l1301) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1303 : Nat := CFSG.KD.Fi24Alpha.KV9 10
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1304 : Nat := CFSG.KD.Fi24Alpha.KV9 11
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1305 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1293, CFSG.KD.Fi24Alpha.Pc.v1294, CFSG.KD.Fi24Alpha.Pc.v1295, CFSG.KD.Fi24Alpha.Pc.v1296, CFSG.KD.Fi24Alpha.Pc.v1297, CFSG.KD.Fi24Alpha.Pc.v1298, CFSG.KD.Fi24Alpha.Pc.v1299, CFSG.KD.Fi24Alpha.Pc.v1300, CFSG.KD.Fi24Alpha.Pc.v1301, CFSG.KD.Fi24Alpha.Pc.v1302, CFSG.KD.Fi24Alpha.Pc.v1303, CFSG.KD.Fi24Alpha.Pc.v1304]
theorem CFSG.KD.Fi24Alpha.Pc.p1303 : Nat.beq (runC AR SD 1293 (ckL CFSG.KD.Fi24Alpha.Pc.l1305) 2 1303 CFSG.KD.Fi24Alpha.Pc.l1303) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1305 : Nat := CFSG.KD.Fi24Alpha.KV9 12
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1306 : Nat := CFSG.KD.Fi24Alpha.KV9 13
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1307 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1293, CFSG.KD.Fi24Alpha.Pc.v1294, CFSG.KD.Fi24Alpha.Pc.v1295, CFSG.KD.Fi24Alpha.Pc.v1296, CFSG.KD.Fi24Alpha.Pc.v1297, CFSG.KD.Fi24Alpha.Pc.v1298, CFSG.KD.Fi24Alpha.Pc.v1299, CFSG.KD.Fi24Alpha.Pc.v1300, CFSG.KD.Fi24Alpha.Pc.v1301, CFSG.KD.Fi24Alpha.Pc.v1302, CFSG.KD.Fi24Alpha.Pc.v1303, CFSG.KD.Fi24Alpha.Pc.v1304, CFSG.KD.Fi24Alpha.Pc.v1305, CFSG.KD.Fi24Alpha.Pc.v1306]
theorem CFSG.KD.Fi24Alpha.Pc.p1305 : Nat.beq (runC AR SD 1293 (ckL CFSG.KD.Fi24Alpha.Pc.l1307) 2 1305 CFSG.KD.Fi24Alpha.Pc.l1305) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1307 : Nat := CFSG.KD.Fi24Alpha.KV9 14
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1308 : Nat := CFSG.KD.Fi24Alpha.KV9 15
theorem CFSG.KD.Fi24Alpha.Pc.f90 : Nat.beq (runC AR SD 1293 (finC AR SD (nat_lit 90) 1293 1309) 2 1307 CFSG.KD.Fi24Alpha.Pc.l1307) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk90 : chk (nat_lit 90) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 90) (lo := 1293) (hi := 1309) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1295) CFSG.KD.Fi24Alpha.Pc.p1293 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1297) CFSG.KD.Fi24Alpha.Pc.p1295 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1299) CFSG.KD.Fi24Alpha.Pc.p1297 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1301) CFSG.KD.Fi24Alpha.Pc.p1299 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1303) CFSG.KD.Fi24Alpha.Pc.p1301 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1305) CFSG.KD.Fi24Alpha.Pc.p1303 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1307) CFSG.KD.Fi24Alpha.Pc.p1305 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f90

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1309 : Nat := CFSG.KD.Fi24Alpha.KV9 16
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1310 : Nat := CFSG.KD.Fi24Alpha.KV9 17
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1311 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1309, CFSG.KD.Fi24Alpha.Pc.v1310]
theorem CFSG.KD.Fi24Alpha.Pc.p1309 : Nat.beq (runC AR SD 1309 (ckL CFSG.KD.Fi24Alpha.Pc.l1311) 2 1309 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1311 : Nat := CFSG.KD.Fi24Alpha.KV9 18
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1312 : Nat := CFSG.KD.Fi24Alpha.KV9 19
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1313 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1309, CFSG.KD.Fi24Alpha.Pc.v1310, CFSG.KD.Fi24Alpha.Pc.v1311, CFSG.KD.Fi24Alpha.Pc.v1312]
theorem CFSG.KD.Fi24Alpha.Pc.p1311 : Nat.beq (runC AR SD 1309 (ckL CFSG.KD.Fi24Alpha.Pc.l1313) 2 1311 CFSG.KD.Fi24Alpha.Pc.l1311) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1313 : Nat := CFSG.KD.Fi24Alpha.KV9 20
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1314 : Nat := CFSG.KD.Fi24Alpha.KV9 21
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1315 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1309, CFSG.KD.Fi24Alpha.Pc.v1310, CFSG.KD.Fi24Alpha.Pc.v1311, CFSG.KD.Fi24Alpha.Pc.v1312, CFSG.KD.Fi24Alpha.Pc.v1313, CFSG.KD.Fi24Alpha.Pc.v1314]
theorem CFSG.KD.Fi24Alpha.Pc.p1313 : Nat.beq (runC AR SD 1309 (ckL CFSG.KD.Fi24Alpha.Pc.l1315) 2 1313 CFSG.KD.Fi24Alpha.Pc.l1313) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1315 : Nat := CFSG.KD.Fi24Alpha.KV9 22
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1316 : Nat := CFSG.KD.Fi24Alpha.KV9 23
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1317 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1309, CFSG.KD.Fi24Alpha.Pc.v1310, CFSG.KD.Fi24Alpha.Pc.v1311, CFSG.KD.Fi24Alpha.Pc.v1312, CFSG.KD.Fi24Alpha.Pc.v1313, CFSG.KD.Fi24Alpha.Pc.v1314, CFSG.KD.Fi24Alpha.Pc.v1315, CFSG.KD.Fi24Alpha.Pc.v1316]
theorem CFSG.KD.Fi24Alpha.Pc.p1315 : Nat.beq (runC AR SD 1309 (ckL CFSG.KD.Fi24Alpha.Pc.l1317) 2 1315 CFSG.KD.Fi24Alpha.Pc.l1315) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1317 : Nat := CFSG.KD.Fi24Alpha.KV9 24
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1318 : Nat := CFSG.KD.Fi24Alpha.KV9 25
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1319 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1309, CFSG.KD.Fi24Alpha.Pc.v1310, CFSG.KD.Fi24Alpha.Pc.v1311, CFSG.KD.Fi24Alpha.Pc.v1312, CFSG.KD.Fi24Alpha.Pc.v1313, CFSG.KD.Fi24Alpha.Pc.v1314, CFSG.KD.Fi24Alpha.Pc.v1315, CFSG.KD.Fi24Alpha.Pc.v1316, CFSG.KD.Fi24Alpha.Pc.v1317, CFSG.KD.Fi24Alpha.Pc.v1318]
theorem CFSG.KD.Fi24Alpha.Pc.p1317 : Nat.beq (runC AR SD 1309 (ckL CFSG.KD.Fi24Alpha.Pc.l1319) 2 1317 CFSG.KD.Fi24Alpha.Pc.l1317) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1319 : Nat := CFSG.KD.Fi24Alpha.KV9 26
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1320 : Nat := CFSG.KD.Fi24Alpha.KV9 27
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1321 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1309, CFSG.KD.Fi24Alpha.Pc.v1310, CFSG.KD.Fi24Alpha.Pc.v1311, CFSG.KD.Fi24Alpha.Pc.v1312, CFSG.KD.Fi24Alpha.Pc.v1313, CFSG.KD.Fi24Alpha.Pc.v1314, CFSG.KD.Fi24Alpha.Pc.v1315, CFSG.KD.Fi24Alpha.Pc.v1316, CFSG.KD.Fi24Alpha.Pc.v1317, CFSG.KD.Fi24Alpha.Pc.v1318, CFSG.KD.Fi24Alpha.Pc.v1319, CFSG.KD.Fi24Alpha.Pc.v1320]
theorem CFSG.KD.Fi24Alpha.Pc.p1319 : Nat.beq (runC AR SD 1309 (ckL CFSG.KD.Fi24Alpha.Pc.l1321) 2 1319 CFSG.KD.Fi24Alpha.Pc.l1319) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1321 : Nat := CFSG.KD.Fi24Alpha.KV9 28
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1322 : Nat := CFSG.KD.Fi24Alpha.KV9 29
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1323 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1309, CFSG.KD.Fi24Alpha.Pc.v1310, CFSG.KD.Fi24Alpha.Pc.v1311, CFSG.KD.Fi24Alpha.Pc.v1312, CFSG.KD.Fi24Alpha.Pc.v1313, CFSG.KD.Fi24Alpha.Pc.v1314, CFSG.KD.Fi24Alpha.Pc.v1315, CFSG.KD.Fi24Alpha.Pc.v1316, CFSG.KD.Fi24Alpha.Pc.v1317, CFSG.KD.Fi24Alpha.Pc.v1318, CFSG.KD.Fi24Alpha.Pc.v1319, CFSG.KD.Fi24Alpha.Pc.v1320, CFSG.KD.Fi24Alpha.Pc.v1321, CFSG.KD.Fi24Alpha.Pc.v1322]
theorem CFSG.KD.Fi24Alpha.Pc.p1321 : Nat.beq (runC AR SD 1309 (ckL CFSG.KD.Fi24Alpha.Pc.l1323) 2 1321 CFSG.KD.Fi24Alpha.Pc.l1321) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1323 : Nat := CFSG.KD.Fi24Alpha.KV9 30
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1324 : Nat := CFSG.KD.Fi24Alpha.KV9 31
theorem CFSG.KD.Fi24Alpha.Pc.f91 : Nat.beq (runC AR SD 1309 (finC AR SD (nat_lit 91) 1309 1325) 2 1323 CFSG.KD.Fi24Alpha.Pc.l1323) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk91 : chk (nat_lit 91) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 91) (lo := 1309) (hi := 1325) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1311) CFSG.KD.Fi24Alpha.Pc.p1309 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1313) CFSG.KD.Fi24Alpha.Pc.p1311 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1315) CFSG.KD.Fi24Alpha.Pc.p1313 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1317) CFSG.KD.Fi24Alpha.Pc.p1315 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1319) CFSG.KD.Fi24Alpha.Pc.p1317 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1321) CFSG.KD.Fi24Alpha.Pc.p1319 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1323) CFSG.KD.Fi24Alpha.Pc.p1321 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f91

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1325 : Nat := CFSG.KD.Fi24Alpha.KV9 32
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1326 : Nat := CFSG.KD.Fi24Alpha.KV9 33
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1327 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1325, CFSG.KD.Fi24Alpha.Pc.v1326]
theorem CFSG.KD.Fi24Alpha.Pc.p1325 : Nat.beq (runC AR SD 1325 (ckL CFSG.KD.Fi24Alpha.Pc.l1327) 2 1325 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1327 : Nat := CFSG.KD.Fi24Alpha.KV9 34
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1328 : Nat := CFSG.KD.Fi24Alpha.KV9 35
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1329 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1325, CFSG.KD.Fi24Alpha.Pc.v1326, CFSG.KD.Fi24Alpha.Pc.v1327, CFSG.KD.Fi24Alpha.Pc.v1328]
theorem CFSG.KD.Fi24Alpha.Pc.p1327 : Nat.beq (runC AR SD 1325 (ckL CFSG.KD.Fi24Alpha.Pc.l1329) 2 1327 CFSG.KD.Fi24Alpha.Pc.l1327) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1329 : Nat := CFSG.KD.Fi24Alpha.KV9 36
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1330 : Nat := CFSG.KD.Fi24Alpha.KV9 37
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1331 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1325, CFSG.KD.Fi24Alpha.Pc.v1326, CFSG.KD.Fi24Alpha.Pc.v1327, CFSG.KD.Fi24Alpha.Pc.v1328, CFSG.KD.Fi24Alpha.Pc.v1329, CFSG.KD.Fi24Alpha.Pc.v1330]
theorem CFSG.KD.Fi24Alpha.Pc.p1329 : Nat.beq (runC AR SD 1325 (ckL CFSG.KD.Fi24Alpha.Pc.l1331) 2 1329 CFSG.KD.Fi24Alpha.Pc.l1329) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1331 : Nat := CFSG.KD.Fi24Alpha.KV9 38
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1332 : Nat := CFSG.KD.Fi24Alpha.KV9 39
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1333 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1325, CFSG.KD.Fi24Alpha.Pc.v1326, CFSG.KD.Fi24Alpha.Pc.v1327, CFSG.KD.Fi24Alpha.Pc.v1328, CFSG.KD.Fi24Alpha.Pc.v1329, CFSG.KD.Fi24Alpha.Pc.v1330, CFSG.KD.Fi24Alpha.Pc.v1331, CFSG.KD.Fi24Alpha.Pc.v1332]
theorem CFSG.KD.Fi24Alpha.Pc.p1331 : Nat.beq (runC AR SD 1325 (ckL CFSG.KD.Fi24Alpha.Pc.l1333) 2 1331 CFSG.KD.Fi24Alpha.Pc.l1331) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1333 : Nat := CFSG.KD.Fi24Alpha.KV9 40
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1334 : Nat := CFSG.KD.Fi24Alpha.KV9 41
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1335 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1325, CFSG.KD.Fi24Alpha.Pc.v1326, CFSG.KD.Fi24Alpha.Pc.v1327, CFSG.KD.Fi24Alpha.Pc.v1328, CFSG.KD.Fi24Alpha.Pc.v1329, CFSG.KD.Fi24Alpha.Pc.v1330, CFSG.KD.Fi24Alpha.Pc.v1331, CFSG.KD.Fi24Alpha.Pc.v1332, CFSG.KD.Fi24Alpha.Pc.v1333, CFSG.KD.Fi24Alpha.Pc.v1334]
theorem CFSG.KD.Fi24Alpha.Pc.p1333 : Nat.beq (runC AR SD 1325 (ckL CFSG.KD.Fi24Alpha.Pc.l1335) 2 1333 CFSG.KD.Fi24Alpha.Pc.l1333) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1335 : Nat := CFSG.KD.Fi24Alpha.KV9 42
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1336 : Nat := CFSG.KD.Fi24Alpha.KV9 43
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1337 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1325, CFSG.KD.Fi24Alpha.Pc.v1326, CFSG.KD.Fi24Alpha.Pc.v1327, CFSG.KD.Fi24Alpha.Pc.v1328, CFSG.KD.Fi24Alpha.Pc.v1329, CFSG.KD.Fi24Alpha.Pc.v1330, CFSG.KD.Fi24Alpha.Pc.v1331, CFSG.KD.Fi24Alpha.Pc.v1332, CFSG.KD.Fi24Alpha.Pc.v1333, CFSG.KD.Fi24Alpha.Pc.v1334, CFSG.KD.Fi24Alpha.Pc.v1335, CFSG.KD.Fi24Alpha.Pc.v1336]
theorem CFSG.KD.Fi24Alpha.Pc.p1335 : Nat.beq (runC AR SD 1325 (ckL CFSG.KD.Fi24Alpha.Pc.l1337) 2 1335 CFSG.KD.Fi24Alpha.Pc.l1335) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1337 : Nat := CFSG.KD.Fi24Alpha.KV9 44
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1338 : Nat := CFSG.KD.Fi24Alpha.KV9 45
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1339 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1325, CFSG.KD.Fi24Alpha.Pc.v1326, CFSG.KD.Fi24Alpha.Pc.v1327, CFSG.KD.Fi24Alpha.Pc.v1328, CFSG.KD.Fi24Alpha.Pc.v1329, CFSG.KD.Fi24Alpha.Pc.v1330, CFSG.KD.Fi24Alpha.Pc.v1331, CFSG.KD.Fi24Alpha.Pc.v1332, CFSG.KD.Fi24Alpha.Pc.v1333, CFSG.KD.Fi24Alpha.Pc.v1334, CFSG.KD.Fi24Alpha.Pc.v1335, CFSG.KD.Fi24Alpha.Pc.v1336, CFSG.KD.Fi24Alpha.Pc.v1337, CFSG.KD.Fi24Alpha.Pc.v1338]
theorem CFSG.KD.Fi24Alpha.Pc.p1337 : Nat.beq (runC AR SD 1325 (ckL CFSG.KD.Fi24Alpha.Pc.l1339) 2 1337 CFSG.KD.Fi24Alpha.Pc.l1337) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1339 : Nat := CFSG.KD.Fi24Alpha.KV9 46
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1340 : Nat := CFSG.KD.Fi24Alpha.KV9 47
theorem CFSG.KD.Fi24Alpha.Pc.f92 : Nat.beq (runC AR SD 1325 (finC AR SD (nat_lit 92) 1325 1341) 2 1339 CFSG.KD.Fi24Alpha.Pc.l1339) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk92 : chk (nat_lit 92) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 92) (lo := 1325) (hi := 1341) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1327) CFSG.KD.Fi24Alpha.Pc.p1325 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1329) CFSG.KD.Fi24Alpha.Pc.p1327 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1331) CFSG.KD.Fi24Alpha.Pc.p1329 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1333) CFSG.KD.Fi24Alpha.Pc.p1331 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1335) CFSG.KD.Fi24Alpha.Pc.p1333 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1337) CFSG.KD.Fi24Alpha.Pc.p1335 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1339) CFSG.KD.Fi24Alpha.Pc.p1337 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f92

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1341 : Nat := CFSG.KD.Fi24Alpha.KV9 48
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1342 : Nat := CFSG.KD.Fi24Alpha.KV9 49
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1343 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1341, CFSG.KD.Fi24Alpha.Pc.v1342]
theorem CFSG.KD.Fi24Alpha.Pc.p1341 : Nat.beq (runC AR SD 1341 (ckL CFSG.KD.Fi24Alpha.Pc.l1343) 2 1341 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1343 : Nat := CFSG.KD.Fi24Alpha.KV9 50
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1344 : Nat := CFSG.KD.Fi24Alpha.KV9 51
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1345 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1341, CFSG.KD.Fi24Alpha.Pc.v1342, CFSG.KD.Fi24Alpha.Pc.v1343, CFSG.KD.Fi24Alpha.Pc.v1344]
theorem CFSG.KD.Fi24Alpha.Pc.p1343 : Nat.beq (runC AR SD 1341 (ckL CFSG.KD.Fi24Alpha.Pc.l1345) 2 1343 CFSG.KD.Fi24Alpha.Pc.l1343) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1345 : Nat := CFSG.KD.Fi24Alpha.KV9 52
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1346 : Nat := CFSG.KD.Fi24Alpha.KV9 53
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1347 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1341, CFSG.KD.Fi24Alpha.Pc.v1342, CFSG.KD.Fi24Alpha.Pc.v1343, CFSG.KD.Fi24Alpha.Pc.v1344, CFSG.KD.Fi24Alpha.Pc.v1345, CFSG.KD.Fi24Alpha.Pc.v1346]
theorem CFSG.KD.Fi24Alpha.Pc.p1345 : Nat.beq (runC AR SD 1341 (ckL CFSG.KD.Fi24Alpha.Pc.l1347) 2 1345 CFSG.KD.Fi24Alpha.Pc.l1345) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1347 : Nat := CFSG.KD.Fi24Alpha.KV9 54
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1348 : Nat := CFSG.KD.Fi24Alpha.KV9 55
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1349 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1341, CFSG.KD.Fi24Alpha.Pc.v1342, CFSG.KD.Fi24Alpha.Pc.v1343, CFSG.KD.Fi24Alpha.Pc.v1344, CFSG.KD.Fi24Alpha.Pc.v1345, CFSG.KD.Fi24Alpha.Pc.v1346, CFSG.KD.Fi24Alpha.Pc.v1347, CFSG.KD.Fi24Alpha.Pc.v1348]
theorem CFSG.KD.Fi24Alpha.Pc.p1347 : Nat.beq (runC AR SD 1341 (ckL CFSG.KD.Fi24Alpha.Pc.l1349) 2 1347 CFSG.KD.Fi24Alpha.Pc.l1347) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1349 : Nat := CFSG.KD.Fi24Alpha.KV9 56
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1350 : Nat := CFSG.KD.Fi24Alpha.KV9 57
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1351 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1341, CFSG.KD.Fi24Alpha.Pc.v1342, CFSG.KD.Fi24Alpha.Pc.v1343, CFSG.KD.Fi24Alpha.Pc.v1344, CFSG.KD.Fi24Alpha.Pc.v1345, CFSG.KD.Fi24Alpha.Pc.v1346, CFSG.KD.Fi24Alpha.Pc.v1347, CFSG.KD.Fi24Alpha.Pc.v1348, CFSG.KD.Fi24Alpha.Pc.v1349, CFSG.KD.Fi24Alpha.Pc.v1350]
theorem CFSG.KD.Fi24Alpha.Pc.p1349 : Nat.beq (runC AR SD 1341 (ckL CFSG.KD.Fi24Alpha.Pc.l1351) 2 1349 CFSG.KD.Fi24Alpha.Pc.l1349) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1351 : Nat := CFSG.KD.Fi24Alpha.KV9 58
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1352 : Nat := CFSG.KD.Fi24Alpha.KV9 59
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1353 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1341, CFSG.KD.Fi24Alpha.Pc.v1342, CFSG.KD.Fi24Alpha.Pc.v1343, CFSG.KD.Fi24Alpha.Pc.v1344, CFSG.KD.Fi24Alpha.Pc.v1345, CFSG.KD.Fi24Alpha.Pc.v1346, CFSG.KD.Fi24Alpha.Pc.v1347, CFSG.KD.Fi24Alpha.Pc.v1348, CFSG.KD.Fi24Alpha.Pc.v1349, CFSG.KD.Fi24Alpha.Pc.v1350, CFSG.KD.Fi24Alpha.Pc.v1351, CFSG.KD.Fi24Alpha.Pc.v1352]
theorem CFSG.KD.Fi24Alpha.Pc.p1351 : Nat.beq (runC AR SD 1341 (ckL CFSG.KD.Fi24Alpha.Pc.l1353) 2 1351 CFSG.KD.Fi24Alpha.Pc.l1351) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1353 : Nat := CFSG.KD.Fi24Alpha.KV9 60
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1354 : Nat := CFSG.KD.Fi24Alpha.KV9 61
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1355 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1341, CFSG.KD.Fi24Alpha.Pc.v1342, CFSG.KD.Fi24Alpha.Pc.v1343, CFSG.KD.Fi24Alpha.Pc.v1344, CFSG.KD.Fi24Alpha.Pc.v1345, CFSG.KD.Fi24Alpha.Pc.v1346, CFSG.KD.Fi24Alpha.Pc.v1347, CFSG.KD.Fi24Alpha.Pc.v1348, CFSG.KD.Fi24Alpha.Pc.v1349, CFSG.KD.Fi24Alpha.Pc.v1350, CFSG.KD.Fi24Alpha.Pc.v1351, CFSG.KD.Fi24Alpha.Pc.v1352, CFSG.KD.Fi24Alpha.Pc.v1353, CFSG.KD.Fi24Alpha.Pc.v1354]
theorem CFSG.KD.Fi24Alpha.Pc.p1353 : Nat.beq (runC AR SD 1341 (ckL CFSG.KD.Fi24Alpha.Pc.l1355) 2 1353 CFSG.KD.Fi24Alpha.Pc.l1353) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1355 : Nat := CFSG.KD.Fi24Alpha.KV9 62
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1356 : Nat := CFSG.KD.Fi24Alpha.KV9 63
theorem CFSG.KD.Fi24Alpha.Pc.f93 : Nat.beq (runC AR SD 1341 (finC AR SD (nat_lit 93) 1341 1357) 2 1355 CFSG.KD.Fi24Alpha.Pc.l1355) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk93 : chk (nat_lit 93) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 93) (lo := 1341) (hi := 1357) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1343) CFSG.KD.Fi24Alpha.Pc.p1341 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1345) CFSG.KD.Fi24Alpha.Pc.p1343 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1347) CFSG.KD.Fi24Alpha.Pc.p1345 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1349) CFSG.KD.Fi24Alpha.Pc.p1347 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1351) CFSG.KD.Fi24Alpha.Pc.p1349 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1353) CFSG.KD.Fi24Alpha.Pc.p1351 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1355) CFSG.KD.Fi24Alpha.Pc.p1353 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f93

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1357 : Nat := CFSG.KD.Fi24Alpha.KV9 64
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1358 : Nat := CFSG.KD.Fi24Alpha.KV9 65
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1359 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1357, CFSG.KD.Fi24Alpha.Pc.v1358]
theorem CFSG.KD.Fi24Alpha.Pc.p1357 : Nat.beq (runC AR SD 1357 (ckL CFSG.KD.Fi24Alpha.Pc.l1359) 2 1357 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1359 : Nat := CFSG.KD.Fi24Alpha.KV9 66
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1360 : Nat := CFSG.KD.Fi24Alpha.KV9 67
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1361 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1357, CFSG.KD.Fi24Alpha.Pc.v1358, CFSG.KD.Fi24Alpha.Pc.v1359, CFSG.KD.Fi24Alpha.Pc.v1360]
theorem CFSG.KD.Fi24Alpha.Pc.p1359 : Nat.beq (runC AR SD 1357 (ckL CFSG.KD.Fi24Alpha.Pc.l1361) 2 1359 CFSG.KD.Fi24Alpha.Pc.l1359) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1361 : Nat := CFSG.KD.Fi24Alpha.KV9 68
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1362 : Nat := CFSG.KD.Fi24Alpha.KV9 69
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1363 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1357, CFSG.KD.Fi24Alpha.Pc.v1358, CFSG.KD.Fi24Alpha.Pc.v1359, CFSG.KD.Fi24Alpha.Pc.v1360, CFSG.KD.Fi24Alpha.Pc.v1361, CFSG.KD.Fi24Alpha.Pc.v1362]
theorem CFSG.KD.Fi24Alpha.Pc.p1361 : Nat.beq (runC AR SD 1357 (ckL CFSG.KD.Fi24Alpha.Pc.l1363) 2 1361 CFSG.KD.Fi24Alpha.Pc.l1361) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1363 : Nat := CFSG.KD.Fi24Alpha.KV9 70
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1364 : Nat := CFSG.KD.Fi24Alpha.KV9 71
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1365 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1357, CFSG.KD.Fi24Alpha.Pc.v1358, CFSG.KD.Fi24Alpha.Pc.v1359, CFSG.KD.Fi24Alpha.Pc.v1360, CFSG.KD.Fi24Alpha.Pc.v1361, CFSG.KD.Fi24Alpha.Pc.v1362, CFSG.KD.Fi24Alpha.Pc.v1363, CFSG.KD.Fi24Alpha.Pc.v1364]
theorem CFSG.KD.Fi24Alpha.Pc.p1363 : Nat.beq (runC AR SD 1357 (ckL CFSG.KD.Fi24Alpha.Pc.l1365) 2 1363 CFSG.KD.Fi24Alpha.Pc.l1363) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1365 : Nat := CFSG.KD.Fi24Alpha.KV9 72
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1366 : Nat := CFSG.KD.Fi24Alpha.KV9 73
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1367 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1357, CFSG.KD.Fi24Alpha.Pc.v1358, CFSG.KD.Fi24Alpha.Pc.v1359, CFSG.KD.Fi24Alpha.Pc.v1360, CFSG.KD.Fi24Alpha.Pc.v1361, CFSG.KD.Fi24Alpha.Pc.v1362, CFSG.KD.Fi24Alpha.Pc.v1363, CFSG.KD.Fi24Alpha.Pc.v1364, CFSG.KD.Fi24Alpha.Pc.v1365, CFSG.KD.Fi24Alpha.Pc.v1366]
theorem CFSG.KD.Fi24Alpha.Pc.p1365 : Nat.beq (runC AR SD 1357 (ckL CFSG.KD.Fi24Alpha.Pc.l1367) 2 1365 CFSG.KD.Fi24Alpha.Pc.l1365) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1367 : Nat := CFSG.KD.Fi24Alpha.KV9 74
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1368 : Nat := CFSG.KD.Fi24Alpha.KV9 75
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1369 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1357, CFSG.KD.Fi24Alpha.Pc.v1358, CFSG.KD.Fi24Alpha.Pc.v1359, CFSG.KD.Fi24Alpha.Pc.v1360, CFSG.KD.Fi24Alpha.Pc.v1361, CFSG.KD.Fi24Alpha.Pc.v1362, CFSG.KD.Fi24Alpha.Pc.v1363, CFSG.KD.Fi24Alpha.Pc.v1364, CFSG.KD.Fi24Alpha.Pc.v1365, CFSG.KD.Fi24Alpha.Pc.v1366, CFSG.KD.Fi24Alpha.Pc.v1367, CFSG.KD.Fi24Alpha.Pc.v1368]
theorem CFSG.KD.Fi24Alpha.Pc.p1367 : Nat.beq (runC AR SD 1357 (ckL CFSG.KD.Fi24Alpha.Pc.l1369) 2 1367 CFSG.KD.Fi24Alpha.Pc.l1367) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1369 : Nat := CFSG.KD.Fi24Alpha.KV9 76
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1370 : Nat := CFSG.KD.Fi24Alpha.KV9 77
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1371 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1357, CFSG.KD.Fi24Alpha.Pc.v1358, CFSG.KD.Fi24Alpha.Pc.v1359, CFSG.KD.Fi24Alpha.Pc.v1360, CFSG.KD.Fi24Alpha.Pc.v1361, CFSG.KD.Fi24Alpha.Pc.v1362, CFSG.KD.Fi24Alpha.Pc.v1363, CFSG.KD.Fi24Alpha.Pc.v1364, CFSG.KD.Fi24Alpha.Pc.v1365, CFSG.KD.Fi24Alpha.Pc.v1366, CFSG.KD.Fi24Alpha.Pc.v1367, CFSG.KD.Fi24Alpha.Pc.v1368, CFSG.KD.Fi24Alpha.Pc.v1369, CFSG.KD.Fi24Alpha.Pc.v1370]
theorem CFSG.KD.Fi24Alpha.Pc.p1369 : Nat.beq (runC AR SD 1357 (ckL CFSG.KD.Fi24Alpha.Pc.l1371) 2 1369 CFSG.KD.Fi24Alpha.Pc.l1369) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1371 : Nat := CFSG.KD.Fi24Alpha.KV9 78
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1372 : Nat := CFSG.KD.Fi24Alpha.KV9 79
theorem CFSG.KD.Fi24Alpha.Pc.f94 : Nat.beq (runC AR SD 1357 (finC AR SD (nat_lit 94) 1357 1373) 2 1371 CFSG.KD.Fi24Alpha.Pc.l1371) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk94 : chk (nat_lit 94) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 94) (lo := 1357) (hi := 1373) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1359) CFSG.KD.Fi24Alpha.Pc.p1357 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1361) CFSG.KD.Fi24Alpha.Pc.p1359 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1363) CFSG.KD.Fi24Alpha.Pc.p1361 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1365) CFSG.KD.Fi24Alpha.Pc.p1363 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1367) CFSG.KD.Fi24Alpha.Pc.p1365 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1369) CFSG.KD.Fi24Alpha.Pc.p1367 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1371) CFSG.KD.Fi24Alpha.Pc.p1369 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f94

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1373 : Nat := CFSG.KD.Fi24Alpha.KV9 80
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1374 : Nat := CFSG.KD.Fi24Alpha.KV9 81
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1375 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1373, CFSG.KD.Fi24Alpha.Pc.v1374]
theorem CFSG.KD.Fi24Alpha.Pc.p1373 : Nat.beq (runC AR SD 1373 (ckL CFSG.KD.Fi24Alpha.Pc.l1375) 2 1373 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1375 : Nat := CFSG.KD.Fi24Alpha.KV9 82
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1376 : Nat := CFSG.KD.Fi24Alpha.KV9 83
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1377 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1373, CFSG.KD.Fi24Alpha.Pc.v1374, CFSG.KD.Fi24Alpha.Pc.v1375, CFSG.KD.Fi24Alpha.Pc.v1376]
theorem CFSG.KD.Fi24Alpha.Pc.p1375 : Nat.beq (runC AR SD 1373 (ckL CFSG.KD.Fi24Alpha.Pc.l1377) 2 1375 CFSG.KD.Fi24Alpha.Pc.l1375) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1377 : Nat := CFSG.KD.Fi24Alpha.KV9 84
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1378 : Nat := CFSG.KD.Fi24Alpha.KV9 85
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1379 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1373, CFSG.KD.Fi24Alpha.Pc.v1374, CFSG.KD.Fi24Alpha.Pc.v1375, CFSG.KD.Fi24Alpha.Pc.v1376, CFSG.KD.Fi24Alpha.Pc.v1377, CFSG.KD.Fi24Alpha.Pc.v1378]
theorem CFSG.KD.Fi24Alpha.Pc.p1377 : Nat.beq (runC AR SD 1373 (ckL CFSG.KD.Fi24Alpha.Pc.l1379) 2 1377 CFSG.KD.Fi24Alpha.Pc.l1377) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1379 : Nat := CFSG.KD.Fi24Alpha.KV9 86
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1380 : Nat := CFSG.KD.Fi24Alpha.KV9 87
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1381 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1373, CFSG.KD.Fi24Alpha.Pc.v1374, CFSG.KD.Fi24Alpha.Pc.v1375, CFSG.KD.Fi24Alpha.Pc.v1376, CFSG.KD.Fi24Alpha.Pc.v1377, CFSG.KD.Fi24Alpha.Pc.v1378, CFSG.KD.Fi24Alpha.Pc.v1379, CFSG.KD.Fi24Alpha.Pc.v1380]
theorem CFSG.KD.Fi24Alpha.Pc.p1379 : Nat.beq (runC AR SD 1373 (ckL CFSG.KD.Fi24Alpha.Pc.l1381) 2 1379 CFSG.KD.Fi24Alpha.Pc.l1379) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1381 : Nat := CFSG.KD.Fi24Alpha.KV9 88
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1382 : Nat := CFSG.KD.Fi24Alpha.KV9 89
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1383 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1373, CFSG.KD.Fi24Alpha.Pc.v1374, CFSG.KD.Fi24Alpha.Pc.v1375, CFSG.KD.Fi24Alpha.Pc.v1376, CFSG.KD.Fi24Alpha.Pc.v1377, CFSG.KD.Fi24Alpha.Pc.v1378, CFSG.KD.Fi24Alpha.Pc.v1379, CFSG.KD.Fi24Alpha.Pc.v1380, CFSG.KD.Fi24Alpha.Pc.v1381, CFSG.KD.Fi24Alpha.Pc.v1382]
theorem CFSG.KD.Fi24Alpha.Pc.p1381 : Nat.beq (runC AR SD 1373 (ckL CFSG.KD.Fi24Alpha.Pc.l1383) 2 1381 CFSG.KD.Fi24Alpha.Pc.l1381) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1383 : Nat := CFSG.KD.Fi24Alpha.KV9 90
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1384 : Nat := CFSG.KD.Fi24Alpha.KV9 91
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1385 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1373, CFSG.KD.Fi24Alpha.Pc.v1374, CFSG.KD.Fi24Alpha.Pc.v1375, CFSG.KD.Fi24Alpha.Pc.v1376, CFSG.KD.Fi24Alpha.Pc.v1377, CFSG.KD.Fi24Alpha.Pc.v1378, CFSG.KD.Fi24Alpha.Pc.v1379, CFSG.KD.Fi24Alpha.Pc.v1380, CFSG.KD.Fi24Alpha.Pc.v1381, CFSG.KD.Fi24Alpha.Pc.v1382, CFSG.KD.Fi24Alpha.Pc.v1383, CFSG.KD.Fi24Alpha.Pc.v1384]
theorem CFSG.KD.Fi24Alpha.Pc.p1383 : Nat.beq (runC AR SD 1373 (ckL CFSG.KD.Fi24Alpha.Pc.l1385) 2 1383 CFSG.KD.Fi24Alpha.Pc.l1383) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1385 : Nat := CFSG.KD.Fi24Alpha.KV9 92
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1386 : Nat := CFSG.KD.Fi24Alpha.KV9 93
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1387 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1373, CFSG.KD.Fi24Alpha.Pc.v1374, CFSG.KD.Fi24Alpha.Pc.v1375, CFSG.KD.Fi24Alpha.Pc.v1376, CFSG.KD.Fi24Alpha.Pc.v1377, CFSG.KD.Fi24Alpha.Pc.v1378, CFSG.KD.Fi24Alpha.Pc.v1379, CFSG.KD.Fi24Alpha.Pc.v1380, CFSG.KD.Fi24Alpha.Pc.v1381, CFSG.KD.Fi24Alpha.Pc.v1382, CFSG.KD.Fi24Alpha.Pc.v1383, CFSG.KD.Fi24Alpha.Pc.v1384, CFSG.KD.Fi24Alpha.Pc.v1385, CFSG.KD.Fi24Alpha.Pc.v1386]
theorem CFSG.KD.Fi24Alpha.Pc.p1385 : Nat.beq (runC AR SD 1373 (ckL CFSG.KD.Fi24Alpha.Pc.l1387) 2 1385 CFSG.KD.Fi24Alpha.Pc.l1385) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1387 : Nat := CFSG.KD.Fi24Alpha.KV9 94
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1388 : Nat := CFSG.KD.Fi24Alpha.KV9 95
theorem CFSG.KD.Fi24Alpha.Pc.f95 : Nat.beq (runC AR SD 1373 (finC AR SD (nat_lit 95) 1373 1389) 2 1387 CFSG.KD.Fi24Alpha.Pc.l1387) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk95 : chk (nat_lit 95) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 95) (lo := 1373) (hi := 1389) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1375) CFSG.KD.Fi24Alpha.Pc.p1373 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1377) CFSG.KD.Fi24Alpha.Pc.p1375 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1379) CFSG.KD.Fi24Alpha.Pc.p1377 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1381) CFSG.KD.Fi24Alpha.Pc.p1379 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1383) CFSG.KD.Fi24Alpha.Pc.p1381 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1385) CFSG.KD.Fi24Alpha.Pc.p1383 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1387) CFSG.KD.Fi24Alpha.Pc.p1385 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f95

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1389 : Nat := CFSG.KD.Fi24Alpha.KV9 96
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1390 : Nat := CFSG.KD.Fi24Alpha.KV9 97
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1391 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1389, CFSG.KD.Fi24Alpha.Pc.v1390]
theorem CFSG.KD.Fi24Alpha.Pc.p1389 : Nat.beq (runC AR SD 1389 (ckL CFSG.KD.Fi24Alpha.Pc.l1391) 2 1389 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1391 : Nat := CFSG.KD.Fi24Alpha.KV9 98
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1392 : Nat := CFSG.KD.Fi24Alpha.KV9 99
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1393 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1389, CFSG.KD.Fi24Alpha.Pc.v1390, CFSG.KD.Fi24Alpha.Pc.v1391, CFSG.KD.Fi24Alpha.Pc.v1392]
theorem CFSG.KD.Fi24Alpha.Pc.p1391 : Nat.beq (runC AR SD 1389 (ckL CFSG.KD.Fi24Alpha.Pc.l1393) 2 1391 CFSG.KD.Fi24Alpha.Pc.l1391) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1393 : Nat := CFSG.KD.Fi24Alpha.KV9 100
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1394 : Nat := CFSG.KD.Fi24Alpha.KV9 101
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1395 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1389, CFSG.KD.Fi24Alpha.Pc.v1390, CFSG.KD.Fi24Alpha.Pc.v1391, CFSG.KD.Fi24Alpha.Pc.v1392, CFSG.KD.Fi24Alpha.Pc.v1393, CFSG.KD.Fi24Alpha.Pc.v1394]
theorem CFSG.KD.Fi24Alpha.Pc.p1393 : Nat.beq (runC AR SD 1389 (ckL CFSG.KD.Fi24Alpha.Pc.l1395) 2 1393 CFSG.KD.Fi24Alpha.Pc.l1393) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1395 : Nat := CFSG.KD.Fi24Alpha.KV9 102
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1396 : Nat := CFSG.KD.Fi24Alpha.KV9 103
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1397 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1389, CFSG.KD.Fi24Alpha.Pc.v1390, CFSG.KD.Fi24Alpha.Pc.v1391, CFSG.KD.Fi24Alpha.Pc.v1392, CFSG.KD.Fi24Alpha.Pc.v1393, CFSG.KD.Fi24Alpha.Pc.v1394, CFSG.KD.Fi24Alpha.Pc.v1395, CFSG.KD.Fi24Alpha.Pc.v1396]
theorem CFSG.KD.Fi24Alpha.Pc.p1395 : Nat.beq (runC AR SD 1389 (ckL CFSG.KD.Fi24Alpha.Pc.l1397) 2 1395 CFSG.KD.Fi24Alpha.Pc.l1395) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1397 : Nat := CFSG.KD.Fi24Alpha.KV9 104
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1398 : Nat := CFSG.KD.Fi24Alpha.KV9 105
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1399 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1389, CFSG.KD.Fi24Alpha.Pc.v1390, CFSG.KD.Fi24Alpha.Pc.v1391, CFSG.KD.Fi24Alpha.Pc.v1392, CFSG.KD.Fi24Alpha.Pc.v1393, CFSG.KD.Fi24Alpha.Pc.v1394, CFSG.KD.Fi24Alpha.Pc.v1395, CFSG.KD.Fi24Alpha.Pc.v1396, CFSG.KD.Fi24Alpha.Pc.v1397, CFSG.KD.Fi24Alpha.Pc.v1398]
theorem CFSG.KD.Fi24Alpha.Pc.p1397 : Nat.beq (runC AR SD 1389 (ckL CFSG.KD.Fi24Alpha.Pc.l1399) 2 1397 CFSG.KD.Fi24Alpha.Pc.l1397) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1399 : Nat := CFSG.KD.Fi24Alpha.KV9 106
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1400 : Nat := CFSG.KD.Fi24Alpha.KV9 107
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1401 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1389, CFSG.KD.Fi24Alpha.Pc.v1390, CFSG.KD.Fi24Alpha.Pc.v1391, CFSG.KD.Fi24Alpha.Pc.v1392, CFSG.KD.Fi24Alpha.Pc.v1393, CFSG.KD.Fi24Alpha.Pc.v1394, CFSG.KD.Fi24Alpha.Pc.v1395, CFSG.KD.Fi24Alpha.Pc.v1396, CFSG.KD.Fi24Alpha.Pc.v1397, CFSG.KD.Fi24Alpha.Pc.v1398, CFSG.KD.Fi24Alpha.Pc.v1399, CFSG.KD.Fi24Alpha.Pc.v1400]
theorem CFSG.KD.Fi24Alpha.Pc.p1399 : Nat.beq (runC AR SD 1389 (ckL CFSG.KD.Fi24Alpha.Pc.l1401) 2 1399 CFSG.KD.Fi24Alpha.Pc.l1399) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1401 : Nat := CFSG.KD.Fi24Alpha.KV9 108
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1402 : Nat := CFSG.KD.Fi24Alpha.KV9 109
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1403 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1389, CFSG.KD.Fi24Alpha.Pc.v1390, CFSG.KD.Fi24Alpha.Pc.v1391, CFSG.KD.Fi24Alpha.Pc.v1392, CFSG.KD.Fi24Alpha.Pc.v1393, CFSG.KD.Fi24Alpha.Pc.v1394, CFSG.KD.Fi24Alpha.Pc.v1395, CFSG.KD.Fi24Alpha.Pc.v1396, CFSG.KD.Fi24Alpha.Pc.v1397, CFSG.KD.Fi24Alpha.Pc.v1398, CFSG.KD.Fi24Alpha.Pc.v1399, CFSG.KD.Fi24Alpha.Pc.v1400, CFSG.KD.Fi24Alpha.Pc.v1401, CFSG.KD.Fi24Alpha.Pc.v1402]
theorem CFSG.KD.Fi24Alpha.Pc.p1401 : Nat.beq (runC AR SD 1389 (ckL CFSG.KD.Fi24Alpha.Pc.l1403) 2 1401 CFSG.KD.Fi24Alpha.Pc.l1401) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1403 : Nat := CFSG.KD.Fi24Alpha.KV9 110
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1404 : Nat := CFSG.KD.Fi24Alpha.KV9 111
theorem CFSG.KD.Fi24Alpha.Pc.f96 : Nat.beq (runC AR SD 1389 (finC AR SD (nat_lit 96) 1389 1405) 2 1403 CFSG.KD.Fi24Alpha.Pc.l1403) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk96 : chk (nat_lit 96) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 96) (lo := 1389) (hi := 1405) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1391) CFSG.KD.Fi24Alpha.Pc.p1389 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1393) CFSG.KD.Fi24Alpha.Pc.p1391 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1395) CFSG.KD.Fi24Alpha.Pc.p1393 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1397) CFSG.KD.Fi24Alpha.Pc.p1395 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1399) CFSG.KD.Fi24Alpha.Pc.p1397 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1401) CFSG.KD.Fi24Alpha.Pc.p1399 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1403) CFSG.KD.Fi24Alpha.Pc.p1401 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f96

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1405 : Nat := CFSG.KD.Fi24Alpha.KV9 112
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1406 : Nat := CFSG.KD.Fi24Alpha.KV9 113
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1407 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1405, CFSG.KD.Fi24Alpha.Pc.v1406]
theorem CFSG.KD.Fi24Alpha.Pc.p1405 : Nat.beq (runC AR SD 1405 (ckL CFSG.KD.Fi24Alpha.Pc.l1407) 2 1405 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1407 : Nat := CFSG.KD.Fi24Alpha.KV9 114
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1408 : Nat := CFSG.KD.Fi24Alpha.KV9 115
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1409 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1405, CFSG.KD.Fi24Alpha.Pc.v1406, CFSG.KD.Fi24Alpha.Pc.v1407, CFSG.KD.Fi24Alpha.Pc.v1408]
theorem CFSG.KD.Fi24Alpha.Pc.p1407 : Nat.beq (runC AR SD 1405 (ckL CFSG.KD.Fi24Alpha.Pc.l1409) 2 1407 CFSG.KD.Fi24Alpha.Pc.l1407) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1409 : Nat := CFSG.KD.Fi24Alpha.KV9 116
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1410 : Nat := CFSG.KD.Fi24Alpha.KV9 117
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1411 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1405, CFSG.KD.Fi24Alpha.Pc.v1406, CFSG.KD.Fi24Alpha.Pc.v1407, CFSG.KD.Fi24Alpha.Pc.v1408, CFSG.KD.Fi24Alpha.Pc.v1409, CFSG.KD.Fi24Alpha.Pc.v1410]
theorem CFSG.KD.Fi24Alpha.Pc.p1409 : Nat.beq (runC AR SD 1405 (ckL CFSG.KD.Fi24Alpha.Pc.l1411) 2 1409 CFSG.KD.Fi24Alpha.Pc.l1409) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1411 : Nat := CFSG.KD.Fi24Alpha.KV9 118
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1412 : Nat := CFSG.KD.Fi24Alpha.KV9 119
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1413 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1405, CFSG.KD.Fi24Alpha.Pc.v1406, CFSG.KD.Fi24Alpha.Pc.v1407, CFSG.KD.Fi24Alpha.Pc.v1408, CFSG.KD.Fi24Alpha.Pc.v1409, CFSG.KD.Fi24Alpha.Pc.v1410, CFSG.KD.Fi24Alpha.Pc.v1411, CFSG.KD.Fi24Alpha.Pc.v1412]
theorem CFSG.KD.Fi24Alpha.Pc.p1411 : Nat.beq (runC AR SD 1405 (ckL CFSG.KD.Fi24Alpha.Pc.l1413) 2 1411 CFSG.KD.Fi24Alpha.Pc.l1411) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1413 : Nat := CFSG.KD.Fi24Alpha.KV9 120
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1414 : Nat := CFSG.KD.Fi24Alpha.KV9 121
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1415 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1405, CFSG.KD.Fi24Alpha.Pc.v1406, CFSG.KD.Fi24Alpha.Pc.v1407, CFSG.KD.Fi24Alpha.Pc.v1408, CFSG.KD.Fi24Alpha.Pc.v1409, CFSG.KD.Fi24Alpha.Pc.v1410, CFSG.KD.Fi24Alpha.Pc.v1411, CFSG.KD.Fi24Alpha.Pc.v1412, CFSG.KD.Fi24Alpha.Pc.v1413, CFSG.KD.Fi24Alpha.Pc.v1414]
theorem CFSG.KD.Fi24Alpha.Pc.p1413 : Nat.beq (runC AR SD 1405 (ckL CFSG.KD.Fi24Alpha.Pc.l1415) 2 1413 CFSG.KD.Fi24Alpha.Pc.l1413) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1415 : Nat := CFSG.KD.Fi24Alpha.KV9 122
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1416 : Nat := CFSG.KD.Fi24Alpha.KV9 123
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1417 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1405, CFSG.KD.Fi24Alpha.Pc.v1406, CFSG.KD.Fi24Alpha.Pc.v1407, CFSG.KD.Fi24Alpha.Pc.v1408, CFSG.KD.Fi24Alpha.Pc.v1409, CFSG.KD.Fi24Alpha.Pc.v1410, CFSG.KD.Fi24Alpha.Pc.v1411, CFSG.KD.Fi24Alpha.Pc.v1412, CFSG.KD.Fi24Alpha.Pc.v1413, CFSG.KD.Fi24Alpha.Pc.v1414, CFSG.KD.Fi24Alpha.Pc.v1415, CFSG.KD.Fi24Alpha.Pc.v1416]
theorem CFSG.KD.Fi24Alpha.Pc.p1415 : Nat.beq (runC AR SD 1405 (ckL CFSG.KD.Fi24Alpha.Pc.l1417) 2 1415 CFSG.KD.Fi24Alpha.Pc.l1415) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1417 : Nat := CFSG.KD.Fi24Alpha.KV9 124
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1418 : Nat := CFSG.KD.Fi24Alpha.KV9 125
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1419 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1405, CFSG.KD.Fi24Alpha.Pc.v1406, CFSG.KD.Fi24Alpha.Pc.v1407, CFSG.KD.Fi24Alpha.Pc.v1408, CFSG.KD.Fi24Alpha.Pc.v1409, CFSG.KD.Fi24Alpha.Pc.v1410, CFSG.KD.Fi24Alpha.Pc.v1411, CFSG.KD.Fi24Alpha.Pc.v1412, CFSG.KD.Fi24Alpha.Pc.v1413, CFSG.KD.Fi24Alpha.Pc.v1414, CFSG.KD.Fi24Alpha.Pc.v1415, CFSG.KD.Fi24Alpha.Pc.v1416, CFSG.KD.Fi24Alpha.Pc.v1417, CFSG.KD.Fi24Alpha.Pc.v1418]
theorem CFSG.KD.Fi24Alpha.Pc.p1417 : Nat.beq (runC AR SD 1405 (ckL CFSG.KD.Fi24Alpha.Pc.l1419) 2 1417 CFSG.KD.Fi24Alpha.Pc.l1417) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1419 : Nat := CFSG.KD.Fi24Alpha.KV9 126
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1420 : Nat := CFSG.KD.Fi24Alpha.KV9 127
theorem CFSG.KD.Fi24Alpha.Pc.f97 : Nat.beq (runC AR SD 1405 (finC AR SD (nat_lit 97) 1405 1421) 2 1419 CFSG.KD.Fi24Alpha.Pc.l1419) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk97 : chk (nat_lit 97) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 97) (lo := 1405) (hi := 1421) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1407) CFSG.KD.Fi24Alpha.Pc.p1405 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1409) CFSG.KD.Fi24Alpha.Pc.p1407 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1411) CFSG.KD.Fi24Alpha.Pc.p1409 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1413) CFSG.KD.Fi24Alpha.Pc.p1411 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1415) CFSG.KD.Fi24Alpha.Pc.p1413 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1417) CFSG.KD.Fi24Alpha.Pc.p1415 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1419) CFSG.KD.Fi24Alpha.Pc.p1417 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f97

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1421 : Nat := CFSG.KD.Fi24Alpha.KV9 128
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1422 : Nat := CFSG.KD.Fi24Alpha.KV9 129
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1423 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1421, CFSG.KD.Fi24Alpha.Pc.v1422]
theorem CFSG.KD.Fi24Alpha.Pc.p1421 : Nat.beq (runC AR SD 1421 (ckL CFSG.KD.Fi24Alpha.Pc.l1423) 2 1421 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1423 : Nat := CFSG.KD.Fi24Alpha.KV9 130
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1424 : Nat := CFSG.KD.Fi24Alpha.KV9 131
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1425 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1421, CFSG.KD.Fi24Alpha.Pc.v1422, CFSG.KD.Fi24Alpha.Pc.v1423, CFSG.KD.Fi24Alpha.Pc.v1424]
theorem CFSG.KD.Fi24Alpha.Pc.p1423 : Nat.beq (runC AR SD 1421 (ckL CFSG.KD.Fi24Alpha.Pc.l1425) 2 1423 CFSG.KD.Fi24Alpha.Pc.l1423) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1425 : Nat := CFSG.KD.Fi24Alpha.KV9 132
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1426 : Nat := CFSG.KD.Fi24Alpha.KV9 133
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1427 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1421, CFSG.KD.Fi24Alpha.Pc.v1422, CFSG.KD.Fi24Alpha.Pc.v1423, CFSG.KD.Fi24Alpha.Pc.v1424, CFSG.KD.Fi24Alpha.Pc.v1425, CFSG.KD.Fi24Alpha.Pc.v1426]
theorem CFSG.KD.Fi24Alpha.Pc.p1425 : Nat.beq (runC AR SD 1421 (ckL CFSG.KD.Fi24Alpha.Pc.l1427) 2 1425 CFSG.KD.Fi24Alpha.Pc.l1425) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1427 : Nat := CFSG.KD.Fi24Alpha.KV9 134
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1428 : Nat := CFSG.KD.Fi24Alpha.KV9 135
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1429 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1421, CFSG.KD.Fi24Alpha.Pc.v1422, CFSG.KD.Fi24Alpha.Pc.v1423, CFSG.KD.Fi24Alpha.Pc.v1424, CFSG.KD.Fi24Alpha.Pc.v1425, CFSG.KD.Fi24Alpha.Pc.v1426, CFSG.KD.Fi24Alpha.Pc.v1427, CFSG.KD.Fi24Alpha.Pc.v1428]
theorem CFSG.KD.Fi24Alpha.Pc.p1427 : Nat.beq (runC AR SD 1421 (ckL CFSG.KD.Fi24Alpha.Pc.l1429) 2 1427 CFSG.KD.Fi24Alpha.Pc.l1427) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1429 : Nat := CFSG.KD.Fi24Alpha.KV9 136
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1430 : Nat := CFSG.KD.Fi24Alpha.KV9 137
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1431 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1421, CFSG.KD.Fi24Alpha.Pc.v1422, CFSG.KD.Fi24Alpha.Pc.v1423, CFSG.KD.Fi24Alpha.Pc.v1424, CFSG.KD.Fi24Alpha.Pc.v1425, CFSG.KD.Fi24Alpha.Pc.v1426, CFSG.KD.Fi24Alpha.Pc.v1427, CFSG.KD.Fi24Alpha.Pc.v1428, CFSG.KD.Fi24Alpha.Pc.v1429, CFSG.KD.Fi24Alpha.Pc.v1430]
theorem CFSG.KD.Fi24Alpha.Pc.p1429 : Nat.beq (runC AR SD 1421 (ckL CFSG.KD.Fi24Alpha.Pc.l1431) 2 1429 CFSG.KD.Fi24Alpha.Pc.l1429) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1431 : Nat := CFSG.KD.Fi24Alpha.KV9 138
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1432 : Nat := CFSG.KD.Fi24Alpha.KV9 139
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1433 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1421, CFSG.KD.Fi24Alpha.Pc.v1422, CFSG.KD.Fi24Alpha.Pc.v1423, CFSG.KD.Fi24Alpha.Pc.v1424, CFSG.KD.Fi24Alpha.Pc.v1425, CFSG.KD.Fi24Alpha.Pc.v1426, CFSG.KD.Fi24Alpha.Pc.v1427, CFSG.KD.Fi24Alpha.Pc.v1428, CFSG.KD.Fi24Alpha.Pc.v1429, CFSG.KD.Fi24Alpha.Pc.v1430, CFSG.KD.Fi24Alpha.Pc.v1431, CFSG.KD.Fi24Alpha.Pc.v1432]
theorem CFSG.KD.Fi24Alpha.Pc.p1431 : Nat.beq (runC AR SD 1421 (ckL CFSG.KD.Fi24Alpha.Pc.l1433) 2 1431 CFSG.KD.Fi24Alpha.Pc.l1431) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1433 : Nat := CFSG.KD.Fi24Alpha.KV9 140
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1434 : Nat := CFSG.KD.Fi24Alpha.KV9 141
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1435 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1421, CFSG.KD.Fi24Alpha.Pc.v1422, CFSG.KD.Fi24Alpha.Pc.v1423, CFSG.KD.Fi24Alpha.Pc.v1424, CFSG.KD.Fi24Alpha.Pc.v1425, CFSG.KD.Fi24Alpha.Pc.v1426, CFSG.KD.Fi24Alpha.Pc.v1427, CFSG.KD.Fi24Alpha.Pc.v1428, CFSG.KD.Fi24Alpha.Pc.v1429, CFSG.KD.Fi24Alpha.Pc.v1430, CFSG.KD.Fi24Alpha.Pc.v1431, CFSG.KD.Fi24Alpha.Pc.v1432, CFSG.KD.Fi24Alpha.Pc.v1433, CFSG.KD.Fi24Alpha.Pc.v1434]
theorem CFSG.KD.Fi24Alpha.Pc.p1433 : Nat.beq (runC AR SD 1421 (ckL CFSG.KD.Fi24Alpha.Pc.l1435) 2 1433 CFSG.KD.Fi24Alpha.Pc.l1433) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1435 : Nat := CFSG.KD.Fi24Alpha.KV9 142
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1436 : Nat := CFSG.KD.Fi24Alpha.KV9 143
theorem CFSG.KD.Fi24Alpha.Pc.f98 : Nat.beq (runC AR SD 1421 (finC AR SD (nat_lit 98) 1421 1437) 2 1435 CFSG.KD.Fi24Alpha.Pc.l1435) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk98 : chk (nat_lit 98) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 98) (lo := 1421) (hi := 1437) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1423) CFSG.KD.Fi24Alpha.Pc.p1421 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1425) CFSG.KD.Fi24Alpha.Pc.p1423 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1427) CFSG.KD.Fi24Alpha.Pc.p1425 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1429) CFSG.KD.Fi24Alpha.Pc.p1427 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1431) CFSG.KD.Fi24Alpha.Pc.p1429 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1433) CFSG.KD.Fi24Alpha.Pc.p1431 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1435) CFSG.KD.Fi24Alpha.Pc.p1433 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f98

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1437 : Nat := CFSG.KD.Fi24Alpha.KV9 144
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1438 : Nat := CFSG.KD.Fi24Alpha.KV9 145
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1439 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1437, CFSG.KD.Fi24Alpha.Pc.v1438]
theorem CFSG.KD.Fi24Alpha.Pc.p1437 : Nat.beq (runC AR SD 1437 (ckL CFSG.KD.Fi24Alpha.Pc.l1439) 2 1437 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1439 : Nat := CFSG.KD.Fi24Alpha.KV9 146
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1440 : Nat := CFSG.KD.Fi24Alpha.KV9 147
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1441 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1437, CFSG.KD.Fi24Alpha.Pc.v1438, CFSG.KD.Fi24Alpha.Pc.v1439, CFSG.KD.Fi24Alpha.Pc.v1440]
theorem CFSG.KD.Fi24Alpha.Pc.p1439 : Nat.beq (runC AR SD 1437 (ckL CFSG.KD.Fi24Alpha.Pc.l1441) 2 1439 CFSG.KD.Fi24Alpha.Pc.l1439) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1441 : Nat := CFSG.KD.Fi24Alpha.KV9 148
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1442 : Nat := CFSG.KD.Fi24Alpha.KV9 149
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1443 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1437, CFSG.KD.Fi24Alpha.Pc.v1438, CFSG.KD.Fi24Alpha.Pc.v1439, CFSG.KD.Fi24Alpha.Pc.v1440, CFSG.KD.Fi24Alpha.Pc.v1441, CFSG.KD.Fi24Alpha.Pc.v1442]
theorem CFSG.KD.Fi24Alpha.Pc.p1441 : Nat.beq (runC AR SD 1437 (ckL CFSG.KD.Fi24Alpha.Pc.l1443) 2 1441 CFSG.KD.Fi24Alpha.Pc.l1441) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1443 : Nat := CFSG.KD.Fi24Alpha.KV9 150
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1444 : Nat := CFSG.KD.Fi24Alpha.KV9 151
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1445 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1437, CFSG.KD.Fi24Alpha.Pc.v1438, CFSG.KD.Fi24Alpha.Pc.v1439, CFSG.KD.Fi24Alpha.Pc.v1440, CFSG.KD.Fi24Alpha.Pc.v1441, CFSG.KD.Fi24Alpha.Pc.v1442, CFSG.KD.Fi24Alpha.Pc.v1443, CFSG.KD.Fi24Alpha.Pc.v1444]
theorem CFSG.KD.Fi24Alpha.Pc.p1443 : Nat.beq (runC AR SD 1437 (ckL CFSG.KD.Fi24Alpha.Pc.l1445) 2 1443 CFSG.KD.Fi24Alpha.Pc.l1443) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1445 : Nat := CFSG.KD.Fi24Alpha.KV9 152
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1446 : Nat := CFSG.KD.Fi24Alpha.KV9 153
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1447 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1437, CFSG.KD.Fi24Alpha.Pc.v1438, CFSG.KD.Fi24Alpha.Pc.v1439, CFSG.KD.Fi24Alpha.Pc.v1440, CFSG.KD.Fi24Alpha.Pc.v1441, CFSG.KD.Fi24Alpha.Pc.v1442, CFSG.KD.Fi24Alpha.Pc.v1443, CFSG.KD.Fi24Alpha.Pc.v1444, CFSG.KD.Fi24Alpha.Pc.v1445, CFSG.KD.Fi24Alpha.Pc.v1446]
theorem CFSG.KD.Fi24Alpha.Pc.p1445 : Nat.beq (runC AR SD 1437 (ckL CFSG.KD.Fi24Alpha.Pc.l1447) 2 1445 CFSG.KD.Fi24Alpha.Pc.l1445) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1447 : Nat := CFSG.KD.Fi24Alpha.KV9 154
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1448 : Nat := CFSG.KD.Fi24Alpha.KV9 155
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1449 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1437, CFSG.KD.Fi24Alpha.Pc.v1438, CFSG.KD.Fi24Alpha.Pc.v1439, CFSG.KD.Fi24Alpha.Pc.v1440, CFSG.KD.Fi24Alpha.Pc.v1441, CFSG.KD.Fi24Alpha.Pc.v1442, CFSG.KD.Fi24Alpha.Pc.v1443, CFSG.KD.Fi24Alpha.Pc.v1444, CFSG.KD.Fi24Alpha.Pc.v1445, CFSG.KD.Fi24Alpha.Pc.v1446, CFSG.KD.Fi24Alpha.Pc.v1447, CFSG.KD.Fi24Alpha.Pc.v1448]
theorem CFSG.KD.Fi24Alpha.Pc.p1447 : Nat.beq (runC AR SD 1437 (ckL CFSG.KD.Fi24Alpha.Pc.l1449) 2 1447 CFSG.KD.Fi24Alpha.Pc.l1447) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1449 : Nat := CFSG.KD.Fi24Alpha.KV9 156
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1450 : Nat := CFSG.KD.Fi24Alpha.KV9 157
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1451 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1437, CFSG.KD.Fi24Alpha.Pc.v1438, CFSG.KD.Fi24Alpha.Pc.v1439, CFSG.KD.Fi24Alpha.Pc.v1440, CFSG.KD.Fi24Alpha.Pc.v1441, CFSG.KD.Fi24Alpha.Pc.v1442, CFSG.KD.Fi24Alpha.Pc.v1443, CFSG.KD.Fi24Alpha.Pc.v1444, CFSG.KD.Fi24Alpha.Pc.v1445, CFSG.KD.Fi24Alpha.Pc.v1446, CFSG.KD.Fi24Alpha.Pc.v1447, CFSG.KD.Fi24Alpha.Pc.v1448, CFSG.KD.Fi24Alpha.Pc.v1449, CFSG.KD.Fi24Alpha.Pc.v1450]
theorem CFSG.KD.Fi24Alpha.Pc.p1449 : Nat.beq (runC AR SD 1437 (ckL CFSG.KD.Fi24Alpha.Pc.l1451) 2 1449 CFSG.KD.Fi24Alpha.Pc.l1449) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1451 : Nat := CFSG.KD.Fi24Alpha.KV9 158
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1452 : Nat := CFSG.KD.Fi24Alpha.KV9 159
theorem CFSG.KD.Fi24Alpha.Pc.f99 : Nat.beq (runC AR SD 1437 (finC AR SD (nat_lit 99) 1437 1453) 2 1451 CFSG.KD.Fi24Alpha.Pc.l1451) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk99 : chk (nat_lit 99) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 99) (lo := 1437) (hi := 1453) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1439) CFSG.KD.Fi24Alpha.Pc.p1437 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1441) CFSG.KD.Fi24Alpha.Pc.p1439 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1443) CFSG.KD.Fi24Alpha.Pc.p1441 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1445) CFSG.KD.Fi24Alpha.Pc.p1443 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1447) CFSG.KD.Fi24Alpha.Pc.p1445 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1449) CFSG.KD.Fi24Alpha.Pc.p1447 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1451) CFSG.KD.Fi24Alpha.Pc.p1449 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f99

end
