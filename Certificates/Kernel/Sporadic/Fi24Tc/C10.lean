module

public import Certificates.Kernel.Sporadic.Fi24Tc.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Tc KV10 "Certificates/Kernel/Sporadic/Fi24Tc/data/v10.bin" 152491 4 16469028 15116636866573483405

public section

open CFSG.KD.Fi24Tc CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1396 : Nat := CFSG.KD.Fi24Tc.KV10 0
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1397 : Nat := CFSG.KD.Fi24Tc.KV10 1
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1398 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1396, CFSG.KD.Fi24Tc.Pc.v1397]
theorem CFSG.KD.Fi24Tc.Pc.p1396 : Nat.beq (runC AR SD 1396 (ckL CFSG.KD.Fi24Tc.Pc.l1398) 2 1396 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1398 : Nat := CFSG.KD.Fi24Tc.KV10 2
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1399 : Nat := CFSG.KD.Fi24Tc.KV10 3
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1400 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1396, CFSG.KD.Fi24Tc.Pc.v1397, CFSG.KD.Fi24Tc.Pc.v1398, CFSG.KD.Fi24Tc.Pc.v1399]
theorem CFSG.KD.Fi24Tc.Pc.p1398 : Nat.beq (runC AR SD 1396 (ckL CFSG.KD.Fi24Tc.Pc.l1400) 2 1398 CFSG.KD.Fi24Tc.Pc.l1398) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1400 : Nat := CFSG.KD.Fi24Tc.KV10 4
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1401 : Nat := CFSG.KD.Fi24Tc.KV10 5
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1402 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1396, CFSG.KD.Fi24Tc.Pc.v1397, CFSG.KD.Fi24Tc.Pc.v1398, CFSG.KD.Fi24Tc.Pc.v1399, CFSG.KD.Fi24Tc.Pc.v1400, CFSG.KD.Fi24Tc.Pc.v1401]
theorem CFSG.KD.Fi24Tc.Pc.p1400 : Nat.beq (runC AR SD 1396 (ckL CFSG.KD.Fi24Tc.Pc.l1402) 2 1400 CFSG.KD.Fi24Tc.Pc.l1400) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f200 : Nat.beq (runC AR SD 1396 (finC AR SD (nat_lit 200) 1396 1403) 1 1402 CFSG.KD.Fi24Tc.Pc.l1402) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk200 : chk (nat_lit 200) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 200) (lo := 1396) (hi := 1403) (m := 7) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 7) (m2 := 5) (j2 := 1398) CFSG.KD.Fi24Tc.Pc.p1396 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 1400) CFSG.KD.Fi24Tc.Pc.p1398 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 1402) CFSG.KD.Fi24Tc.Pc.p1400 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f200

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1403_2 : Nat := CFSG.KD.Fi24Tc.KV10 6
theorem CFSG.KD.Fi24Tc.Pc.q1403_2 : Nat.beq (powTop AR.mul (getV AR SD 1403 [] (SD.na.getD 1403 0)) (SD.nk.getD 1403 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1403_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1403 : Nat := CFSG.KD.Fi24Tc.KV10 7
theorem CFSG.KD.Fi24Tc.Pc.r1403 : Nat.beq (powR AR.mul AR.one (getV AR SD 1403 [] (SD.na.getD 1403 0)) (SD.nk.getD 1403 1) 2 CFSG.KD.Fi24Tc.Pc.a1403_2 true) CFSG.KD.Fi24Tc.Pc.v1403 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1404 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1403]
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1404 : Nat := CFSG.KD.Fi24Tc.KV10 8
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1405 : Nat := CFSG.KD.Fi24Tc.KV10 9
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1406 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1403, CFSG.KD.Fi24Tc.Pc.v1404, CFSG.KD.Fi24Tc.Pc.v1405]
theorem CFSG.KD.Fi24Tc.Pc.p1404 : Nat.beq (runC AR SD 1403 (ckL CFSG.KD.Fi24Tc.Pc.l1406) 2 1404 CFSG.KD.Fi24Tc.Pc.l1404) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f201 : Nat.beq (runC AR SD 1403 (finC AR SD (nat_lit 201) 1403 1408) 2 1406 CFSG.KD.Fi24Tc.Pc.l1406) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk201 : chk (nat_lit 201) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 201) (lo := 1403) (hi := 1408) (m := 5) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 5) (m2 := 4) (j2 := 1404) (Lr := CFSG.KD.Fi24Tc.Pc.l1404) ((nodeV_pow (R := AR) (D := SD) (lo := 1403) (L := []) (j := 1403) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1403 [] (SD.na.getD 1403 0)) (SD.nk.getD 1403 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1403_2 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1403)))) (by quickRfl) rfl rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1406) CFSG.KD.Fi24Tc.Pc.p1404 rfl rfl)))).trans CFSG.KD.Fi24Tc.Pc.f201

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1408 : Nat := CFSG.KD.Fi24Tc.KV10 10
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1409 : Nat := CFSG.KD.Fi24Tc.KV10 11
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1410 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1408, CFSG.KD.Fi24Tc.Pc.v1409]
theorem CFSG.KD.Fi24Tc.Pc.p1408 : Nat.beq (runC AR SD 1408 (ckL CFSG.KD.Fi24Tc.Pc.l1410) 2 1408 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1410 : Nat := CFSG.KD.Fi24Tc.KV10 12
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1411 : Nat := CFSG.KD.Fi24Tc.KV10 13
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1412 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1408, CFSG.KD.Fi24Tc.Pc.v1409, CFSG.KD.Fi24Tc.Pc.v1410, CFSG.KD.Fi24Tc.Pc.v1411]
theorem CFSG.KD.Fi24Tc.Pc.p1410 : Nat.beq (runC AR SD 1408 (ckL CFSG.KD.Fi24Tc.Pc.l1412) 2 1410 CFSG.KD.Fi24Tc.Pc.l1410) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1412 : Nat := CFSG.KD.Fi24Tc.KV10 14
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1413 : Nat := CFSG.KD.Fi24Tc.KV10 15
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1414 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1408, CFSG.KD.Fi24Tc.Pc.v1409, CFSG.KD.Fi24Tc.Pc.v1410, CFSG.KD.Fi24Tc.Pc.v1411, CFSG.KD.Fi24Tc.Pc.v1412, CFSG.KD.Fi24Tc.Pc.v1413]
theorem CFSG.KD.Fi24Tc.Pc.p1412 : Nat.beq (runC AR SD 1408 (ckL CFSG.KD.Fi24Tc.Pc.l1414) 2 1412 CFSG.KD.Fi24Tc.Pc.l1412) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f202 : Nat.beq (runC AR SD 1408 (finC AR SD (nat_lit 202) 1408 1416) 2 1414 CFSG.KD.Fi24Tc.Pc.l1414) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk202 : chk (nat_lit 202) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 202) (lo := 1408) (hi := 1416) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1410) CFSG.KD.Fi24Tc.Pc.p1408 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1412) CFSG.KD.Fi24Tc.Pc.p1410 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1414) CFSG.KD.Fi24Tc.Pc.p1412 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f202

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1416 : Nat := CFSG.KD.Fi24Tc.KV10 16
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1417 : Nat := CFSG.KD.Fi24Tc.KV10 17
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1418 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1416, CFSG.KD.Fi24Tc.Pc.v1417]
theorem CFSG.KD.Fi24Tc.Pc.p1416 : Nat.beq (runC AR SD 1416 (ckL CFSG.KD.Fi24Tc.Pc.l1418) 2 1416 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1418 : Nat := CFSG.KD.Fi24Tc.KV10 18
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1419 : Nat := CFSG.KD.Fi24Tc.KV10 19
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1420 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1416, CFSG.KD.Fi24Tc.Pc.v1417, CFSG.KD.Fi24Tc.Pc.v1418, CFSG.KD.Fi24Tc.Pc.v1419]
theorem CFSG.KD.Fi24Tc.Pc.p1418 : Nat.beq (runC AR SD 1416 (ckL CFSG.KD.Fi24Tc.Pc.l1420) 2 1418 CFSG.KD.Fi24Tc.Pc.l1418) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1420 : Nat := CFSG.KD.Fi24Tc.KV10 20
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1421 : Nat := CFSG.KD.Fi24Tc.KV10 21
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1422 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1416, CFSG.KD.Fi24Tc.Pc.v1417, CFSG.KD.Fi24Tc.Pc.v1418, CFSG.KD.Fi24Tc.Pc.v1419, CFSG.KD.Fi24Tc.Pc.v1420, CFSG.KD.Fi24Tc.Pc.v1421]
theorem CFSG.KD.Fi24Tc.Pc.p1420 : Nat.beq (runC AR SD 1416 (ckL CFSG.KD.Fi24Tc.Pc.l1422) 2 1420 CFSG.KD.Fi24Tc.Pc.l1420) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f203 : Nat.beq (runC AR SD 1416 (finC AR SD (nat_lit 203) 1416 1424) 2 1422 CFSG.KD.Fi24Tc.Pc.l1422) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk203 : chk (nat_lit 203) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 203) (lo := 1416) (hi := 1424) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1418) CFSG.KD.Fi24Tc.Pc.p1416 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1420) CFSG.KD.Fi24Tc.Pc.p1418 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1422) CFSG.KD.Fi24Tc.Pc.p1420 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f203

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1424 : Nat := CFSG.KD.Fi24Tc.KV10 22
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1425 : Nat := CFSG.KD.Fi24Tc.KV10 23
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1426 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1424, CFSG.KD.Fi24Tc.Pc.v1425]
theorem CFSG.KD.Fi24Tc.Pc.p1424 : Nat.beq (runC AR SD 1424 (ckL CFSG.KD.Fi24Tc.Pc.l1426) 2 1424 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1426 : Nat := CFSG.KD.Fi24Tc.KV10 24
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1427 : Nat := CFSG.KD.Fi24Tc.KV10 25
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1428 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1424, CFSG.KD.Fi24Tc.Pc.v1425, CFSG.KD.Fi24Tc.Pc.v1426, CFSG.KD.Fi24Tc.Pc.v1427]
theorem CFSG.KD.Fi24Tc.Pc.p1426 : Nat.beq (runC AR SD 1424 (ckL CFSG.KD.Fi24Tc.Pc.l1428) 2 1426 CFSG.KD.Fi24Tc.Pc.l1426) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1428 : Nat := CFSG.KD.Fi24Tc.KV10 26
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1429 : Nat := CFSG.KD.Fi24Tc.KV10 27
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1430 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1424, CFSG.KD.Fi24Tc.Pc.v1425, CFSG.KD.Fi24Tc.Pc.v1426, CFSG.KD.Fi24Tc.Pc.v1427, CFSG.KD.Fi24Tc.Pc.v1428, CFSG.KD.Fi24Tc.Pc.v1429]
theorem CFSG.KD.Fi24Tc.Pc.p1428 : Nat.beq (runC AR SD 1424 (ckL CFSG.KD.Fi24Tc.Pc.l1430) 2 1428 CFSG.KD.Fi24Tc.Pc.l1428) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f204 : Nat.beq (runC AR SD 1424 (finC AR SD (nat_lit 204) 1424 1432) 2 1430 CFSG.KD.Fi24Tc.Pc.l1430) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk204 : chk (nat_lit 204) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 204) (lo := 1424) (hi := 1432) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1426) CFSG.KD.Fi24Tc.Pc.p1424 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1428) CFSG.KD.Fi24Tc.Pc.p1426 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1430) CFSG.KD.Fi24Tc.Pc.p1428 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f204

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1432 : Nat := CFSG.KD.Fi24Tc.KV10 28
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1433 : Nat := CFSG.KD.Fi24Tc.KV10 29
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1434 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1432, CFSG.KD.Fi24Tc.Pc.v1433]
theorem CFSG.KD.Fi24Tc.Pc.p1432 : Nat.beq (runC AR SD 1432 (ckL CFSG.KD.Fi24Tc.Pc.l1434) 2 1432 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1434 : Nat := CFSG.KD.Fi24Tc.KV10 30
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1435 : Nat := CFSG.KD.Fi24Tc.KV10 31
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1436 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1432, CFSG.KD.Fi24Tc.Pc.v1433, CFSG.KD.Fi24Tc.Pc.v1434, CFSG.KD.Fi24Tc.Pc.v1435]
theorem CFSG.KD.Fi24Tc.Pc.p1434 : Nat.beq (runC AR SD 1432 (ckL CFSG.KD.Fi24Tc.Pc.l1436) 2 1434 CFSG.KD.Fi24Tc.Pc.l1434) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1436 : Nat := CFSG.KD.Fi24Tc.KV10 32
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1437 : Nat := CFSG.KD.Fi24Tc.KV10 33
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1438 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1432, CFSG.KD.Fi24Tc.Pc.v1433, CFSG.KD.Fi24Tc.Pc.v1434, CFSG.KD.Fi24Tc.Pc.v1435, CFSG.KD.Fi24Tc.Pc.v1436, CFSG.KD.Fi24Tc.Pc.v1437]
theorem CFSG.KD.Fi24Tc.Pc.p1436 : Nat.beq (runC AR SD 1432 (ckL CFSG.KD.Fi24Tc.Pc.l1438) 2 1436 CFSG.KD.Fi24Tc.Pc.l1436) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f205 : Nat.beq (runC AR SD 1432 (finC AR SD (nat_lit 205) 1432 1440) 2 1438 CFSG.KD.Fi24Tc.Pc.l1438) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk205 : chk (nat_lit 205) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 205) (lo := 1432) (hi := 1440) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1434) CFSG.KD.Fi24Tc.Pc.p1432 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1436) CFSG.KD.Fi24Tc.Pc.p1434 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1438) CFSG.KD.Fi24Tc.Pc.p1436 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f205

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1440 : Nat := CFSG.KD.Fi24Tc.KV10 34
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1441 : Nat := CFSG.KD.Fi24Tc.KV10 35
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1442 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1440, CFSG.KD.Fi24Tc.Pc.v1441]
theorem CFSG.KD.Fi24Tc.Pc.p1440 : Nat.beq (runC AR SD 1440 (ckL CFSG.KD.Fi24Tc.Pc.l1442) 2 1440 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1442 : Nat := CFSG.KD.Fi24Tc.KV10 36
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1443 : Nat := CFSG.KD.Fi24Tc.KV10 37
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1444 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1440, CFSG.KD.Fi24Tc.Pc.v1441, CFSG.KD.Fi24Tc.Pc.v1442, CFSG.KD.Fi24Tc.Pc.v1443]
theorem CFSG.KD.Fi24Tc.Pc.p1442 : Nat.beq (runC AR SD 1440 (ckL CFSG.KD.Fi24Tc.Pc.l1444) 2 1442 CFSG.KD.Fi24Tc.Pc.l1442) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1444 : Nat := CFSG.KD.Fi24Tc.KV10 38
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1445 : Nat := CFSG.KD.Fi24Tc.KV10 39
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1446 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1440, CFSG.KD.Fi24Tc.Pc.v1441, CFSG.KD.Fi24Tc.Pc.v1442, CFSG.KD.Fi24Tc.Pc.v1443, CFSG.KD.Fi24Tc.Pc.v1444, CFSG.KD.Fi24Tc.Pc.v1445]
theorem CFSG.KD.Fi24Tc.Pc.p1444 : Nat.beq (runC AR SD 1440 (ckL CFSG.KD.Fi24Tc.Pc.l1446) 2 1444 CFSG.KD.Fi24Tc.Pc.l1444) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f206 : Nat.beq (runC AR SD 1440 (finC AR SD (nat_lit 206) 1440 1448) 2 1446 CFSG.KD.Fi24Tc.Pc.l1446) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk206 : chk (nat_lit 206) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 206) (lo := 1440) (hi := 1448) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1442) CFSG.KD.Fi24Tc.Pc.p1440 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1444) CFSG.KD.Fi24Tc.Pc.p1442 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1446) CFSG.KD.Fi24Tc.Pc.p1444 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f206

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1448 : Nat := CFSG.KD.Fi24Tc.KV10 40
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1449 : Nat := CFSG.KD.Fi24Tc.KV10 41
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1450 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1448, CFSG.KD.Fi24Tc.Pc.v1449]
theorem CFSG.KD.Fi24Tc.Pc.p1448 : Nat.beq (runC AR SD 1448 (ckL CFSG.KD.Fi24Tc.Pc.l1450) 2 1448 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1450 : Nat := CFSG.KD.Fi24Tc.KV10 42
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1451 : Nat := CFSG.KD.Fi24Tc.KV10 43
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1452 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1448, CFSG.KD.Fi24Tc.Pc.v1449, CFSG.KD.Fi24Tc.Pc.v1450, CFSG.KD.Fi24Tc.Pc.v1451]
theorem CFSG.KD.Fi24Tc.Pc.p1450 : Nat.beq (runC AR SD 1448 (ckL CFSG.KD.Fi24Tc.Pc.l1452) 2 1450 CFSG.KD.Fi24Tc.Pc.l1450) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1452 : Nat := CFSG.KD.Fi24Tc.KV10 44
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1453 : Nat := CFSG.KD.Fi24Tc.KV10 45
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1454 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1448, CFSG.KD.Fi24Tc.Pc.v1449, CFSG.KD.Fi24Tc.Pc.v1450, CFSG.KD.Fi24Tc.Pc.v1451, CFSG.KD.Fi24Tc.Pc.v1452, CFSG.KD.Fi24Tc.Pc.v1453]
theorem CFSG.KD.Fi24Tc.Pc.p1452 : Nat.beq (runC AR SD 1448 (ckL CFSG.KD.Fi24Tc.Pc.l1454) 2 1452 CFSG.KD.Fi24Tc.Pc.l1452) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f207 : Nat.beq (runC AR SD 1448 (finC AR SD (nat_lit 207) 1448 1456) 2 1454 CFSG.KD.Fi24Tc.Pc.l1454) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk207 : chk (nat_lit 207) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 207) (lo := 1448) (hi := 1456) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1450) CFSG.KD.Fi24Tc.Pc.p1448 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1452) CFSG.KD.Fi24Tc.Pc.p1450 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1454) CFSG.KD.Fi24Tc.Pc.p1452 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f207

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1456 : Nat := CFSG.KD.Fi24Tc.KV10 46
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1457 : Nat := CFSG.KD.Fi24Tc.KV10 47
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1458 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1456, CFSG.KD.Fi24Tc.Pc.v1457]
theorem CFSG.KD.Fi24Tc.Pc.p1456 : Nat.beq (runC AR SD 1456 (ckL CFSG.KD.Fi24Tc.Pc.l1458) 2 1456 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1458 : Nat := CFSG.KD.Fi24Tc.KV10 48
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1459 : Nat := CFSG.KD.Fi24Tc.KV10 49
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1460 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1456, CFSG.KD.Fi24Tc.Pc.v1457, CFSG.KD.Fi24Tc.Pc.v1458, CFSG.KD.Fi24Tc.Pc.v1459]
theorem CFSG.KD.Fi24Tc.Pc.p1458 : Nat.beq (runC AR SD 1456 (ckL CFSG.KD.Fi24Tc.Pc.l1460) 2 1458 CFSG.KD.Fi24Tc.Pc.l1458) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1460 : Nat := CFSG.KD.Fi24Tc.KV10 50
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1461 : Nat := CFSG.KD.Fi24Tc.KV10 51
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1462 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1456, CFSG.KD.Fi24Tc.Pc.v1457, CFSG.KD.Fi24Tc.Pc.v1458, CFSG.KD.Fi24Tc.Pc.v1459, CFSG.KD.Fi24Tc.Pc.v1460, CFSG.KD.Fi24Tc.Pc.v1461]
theorem CFSG.KD.Fi24Tc.Pc.p1460 : Nat.beq (runC AR SD 1456 (ckL CFSG.KD.Fi24Tc.Pc.l1462) 2 1460 CFSG.KD.Fi24Tc.Pc.l1460) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f208 : Nat.beq (runC AR SD 1456 (finC AR SD (nat_lit 208) 1456 1464) 2 1462 CFSG.KD.Fi24Tc.Pc.l1462) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk208 : chk (nat_lit 208) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 208) (lo := 1456) (hi := 1464) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1458) CFSG.KD.Fi24Tc.Pc.p1456 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1460) CFSG.KD.Fi24Tc.Pc.p1458 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1462) CFSG.KD.Fi24Tc.Pc.p1460 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f208

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1464 : Nat := CFSG.KD.Fi24Tc.KV10 52
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1465 : Nat := CFSG.KD.Fi24Tc.KV10 53
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1466 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1464, CFSG.KD.Fi24Tc.Pc.v1465]
theorem CFSG.KD.Fi24Tc.Pc.p1464 : Nat.beq (runC AR SD 1464 (ckL CFSG.KD.Fi24Tc.Pc.l1466) 2 1464 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1466 : Nat := CFSG.KD.Fi24Tc.KV10 54
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1467 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1464, CFSG.KD.Fi24Tc.Pc.v1465, CFSG.KD.Fi24Tc.Pc.v1466]
theorem CFSG.KD.Fi24Tc.Pc.p1466 : Nat.beq (runC AR SD 1464 (ckL CFSG.KD.Fi24Tc.Pc.l1467) 1 1466 CFSG.KD.Fi24Tc.Pc.l1466) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1467 : Nat := CFSG.KD.Fi24Tc.KV10 55
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1468 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1464, CFSG.KD.Fi24Tc.Pc.v1465, CFSG.KD.Fi24Tc.Pc.v1466, CFSG.KD.Fi24Tc.Pc.v1467]
theorem CFSG.KD.Fi24Tc.Pc.p1467 : Nat.beq (runC AR SD 1464 (ckL CFSG.KD.Fi24Tc.Pc.l1468) 1 1467 CFSG.KD.Fi24Tc.Pc.l1467) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f209 : Nat.beq (runC AR SD 1464 (finC AR SD (nat_lit 209) 1464 1469) 1 1468 CFSG.KD.Fi24Tc.Pc.l1468) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk209 : chk (nat_lit 209) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 209) (lo := 1464) (hi := 1469) (m := 5) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 5) (m2 := 3) (j2 := 1466) CFSG.KD.Fi24Tc.Pc.p1464 rfl rfl).trans ((runC_seq (m := 3) (m2 := 2) (j2 := 1467) CFSG.KD.Fi24Tc.Pc.p1466 rfl rfl).trans (runC_seq (m := 2) (m2 := 1) (j2 := 1468) CFSG.KD.Fi24Tc.Pc.p1467 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f209

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1469 : Nat := CFSG.KD.Fi24Tc.KV10 56
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1470 : Nat := CFSG.KD.Fi24Tc.KV10 57
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1471 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1469, CFSG.KD.Fi24Tc.Pc.v1470]
theorem CFSG.KD.Fi24Tc.Pc.p1469 : Nat.beq (runC AR SD 1469 (ckL CFSG.KD.Fi24Tc.Pc.l1471) 2 1469 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1471 : Nat := CFSG.KD.Fi24Tc.KV10 58
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1472 : Nat := CFSG.KD.Fi24Tc.KV10 59
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1473 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1469, CFSG.KD.Fi24Tc.Pc.v1470, CFSG.KD.Fi24Tc.Pc.v1471, CFSG.KD.Fi24Tc.Pc.v1472]
theorem CFSG.KD.Fi24Tc.Pc.p1471 : Nat.beq (runC AR SD 1469 (ckL CFSG.KD.Fi24Tc.Pc.l1473) 2 1471 CFSG.KD.Fi24Tc.Pc.l1471) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1473 : Nat := CFSG.KD.Fi24Tc.KV10 60
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1474 : Nat := CFSG.KD.Fi24Tc.KV10 61
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1475 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1469, CFSG.KD.Fi24Tc.Pc.v1470, CFSG.KD.Fi24Tc.Pc.v1471, CFSG.KD.Fi24Tc.Pc.v1472, CFSG.KD.Fi24Tc.Pc.v1473, CFSG.KD.Fi24Tc.Pc.v1474]
theorem CFSG.KD.Fi24Tc.Pc.p1473 : Nat.beq (runC AR SD 1469 (ckL CFSG.KD.Fi24Tc.Pc.l1475) 2 1473 CFSG.KD.Fi24Tc.Pc.l1473) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f210 : Nat.beq (runC AR SD 1469 (finC AR SD (nat_lit 210) 1469 1477) 2 1475 CFSG.KD.Fi24Tc.Pc.l1475) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk210 : chk (nat_lit 210) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 210) (lo := 1469) (hi := 1477) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1471) CFSG.KD.Fi24Tc.Pc.p1469 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1473) CFSG.KD.Fi24Tc.Pc.p1471 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1475) CFSG.KD.Fi24Tc.Pc.p1473 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f210

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1477 : Nat := CFSG.KD.Fi24Tc.KV10 96
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1478 : Nat := CFSG.KD.Fi24Tc.KV10 97
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1479 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1477, CFSG.KD.Fi24Tc.Pc.v1478]
theorem CFSG.KD.Fi24Tc.Pc.p1477 : Nat.beq (runC AR SD 1477 (ckL CFSG.KD.Fi24Tc.Pc.l1479) 2 1477 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1479 : Nat := CFSG.KD.Fi24Tc.KV10 98
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1480 : Nat := CFSG.KD.Fi24Tc.KV10 99
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1481 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1477, CFSG.KD.Fi24Tc.Pc.v1478, CFSG.KD.Fi24Tc.Pc.v1479, CFSG.KD.Fi24Tc.Pc.v1480]
theorem CFSG.KD.Fi24Tc.Pc.p1479 : Nat.beq (runC AR SD 1477 (ckL CFSG.KD.Fi24Tc.Pc.l1481) 2 1479 CFSG.KD.Fi24Tc.Pc.l1479) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1481 : Nat := CFSG.KD.Fi24Tc.KV10 100
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1482 : Nat := CFSG.KD.Fi24Tc.KV10 101
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1483 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1477, CFSG.KD.Fi24Tc.Pc.v1478, CFSG.KD.Fi24Tc.Pc.v1479, CFSG.KD.Fi24Tc.Pc.v1480, CFSG.KD.Fi24Tc.Pc.v1481, CFSG.KD.Fi24Tc.Pc.v1482]
theorem CFSG.KD.Fi24Tc.Pc.p1481 : Nat.beq (runC AR SD 1477 (ckL CFSG.KD.Fi24Tc.Pc.l1483) 2 1481 CFSG.KD.Fi24Tc.Pc.l1481) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f211 : Nat.beq (runC AR SD 1477 (finC AR SD (nat_lit 211) 1477 1485) 2 1483 CFSG.KD.Fi24Tc.Pc.l1483) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk211 : chk (nat_lit 211) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 211) (lo := 1477) (hi := 1485) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1479) CFSG.KD.Fi24Tc.Pc.p1477 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1481) CFSG.KD.Fi24Tc.Pc.p1479 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1483) CFSG.KD.Fi24Tc.Pc.p1481 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f211

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1485 : Nat := CFSG.KD.Fi24Tc.KV10 102
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1486 : Nat := CFSG.KD.Fi24Tc.KV10 103
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1487 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1485, CFSG.KD.Fi24Tc.Pc.v1486]
theorem CFSG.KD.Fi24Tc.Pc.p1485 : Nat.beq (runC AR SD 1485 (ckL CFSG.KD.Fi24Tc.Pc.l1487) 2 1485 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1487 : Nat := CFSG.KD.Fi24Tc.KV10 104
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1488 : Nat := CFSG.KD.Fi24Tc.KV10 105
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1489 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1485, CFSG.KD.Fi24Tc.Pc.v1486, CFSG.KD.Fi24Tc.Pc.v1487, CFSG.KD.Fi24Tc.Pc.v1488]
theorem CFSG.KD.Fi24Tc.Pc.p1487 : Nat.beq (runC AR SD 1485 (ckL CFSG.KD.Fi24Tc.Pc.l1489) 2 1487 CFSG.KD.Fi24Tc.Pc.l1487) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1489 : Nat := CFSG.KD.Fi24Tc.KV10 106
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1490 : Nat := CFSG.KD.Fi24Tc.KV10 107
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1491 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1485, CFSG.KD.Fi24Tc.Pc.v1486, CFSG.KD.Fi24Tc.Pc.v1487, CFSG.KD.Fi24Tc.Pc.v1488, CFSG.KD.Fi24Tc.Pc.v1489, CFSG.KD.Fi24Tc.Pc.v1490]
theorem CFSG.KD.Fi24Tc.Pc.p1489 : Nat.beq (runC AR SD 1485 (ckL CFSG.KD.Fi24Tc.Pc.l1491) 2 1489 CFSG.KD.Fi24Tc.Pc.l1489) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f212 : Nat.beq (runC AR SD 1485 (finC AR SD (nat_lit 212) 1485 1493) 2 1491 CFSG.KD.Fi24Tc.Pc.l1491) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk212 : chk (nat_lit 212) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 212) (lo := 1485) (hi := 1493) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1487) CFSG.KD.Fi24Tc.Pc.p1485 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1489) CFSG.KD.Fi24Tc.Pc.p1487 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1491) CFSG.KD.Fi24Tc.Pc.p1489 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f212

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1493 : Nat := CFSG.KD.Fi24Tc.KV10 62
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1494 : Nat := CFSG.KD.Fi24Tc.KV10 63
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1495 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1493, CFSG.KD.Fi24Tc.Pc.v1494]
theorem CFSG.KD.Fi24Tc.Pc.p1493 : Nat.beq (runC AR SD 1493 (ckL CFSG.KD.Fi24Tc.Pc.l1495) 2 1493 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1495 : Nat := CFSG.KD.Fi24Tc.KV10 64
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1496 : Nat := CFSG.KD.Fi24Tc.KV10 65
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1497 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1493, CFSG.KD.Fi24Tc.Pc.v1494, CFSG.KD.Fi24Tc.Pc.v1495, CFSG.KD.Fi24Tc.Pc.v1496]
theorem CFSG.KD.Fi24Tc.Pc.p1495 : Nat.beq (runC AR SD 1493 (ckL CFSG.KD.Fi24Tc.Pc.l1497) 2 1495 CFSG.KD.Fi24Tc.Pc.l1495) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1497 : Nat := CFSG.KD.Fi24Tc.KV10 66
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1498 : Nat := CFSG.KD.Fi24Tc.KV10 67
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1499 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1493, CFSG.KD.Fi24Tc.Pc.v1494, CFSG.KD.Fi24Tc.Pc.v1495, CFSG.KD.Fi24Tc.Pc.v1496, CFSG.KD.Fi24Tc.Pc.v1497, CFSG.KD.Fi24Tc.Pc.v1498]
theorem CFSG.KD.Fi24Tc.Pc.p1497 : Nat.beq (runC AR SD 1493 (ckL CFSG.KD.Fi24Tc.Pc.l1499) 2 1497 CFSG.KD.Fi24Tc.Pc.l1497) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f213 : Nat.beq (runC AR SD 1493 (finC AR SD (nat_lit 213) 1493 1501) 2 1499 CFSG.KD.Fi24Tc.Pc.l1499) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk213 : chk (nat_lit 213) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 213) (lo := 1493) (hi := 1501) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1495) CFSG.KD.Fi24Tc.Pc.p1493 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1497) CFSG.KD.Fi24Tc.Pc.p1495 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1499) CFSG.KD.Fi24Tc.Pc.p1497 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f213

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1501 : Nat := CFSG.KD.Fi24Tc.KV10 68
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1502 : Nat := CFSG.KD.Fi24Tc.KV10 69
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1503 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1501, CFSG.KD.Fi24Tc.Pc.v1502]
theorem CFSG.KD.Fi24Tc.Pc.p1501 : Nat.beq (runC AR SD 1501 (ckL CFSG.KD.Fi24Tc.Pc.l1503) 2 1501 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1503 : Nat := CFSG.KD.Fi24Tc.KV10 70
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1504 : Nat := CFSG.KD.Fi24Tc.KV10 71
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1505 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1501, CFSG.KD.Fi24Tc.Pc.v1502, CFSG.KD.Fi24Tc.Pc.v1503, CFSG.KD.Fi24Tc.Pc.v1504]
theorem CFSG.KD.Fi24Tc.Pc.p1503 : Nat.beq (runC AR SD 1501 (ckL CFSG.KD.Fi24Tc.Pc.l1505) 2 1503 CFSG.KD.Fi24Tc.Pc.l1503) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1505 : Nat := CFSG.KD.Fi24Tc.KV10 72
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1506 : Nat := CFSG.KD.Fi24Tc.KV10 73
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1507 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1501, CFSG.KD.Fi24Tc.Pc.v1502, CFSG.KD.Fi24Tc.Pc.v1503, CFSG.KD.Fi24Tc.Pc.v1504, CFSG.KD.Fi24Tc.Pc.v1505, CFSG.KD.Fi24Tc.Pc.v1506]
theorem CFSG.KD.Fi24Tc.Pc.p1505 : Nat.beq (runC AR SD 1501 (ckL CFSG.KD.Fi24Tc.Pc.l1507) 2 1505 CFSG.KD.Fi24Tc.Pc.l1505) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f214 : Nat.beq (runC AR SD 1501 (finC AR SD (nat_lit 214) 1501 1509) 2 1507 CFSG.KD.Fi24Tc.Pc.l1507) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk214 : chk (nat_lit 214) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 214) (lo := 1501) (hi := 1509) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1503) CFSG.KD.Fi24Tc.Pc.p1501 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1505) CFSG.KD.Fi24Tc.Pc.p1503 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1507) CFSG.KD.Fi24Tc.Pc.p1505 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f214

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1509 : Nat := CFSG.KD.Fi24Tc.KV10 74
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1510 : Nat := CFSG.KD.Fi24Tc.KV10 75
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1511 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1509, CFSG.KD.Fi24Tc.Pc.v1510]
theorem CFSG.KD.Fi24Tc.Pc.p1509 : Nat.beq (runC AR SD 1509 (ckL CFSG.KD.Fi24Tc.Pc.l1511) 2 1509 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1511_3 : Nat := CFSG.KD.Fi24Tc.KV10 76
theorem CFSG.KD.Fi24Tc.Pc.q1511_3 : Nat.beq (powTop AR.mul (getV AR SD 1509 CFSG.KD.Fi24Tc.Pc.l1511 (SD.na.getD 1511 0)) (SD.nk.getD 1511 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a1511_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1511_2 : Nat := CFSG.KD.Fi24Tc.KV10 77
theorem CFSG.KD.Fi24Tc.Pc.q1511_2 : Nat.beq (powTop AR.mul (getV AR SD 1509 CFSG.KD.Fi24Tc.Pc.l1511 (SD.na.getD 1511 0)) (SD.nk.getD 1511 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1511_2) 1 CFSG.KD.Fi24Tc.Pc.a1511_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1511_1 : Nat := CFSG.KD.Fi24Tc.KV10 78
theorem CFSG.KD.Fi24Tc.Pc.q1511_1 : Nat.beq (powTop AR.mul (getV AR SD 1509 CFSG.KD.Fi24Tc.Pc.l1511 (SD.na.getD 1511 0)) (SD.nk.getD 1511 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a1511_1) 1 CFSG.KD.Fi24Tc.Pc.a1511_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1511 : Nat := CFSG.KD.Fi24Tc.KV10 79
theorem CFSG.KD.Fi24Tc.Pc.r1511 : Nat.beq (powR AR.mul AR.one (getV AR SD 1509 CFSG.KD.Fi24Tc.Pc.l1511 (SD.na.getD 1511 0)) (SD.nk.getD 1511 1) 1 CFSG.KD.Fi24Tc.Pc.a1511_1 true) CFSG.KD.Fi24Tc.Pc.v1511 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1512 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1509, CFSG.KD.Fi24Tc.Pc.v1510, CFSG.KD.Fi24Tc.Pc.v1511]
theorem CFSG.KD.Fi24Tc.Pc.f215 : Nat.beq (runC AR SD 1509 (finC AR SD (nat_lit 215) 1509 1512) 0 1512 CFSG.KD.Fi24Tc.Pc.l1512) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk215 : chk (nat_lit 215) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 215) (lo := 1509) (hi := 1512) (m := 3) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 3) (m2 := 1) (j2 := 1511) CFSG.KD.Fi24Tc.Pc.p1509 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 1512) (Lr := CFSG.KD.Fi24Tc.Pc.l1512) ((nodeV_pow (R := AR) (D := SD) (lo := 1509) (L := CFSG.KD.Fi24Tc.Pc.l1511) (j := 1511) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1509 CFSG.KD.Fi24Tc.Pc.l1511 (SD.na.getD 1511 0)) (SD.nk.getD 1511 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1511_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q1511_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q1511_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1511)))))) (by quickRfl) rfl rfl rfl)))).trans CFSG.KD.Fi24Tc.Pc.f215

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1512 : Nat := CFSG.KD.Fi24Tc.KV10 80
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1513 : Nat := CFSG.KD.Fi24Tc.KV10 81
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1514 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1512, CFSG.KD.Fi24Tc.Pc.v1513]
theorem CFSG.KD.Fi24Tc.Pc.p1512 : Nat.beq (runC AR SD 1512 (ckL CFSG.KD.Fi24Tc.Pc.l1514) 2 1512 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1514 : Nat := CFSG.KD.Fi24Tc.KV10 82
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1515 : Nat := CFSG.KD.Fi24Tc.KV10 83
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1516 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1512, CFSG.KD.Fi24Tc.Pc.v1513, CFSG.KD.Fi24Tc.Pc.v1514, CFSG.KD.Fi24Tc.Pc.v1515]
theorem CFSG.KD.Fi24Tc.Pc.p1514 : Nat.beq (runC AR SD 1512 (ckL CFSG.KD.Fi24Tc.Pc.l1516) 2 1514 CFSG.KD.Fi24Tc.Pc.l1514) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1516 : Nat := CFSG.KD.Fi24Tc.KV10 84
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1517 : Nat := CFSG.KD.Fi24Tc.KV10 85
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1518 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1512, CFSG.KD.Fi24Tc.Pc.v1513, CFSG.KD.Fi24Tc.Pc.v1514, CFSG.KD.Fi24Tc.Pc.v1515, CFSG.KD.Fi24Tc.Pc.v1516, CFSG.KD.Fi24Tc.Pc.v1517]
theorem CFSG.KD.Fi24Tc.Pc.p1516 : Nat.beq (runC AR SD 1512 (ckL CFSG.KD.Fi24Tc.Pc.l1518) 2 1516 CFSG.KD.Fi24Tc.Pc.l1516) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f216 : Nat.beq (runC AR SD 1512 (finC AR SD (nat_lit 216) 1512 1520) 2 1518 CFSG.KD.Fi24Tc.Pc.l1518) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk216 : chk (nat_lit 216) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 216) (lo := 1512) (hi := 1520) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1514) CFSG.KD.Fi24Tc.Pc.p1512 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1516) CFSG.KD.Fi24Tc.Pc.p1514 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1518) CFSG.KD.Fi24Tc.Pc.p1516 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f216

theorem CFSG.KD.Fi24Tc.Pc.f217 : Nat.beq (runC AR SD 1520 (finC AR SD (nat_lit 217) 1520 1521) 1 1520 []) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk217 : chk (nat_lit 217) = true :=
  (chunkOK_eq (R := AR) (D := SD) (c := nat_lit 217) (lo := 1520) (hi := 1521) (m := 1) rfl rfl rfl).trans CFSG.KD.Fi24Tc.Pc.f217

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1521_3 : Nat := CFSG.KD.Fi24Tc.KV10 86
theorem CFSG.KD.Fi24Tc.Pc.q1521_3 : Nat.beq (powTop AR.mul (getV AR SD 1521 [] (SD.na.getD 1521 0)) (SD.nk.getD 1521 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a1521_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1521_2 : Nat := CFSG.KD.Fi24Tc.KV10 87
theorem CFSG.KD.Fi24Tc.Pc.q1521_2 : Nat.beq (powTop AR.mul (getV AR SD 1521 [] (SD.na.getD 1521 0)) (SD.nk.getD 1521 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1521_2) 1 CFSG.KD.Fi24Tc.Pc.a1521_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1521_1 : Nat := CFSG.KD.Fi24Tc.KV10 88
theorem CFSG.KD.Fi24Tc.Pc.q1521_1 : Nat.beq (powTop AR.mul (getV AR SD 1521 [] (SD.na.getD 1521 0)) (SD.nk.getD 1521 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a1521_1) 1 CFSG.KD.Fi24Tc.Pc.a1521_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1521 : Nat := CFSG.KD.Fi24Tc.KV10 89
theorem CFSG.KD.Fi24Tc.Pc.r1521 : Nat.beq (powR AR.mul AR.one (getV AR SD 1521 [] (SD.na.getD 1521 0)) (SD.nk.getD 1521 1) 1 CFSG.KD.Fi24Tc.Pc.a1521_1 true) CFSG.KD.Fi24Tc.Pc.v1521 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1522 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1521]
theorem CFSG.KD.Fi24Tc.Pc.f218 : Nat.beq (runC AR SD 1521 (finC AR SD (nat_lit 218) 1521 1522) 0 1522 CFSG.KD.Fi24Tc.Pc.l1522) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk218 : chk (nat_lit 218) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 218) (lo := 1521) (hi := 1522) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 1522) (Lr := CFSG.KD.Fi24Tc.Pc.l1522) ((nodeV_pow (R := AR) (D := SD) (lo := 1521) (L := []) (j := 1521) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1521 [] (SD.na.getD 1521 0)) (SD.nk.getD 1521 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1521_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q1521_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q1521_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1521)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f218

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1522 : Nat := CFSG.KD.Fi24Tc.KV10 90
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1523 : Nat := CFSG.KD.Fi24Tc.KV10 91
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1524 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1522, CFSG.KD.Fi24Tc.Pc.v1523]
theorem CFSG.KD.Fi24Tc.Pc.p1522 : Nat.beq (runC AR SD 1522 (ckL CFSG.KD.Fi24Tc.Pc.l1524) 2 1522 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1524 : Nat := CFSG.KD.Fi24Tc.KV10 92
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1525 : Nat := CFSG.KD.Fi24Tc.KV10 93
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1526 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1522, CFSG.KD.Fi24Tc.Pc.v1523, CFSG.KD.Fi24Tc.Pc.v1524, CFSG.KD.Fi24Tc.Pc.v1525]
theorem CFSG.KD.Fi24Tc.Pc.p1524 : Nat.beq (runC AR SD 1522 (ckL CFSG.KD.Fi24Tc.Pc.l1526) 2 1524 CFSG.KD.Fi24Tc.Pc.l1524) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1526 : Nat := CFSG.KD.Fi24Tc.KV10 94
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1527 : Nat := CFSG.KD.Fi24Tc.KV10 95
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1528 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1522, CFSG.KD.Fi24Tc.Pc.v1523, CFSG.KD.Fi24Tc.Pc.v1524, CFSG.KD.Fi24Tc.Pc.v1525, CFSG.KD.Fi24Tc.Pc.v1526, CFSG.KD.Fi24Tc.Pc.v1527]
theorem CFSG.KD.Fi24Tc.Pc.p1526 : Nat.beq (runC AR SD 1522 (ckL CFSG.KD.Fi24Tc.Pc.l1528) 2 1526 CFSG.KD.Fi24Tc.Pc.l1526) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f219 : Nat.beq (runC AR SD 1522 (finC AR SD (nat_lit 219) 1522 1530) 2 1528 CFSG.KD.Fi24Tc.Pc.l1528) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk219 : chk (nat_lit 219) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 219) (lo := 1522) (hi := 1530) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1524) CFSG.KD.Fi24Tc.Pc.p1522 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1526) CFSG.KD.Fi24Tc.Pc.p1524 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1528) CFSG.KD.Fi24Tc.Pc.p1526 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f219

end
