module

public import Certificates.Kernel.Sporadic.Fi24Alpha.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Alpha KV10 "Certificates/Kernel/Sporadic/Fi24Alpha/data/v10.bin" 152491 4 22568668 15875693444707196700

public section

open CFSG.KD.Fi24Alpha CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1453 : Nat := CFSG.KD.Fi24Alpha.KV10 0
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1454 : Nat := CFSG.KD.Fi24Alpha.KV10 1
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1455 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1453, CFSG.KD.Fi24Alpha.Pc.v1454]
theorem CFSG.KD.Fi24Alpha.Pc.p1453 : Nat.beq (runC AR SD 1453 (ckL CFSG.KD.Fi24Alpha.Pc.l1455) 2 1453 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1455 : Nat := CFSG.KD.Fi24Alpha.KV10 2
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1456 : Nat := CFSG.KD.Fi24Alpha.KV10 3
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1457 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1453, CFSG.KD.Fi24Alpha.Pc.v1454, CFSG.KD.Fi24Alpha.Pc.v1455, CFSG.KD.Fi24Alpha.Pc.v1456]
theorem CFSG.KD.Fi24Alpha.Pc.p1455 : Nat.beq (runC AR SD 1453 (ckL CFSG.KD.Fi24Alpha.Pc.l1457) 2 1455 CFSG.KD.Fi24Alpha.Pc.l1455) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1457 : Nat := CFSG.KD.Fi24Alpha.KV10 4
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1458 : Nat := CFSG.KD.Fi24Alpha.KV10 5
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1459 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1453, CFSG.KD.Fi24Alpha.Pc.v1454, CFSG.KD.Fi24Alpha.Pc.v1455, CFSG.KD.Fi24Alpha.Pc.v1456, CFSG.KD.Fi24Alpha.Pc.v1457, CFSG.KD.Fi24Alpha.Pc.v1458]
theorem CFSG.KD.Fi24Alpha.Pc.p1457 : Nat.beq (runC AR SD 1453 (ckL CFSG.KD.Fi24Alpha.Pc.l1459) 2 1457 CFSG.KD.Fi24Alpha.Pc.l1457) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1459 : Nat := CFSG.KD.Fi24Alpha.KV10 6
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1460 : Nat := CFSG.KD.Fi24Alpha.KV10 7
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1461 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1453, CFSG.KD.Fi24Alpha.Pc.v1454, CFSG.KD.Fi24Alpha.Pc.v1455, CFSG.KD.Fi24Alpha.Pc.v1456, CFSG.KD.Fi24Alpha.Pc.v1457, CFSG.KD.Fi24Alpha.Pc.v1458, CFSG.KD.Fi24Alpha.Pc.v1459, CFSG.KD.Fi24Alpha.Pc.v1460]
theorem CFSG.KD.Fi24Alpha.Pc.p1459 : Nat.beq (runC AR SD 1453 (ckL CFSG.KD.Fi24Alpha.Pc.l1461) 2 1459 CFSG.KD.Fi24Alpha.Pc.l1459) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1461 : Nat := CFSG.KD.Fi24Alpha.KV10 8
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1462 : Nat := CFSG.KD.Fi24Alpha.KV10 9
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1463 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1453, CFSG.KD.Fi24Alpha.Pc.v1454, CFSG.KD.Fi24Alpha.Pc.v1455, CFSG.KD.Fi24Alpha.Pc.v1456, CFSG.KD.Fi24Alpha.Pc.v1457, CFSG.KD.Fi24Alpha.Pc.v1458, CFSG.KD.Fi24Alpha.Pc.v1459, CFSG.KD.Fi24Alpha.Pc.v1460, CFSG.KD.Fi24Alpha.Pc.v1461, CFSG.KD.Fi24Alpha.Pc.v1462]
theorem CFSG.KD.Fi24Alpha.Pc.p1461 : Nat.beq (runC AR SD 1453 (ckL CFSG.KD.Fi24Alpha.Pc.l1463) 2 1461 CFSG.KD.Fi24Alpha.Pc.l1461) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1463 : Nat := CFSG.KD.Fi24Alpha.KV10 10
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1464 : Nat := CFSG.KD.Fi24Alpha.KV10 11
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1465 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1453, CFSG.KD.Fi24Alpha.Pc.v1454, CFSG.KD.Fi24Alpha.Pc.v1455, CFSG.KD.Fi24Alpha.Pc.v1456, CFSG.KD.Fi24Alpha.Pc.v1457, CFSG.KD.Fi24Alpha.Pc.v1458, CFSG.KD.Fi24Alpha.Pc.v1459, CFSG.KD.Fi24Alpha.Pc.v1460, CFSG.KD.Fi24Alpha.Pc.v1461, CFSG.KD.Fi24Alpha.Pc.v1462, CFSG.KD.Fi24Alpha.Pc.v1463, CFSG.KD.Fi24Alpha.Pc.v1464]
theorem CFSG.KD.Fi24Alpha.Pc.p1463 : Nat.beq (runC AR SD 1453 (ckL CFSG.KD.Fi24Alpha.Pc.l1465) 2 1463 CFSG.KD.Fi24Alpha.Pc.l1463) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1465 : Nat := CFSG.KD.Fi24Alpha.KV10 12
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1466 : Nat := CFSG.KD.Fi24Alpha.KV10 13
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1467 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1453, CFSG.KD.Fi24Alpha.Pc.v1454, CFSG.KD.Fi24Alpha.Pc.v1455, CFSG.KD.Fi24Alpha.Pc.v1456, CFSG.KD.Fi24Alpha.Pc.v1457, CFSG.KD.Fi24Alpha.Pc.v1458, CFSG.KD.Fi24Alpha.Pc.v1459, CFSG.KD.Fi24Alpha.Pc.v1460, CFSG.KD.Fi24Alpha.Pc.v1461, CFSG.KD.Fi24Alpha.Pc.v1462, CFSG.KD.Fi24Alpha.Pc.v1463, CFSG.KD.Fi24Alpha.Pc.v1464, CFSG.KD.Fi24Alpha.Pc.v1465, CFSG.KD.Fi24Alpha.Pc.v1466]
theorem CFSG.KD.Fi24Alpha.Pc.p1465 : Nat.beq (runC AR SD 1453 (ckL CFSG.KD.Fi24Alpha.Pc.l1467) 2 1465 CFSG.KD.Fi24Alpha.Pc.l1465) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1467 : Nat := CFSG.KD.Fi24Alpha.KV10 14
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1468 : Nat := CFSG.KD.Fi24Alpha.KV10 15
theorem CFSG.KD.Fi24Alpha.Pc.f100 : Nat.beq (runC AR SD 1453 (finC AR SD (nat_lit 100) 1453 1469) 2 1467 CFSG.KD.Fi24Alpha.Pc.l1467) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk100 : chk (nat_lit 100) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 100) (lo := 1453) (hi := 1469) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1455) CFSG.KD.Fi24Alpha.Pc.p1453 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1457) CFSG.KD.Fi24Alpha.Pc.p1455 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1459) CFSG.KD.Fi24Alpha.Pc.p1457 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1461) CFSG.KD.Fi24Alpha.Pc.p1459 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1463) CFSG.KD.Fi24Alpha.Pc.p1461 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1465) CFSG.KD.Fi24Alpha.Pc.p1463 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1467) CFSG.KD.Fi24Alpha.Pc.p1465 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f100

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1469 : Nat := CFSG.KD.Fi24Alpha.KV10 16
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1470 : Nat := CFSG.KD.Fi24Alpha.KV10 17
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1471 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1469, CFSG.KD.Fi24Alpha.Pc.v1470]
theorem CFSG.KD.Fi24Alpha.Pc.p1469 : Nat.beq (runC AR SD 1469 (ckL CFSG.KD.Fi24Alpha.Pc.l1471) 2 1469 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1471 : Nat := CFSG.KD.Fi24Alpha.KV10 18
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1472 : Nat := CFSG.KD.Fi24Alpha.KV10 19
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1473 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1469, CFSG.KD.Fi24Alpha.Pc.v1470, CFSG.KD.Fi24Alpha.Pc.v1471, CFSG.KD.Fi24Alpha.Pc.v1472]
theorem CFSG.KD.Fi24Alpha.Pc.p1471 : Nat.beq (runC AR SD 1469 (ckL CFSG.KD.Fi24Alpha.Pc.l1473) 2 1471 CFSG.KD.Fi24Alpha.Pc.l1471) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1473 : Nat := CFSG.KD.Fi24Alpha.KV10 20
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1474 : Nat := CFSG.KD.Fi24Alpha.KV10 21
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1475 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1469, CFSG.KD.Fi24Alpha.Pc.v1470, CFSG.KD.Fi24Alpha.Pc.v1471, CFSG.KD.Fi24Alpha.Pc.v1472, CFSG.KD.Fi24Alpha.Pc.v1473, CFSG.KD.Fi24Alpha.Pc.v1474]
theorem CFSG.KD.Fi24Alpha.Pc.p1473 : Nat.beq (runC AR SD 1469 (ckL CFSG.KD.Fi24Alpha.Pc.l1475) 2 1473 CFSG.KD.Fi24Alpha.Pc.l1473) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1475 : Nat := CFSG.KD.Fi24Alpha.KV10 22
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1476 : Nat := CFSG.KD.Fi24Alpha.KV10 23
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1477 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1469, CFSG.KD.Fi24Alpha.Pc.v1470, CFSG.KD.Fi24Alpha.Pc.v1471, CFSG.KD.Fi24Alpha.Pc.v1472, CFSG.KD.Fi24Alpha.Pc.v1473, CFSG.KD.Fi24Alpha.Pc.v1474, CFSG.KD.Fi24Alpha.Pc.v1475, CFSG.KD.Fi24Alpha.Pc.v1476]
theorem CFSG.KD.Fi24Alpha.Pc.p1475 : Nat.beq (runC AR SD 1469 (ckL CFSG.KD.Fi24Alpha.Pc.l1477) 2 1475 CFSG.KD.Fi24Alpha.Pc.l1475) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1477 : Nat := CFSG.KD.Fi24Alpha.KV10 24
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1478 : Nat := CFSG.KD.Fi24Alpha.KV10 25
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1479 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1469, CFSG.KD.Fi24Alpha.Pc.v1470, CFSG.KD.Fi24Alpha.Pc.v1471, CFSG.KD.Fi24Alpha.Pc.v1472, CFSG.KD.Fi24Alpha.Pc.v1473, CFSG.KD.Fi24Alpha.Pc.v1474, CFSG.KD.Fi24Alpha.Pc.v1475, CFSG.KD.Fi24Alpha.Pc.v1476, CFSG.KD.Fi24Alpha.Pc.v1477, CFSG.KD.Fi24Alpha.Pc.v1478]
theorem CFSG.KD.Fi24Alpha.Pc.p1477 : Nat.beq (runC AR SD 1469 (ckL CFSG.KD.Fi24Alpha.Pc.l1479) 2 1477 CFSG.KD.Fi24Alpha.Pc.l1477) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1479 : Nat := CFSG.KD.Fi24Alpha.KV10 26
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1480 : Nat := CFSG.KD.Fi24Alpha.KV10 27
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1481 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1469, CFSG.KD.Fi24Alpha.Pc.v1470, CFSG.KD.Fi24Alpha.Pc.v1471, CFSG.KD.Fi24Alpha.Pc.v1472, CFSG.KD.Fi24Alpha.Pc.v1473, CFSG.KD.Fi24Alpha.Pc.v1474, CFSG.KD.Fi24Alpha.Pc.v1475, CFSG.KD.Fi24Alpha.Pc.v1476, CFSG.KD.Fi24Alpha.Pc.v1477, CFSG.KD.Fi24Alpha.Pc.v1478, CFSG.KD.Fi24Alpha.Pc.v1479, CFSG.KD.Fi24Alpha.Pc.v1480]
theorem CFSG.KD.Fi24Alpha.Pc.p1479 : Nat.beq (runC AR SD 1469 (ckL CFSG.KD.Fi24Alpha.Pc.l1481) 2 1479 CFSG.KD.Fi24Alpha.Pc.l1479) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1481 : Nat := CFSG.KD.Fi24Alpha.KV10 28
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1482 : Nat := CFSG.KD.Fi24Alpha.KV10 29
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1483 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1469, CFSG.KD.Fi24Alpha.Pc.v1470, CFSG.KD.Fi24Alpha.Pc.v1471, CFSG.KD.Fi24Alpha.Pc.v1472, CFSG.KD.Fi24Alpha.Pc.v1473, CFSG.KD.Fi24Alpha.Pc.v1474, CFSG.KD.Fi24Alpha.Pc.v1475, CFSG.KD.Fi24Alpha.Pc.v1476, CFSG.KD.Fi24Alpha.Pc.v1477, CFSG.KD.Fi24Alpha.Pc.v1478, CFSG.KD.Fi24Alpha.Pc.v1479, CFSG.KD.Fi24Alpha.Pc.v1480, CFSG.KD.Fi24Alpha.Pc.v1481, CFSG.KD.Fi24Alpha.Pc.v1482]
theorem CFSG.KD.Fi24Alpha.Pc.p1481 : Nat.beq (runC AR SD 1469 (ckL CFSG.KD.Fi24Alpha.Pc.l1483) 2 1481 CFSG.KD.Fi24Alpha.Pc.l1481) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1483 : Nat := CFSG.KD.Fi24Alpha.KV10 30
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1484 : Nat := CFSG.KD.Fi24Alpha.KV10 31
theorem CFSG.KD.Fi24Alpha.Pc.f101 : Nat.beq (runC AR SD 1469 (finC AR SD (nat_lit 101) 1469 1485) 2 1483 CFSG.KD.Fi24Alpha.Pc.l1483) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk101 : chk (nat_lit 101) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 101) (lo := 1469) (hi := 1485) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1471) CFSG.KD.Fi24Alpha.Pc.p1469 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1473) CFSG.KD.Fi24Alpha.Pc.p1471 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1475) CFSG.KD.Fi24Alpha.Pc.p1473 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1477) CFSG.KD.Fi24Alpha.Pc.p1475 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1479) CFSG.KD.Fi24Alpha.Pc.p1477 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1481) CFSG.KD.Fi24Alpha.Pc.p1479 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1483) CFSG.KD.Fi24Alpha.Pc.p1481 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f101

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1485 : Nat := CFSG.KD.Fi24Alpha.KV10 32
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1486 : Nat := CFSG.KD.Fi24Alpha.KV10 33
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1487 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1485, CFSG.KD.Fi24Alpha.Pc.v1486]
theorem CFSG.KD.Fi24Alpha.Pc.p1485 : Nat.beq (runC AR SD 1485 (ckL CFSG.KD.Fi24Alpha.Pc.l1487) 2 1485 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1487 : Nat := CFSG.KD.Fi24Alpha.KV10 34
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1488 : Nat := CFSG.KD.Fi24Alpha.KV10 35
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1489 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1485, CFSG.KD.Fi24Alpha.Pc.v1486, CFSG.KD.Fi24Alpha.Pc.v1487, CFSG.KD.Fi24Alpha.Pc.v1488]
theorem CFSG.KD.Fi24Alpha.Pc.p1487 : Nat.beq (runC AR SD 1485 (ckL CFSG.KD.Fi24Alpha.Pc.l1489) 2 1487 CFSG.KD.Fi24Alpha.Pc.l1487) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1489 : Nat := CFSG.KD.Fi24Alpha.KV10 36
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1490 : Nat := CFSG.KD.Fi24Alpha.KV10 37
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1491 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1485, CFSG.KD.Fi24Alpha.Pc.v1486, CFSG.KD.Fi24Alpha.Pc.v1487, CFSG.KD.Fi24Alpha.Pc.v1488, CFSG.KD.Fi24Alpha.Pc.v1489, CFSG.KD.Fi24Alpha.Pc.v1490]
theorem CFSG.KD.Fi24Alpha.Pc.p1489 : Nat.beq (runC AR SD 1485 (ckL CFSG.KD.Fi24Alpha.Pc.l1491) 2 1489 CFSG.KD.Fi24Alpha.Pc.l1489) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1491 : Nat := CFSG.KD.Fi24Alpha.KV10 38
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1492 : Nat := CFSG.KD.Fi24Alpha.KV10 39
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1493 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1485, CFSG.KD.Fi24Alpha.Pc.v1486, CFSG.KD.Fi24Alpha.Pc.v1487, CFSG.KD.Fi24Alpha.Pc.v1488, CFSG.KD.Fi24Alpha.Pc.v1489, CFSG.KD.Fi24Alpha.Pc.v1490, CFSG.KD.Fi24Alpha.Pc.v1491, CFSG.KD.Fi24Alpha.Pc.v1492]
theorem CFSG.KD.Fi24Alpha.Pc.p1491 : Nat.beq (runC AR SD 1485 (ckL CFSG.KD.Fi24Alpha.Pc.l1493) 2 1491 CFSG.KD.Fi24Alpha.Pc.l1491) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1493 : Nat := CFSG.KD.Fi24Alpha.KV10 40
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1494 : Nat := CFSG.KD.Fi24Alpha.KV10 41
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1495 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1485, CFSG.KD.Fi24Alpha.Pc.v1486, CFSG.KD.Fi24Alpha.Pc.v1487, CFSG.KD.Fi24Alpha.Pc.v1488, CFSG.KD.Fi24Alpha.Pc.v1489, CFSG.KD.Fi24Alpha.Pc.v1490, CFSG.KD.Fi24Alpha.Pc.v1491, CFSG.KD.Fi24Alpha.Pc.v1492, CFSG.KD.Fi24Alpha.Pc.v1493, CFSG.KD.Fi24Alpha.Pc.v1494]
theorem CFSG.KD.Fi24Alpha.Pc.p1493 : Nat.beq (runC AR SD 1485 (ckL CFSG.KD.Fi24Alpha.Pc.l1495) 2 1493 CFSG.KD.Fi24Alpha.Pc.l1493) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1495 : Nat := CFSG.KD.Fi24Alpha.KV10 42
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1496 : Nat := CFSG.KD.Fi24Alpha.KV10 43
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1497 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1485, CFSG.KD.Fi24Alpha.Pc.v1486, CFSG.KD.Fi24Alpha.Pc.v1487, CFSG.KD.Fi24Alpha.Pc.v1488, CFSG.KD.Fi24Alpha.Pc.v1489, CFSG.KD.Fi24Alpha.Pc.v1490, CFSG.KD.Fi24Alpha.Pc.v1491, CFSG.KD.Fi24Alpha.Pc.v1492, CFSG.KD.Fi24Alpha.Pc.v1493, CFSG.KD.Fi24Alpha.Pc.v1494, CFSG.KD.Fi24Alpha.Pc.v1495, CFSG.KD.Fi24Alpha.Pc.v1496]
theorem CFSG.KD.Fi24Alpha.Pc.p1495 : Nat.beq (runC AR SD 1485 (ckL CFSG.KD.Fi24Alpha.Pc.l1497) 2 1495 CFSG.KD.Fi24Alpha.Pc.l1495) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1497 : Nat := CFSG.KD.Fi24Alpha.KV10 44
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1498 : Nat := CFSG.KD.Fi24Alpha.KV10 45
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1499 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1485, CFSG.KD.Fi24Alpha.Pc.v1486, CFSG.KD.Fi24Alpha.Pc.v1487, CFSG.KD.Fi24Alpha.Pc.v1488, CFSG.KD.Fi24Alpha.Pc.v1489, CFSG.KD.Fi24Alpha.Pc.v1490, CFSG.KD.Fi24Alpha.Pc.v1491, CFSG.KD.Fi24Alpha.Pc.v1492, CFSG.KD.Fi24Alpha.Pc.v1493, CFSG.KD.Fi24Alpha.Pc.v1494, CFSG.KD.Fi24Alpha.Pc.v1495, CFSG.KD.Fi24Alpha.Pc.v1496, CFSG.KD.Fi24Alpha.Pc.v1497, CFSG.KD.Fi24Alpha.Pc.v1498]
theorem CFSG.KD.Fi24Alpha.Pc.p1497 : Nat.beq (runC AR SD 1485 (ckL CFSG.KD.Fi24Alpha.Pc.l1499) 2 1497 CFSG.KD.Fi24Alpha.Pc.l1497) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1499 : Nat := CFSG.KD.Fi24Alpha.KV10 46
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1500 : Nat := CFSG.KD.Fi24Alpha.KV10 47
theorem CFSG.KD.Fi24Alpha.Pc.f102 : Nat.beq (runC AR SD 1485 (finC AR SD (nat_lit 102) 1485 1501) 2 1499 CFSG.KD.Fi24Alpha.Pc.l1499) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk102 : chk (nat_lit 102) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 102) (lo := 1485) (hi := 1501) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1487) CFSG.KD.Fi24Alpha.Pc.p1485 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1489) CFSG.KD.Fi24Alpha.Pc.p1487 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1491) CFSG.KD.Fi24Alpha.Pc.p1489 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1493) CFSG.KD.Fi24Alpha.Pc.p1491 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1495) CFSG.KD.Fi24Alpha.Pc.p1493 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1497) CFSG.KD.Fi24Alpha.Pc.p1495 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1499) CFSG.KD.Fi24Alpha.Pc.p1497 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f102

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1501 : Nat := CFSG.KD.Fi24Alpha.KV10 48
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1502 : Nat := CFSG.KD.Fi24Alpha.KV10 49
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1503 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1501, CFSG.KD.Fi24Alpha.Pc.v1502]
theorem CFSG.KD.Fi24Alpha.Pc.p1501 : Nat.beq (runC AR SD 1501 (ckL CFSG.KD.Fi24Alpha.Pc.l1503) 2 1501 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1503 : Nat := CFSG.KD.Fi24Alpha.KV10 50
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1504 : Nat := CFSG.KD.Fi24Alpha.KV10 51
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1505 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1501, CFSG.KD.Fi24Alpha.Pc.v1502, CFSG.KD.Fi24Alpha.Pc.v1503, CFSG.KD.Fi24Alpha.Pc.v1504]
theorem CFSG.KD.Fi24Alpha.Pc.p1503 : Nat.beq (runC AR SD 1501 (ckL CFSG.KD.Fi24Alpha.Pc.l1505) 2 1503 CFSG.KD.Fi24Alpha.Pc.l1503) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1505 : Nat := CFSG.KD.Fi24Alpha.KV10 52
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1506 : Nat := CFSG.KD.Fi24Alpha.KV10 53
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1507 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1501, CFSG.KD.Fi24Alpha.Pc.v1502, CFSG.KD.Fi24Alpha.Pc.v1503, CFSG.KD.Fi24Alpha.Pc.v1504, CFSG.KD.Fi24Alpha.Pc.v1505, CFSG.KD.Fi24Alpha.Pc.v1506]
theorem CFSG.KD.Fi24Alpha.Pc.p1505 : Nat.beq (runC AR SD 1501 (ckL CFSG.KD.Fi24Alpha.Pc.l1507) 2 1505 CFSG.KD.Fi24Alpha.Pc.l1505) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1507 : Nat := CFSG.KD.Fi24Alpha.KV10 54
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1508 : Nat := CFSG.KD.Fi24Alpha.KV10 55
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1509 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1501, CFSG.KD.Fi24Alpha.Pc.v1502, CFSG.KD.Fi24Alpha.Pc.v1503, CFSG.KD.Fi24Alpha.Pc.v1504, CFSG.KD.Fi24Alpha.Pc.v1505, CFSG.KD.Fi24Alpha.Pc.v1506, CFSG.KD.Fi24Alpha.Pc.v1507, CFSG.KD.Fi24Alpha.Pc.v1508]
theorem CFSG.KD.Fi24Alpha.Pc.p1507 : Nat.beq (runC AR SD 1501 (ckL CFSG.KD.Fi24Alpha.Pc.l1509) 2 1507 CFSG.KD.Fi24Alpha.Pc.l1507) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1509 : Nat := CFSG.KD.Fi24Alpha.KV10 56
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1510 : Nat := CFSG.KD.Fi24Alpha.KV10 57
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1511 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1501, CFSG.KD.Fi24Alpha.Pc.v1502, CFSG.KD.Fi24Alpha.Pc.v1503, CFSG.KD.Fi24Alpha.Pc.v1504, CFSG.KD.Fi24Alpha.Pc.v1505, CFSG.KD.Fi24Alpha.Pc.v1506, CFSG.KD.Fi24Alpha.Pc.v1507, CFSG.KD.Fi24Alpha.Pc.v1508, CFSG.KD.Fi24Alpha.Pc.v1509, CFSG.KD.Fi24Alpha.Pc.v1510]
theorem CFSG.KD.Fi24Alpha.Pc.p1509 : Nat.beq (runC AR SD 1501 (ckL CFSG.KD.Fi24Alpha.Pc.l1511) 2 1509 CFSG.KD.Fi24Alpha.Pc.l1509) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1511 : Nat := CFSG.KD.Fi24Alpha.KV10 58
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1512 : Nat := CFSG.KD.Fi24Alpha.KV10 59
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1513 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1501, CFSG.KD.Fi24Alpha.Pc.v1502, CFSG.KD.Fi24Alpha.Pc.v1503, CFSG.KD.Fi24Alpha.Pc.v1504, CFSG.KD.Fi24Alpha.Pc.v1505, CFSG.KD.Fi24Alpha.Pc.v1506, CFSG.KD.Fi24Alpha.Pc.v1507, CFSG.KD.Fi24Alpha.Pc.v1508, CFSG.KD.Fi24Alpha.Pc.v1509, CFSG.KD.Fi24Alpha.Pc.v1510, CFSG.KD.Fi24Alpha.Pc.v1511, CFSG.KD.Fi24Alpha.Pc.v1512]
theorem CFSG.KD.Fi24Alpha.Pc.p1511 : Nat.beq (runC AR SD 1501 (ckL CFSG.KD.Fi24Alpha.Pc.l1513) 2 1511 CFSG.KD.Fi24Alpha.Pc.l1511) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1513 : Nat := CFSG.KD.Fi24Alpha.KV10 60
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1514 : Nat := CFSG.KD.Fi24Alpha.KV10 61
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1515 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1501, CFSG.KD.Fi24Alpha.Pc.v1502, CFSG.KD.Fi24Alpha.Pc.v1503, CFSG.KD.Fi24Alpha.Pc.v1504, CFSG.KD.Fi24Alpha.Pc.v1505, CFSG.KD.Fi24Alpha.Pc.v1506, CFSG.KD.Fi24Alpha.Pc.v1507, CFSG.KD.Fi24Alpha.Pc.v1508, CFSG.KD.Fi24Alpha.Pc.v1509, CFSG.KD.Fi24Alpha.Pc.v1510, CFSG.KD.Fi24Alpha.Pc.v1511, CFSG.KD.Fi24Alpha.Pc.v1512, CFSG.KD.Fi24Alpha.Pc.v1513, CFSG.KD.Fi24Alpha.Pc.v1514]
theorem CFSG.KD.Fi24Alpha.Pc.p1513 : Nat.beq (runC AR SD 1501 (ckL CFSG.KD.Fi24Alpha.Pc.l1515) 2 1513 CFSG.KD.Fi24Alpha.Pc.l1513) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1515 : Nat := CFSG.KD.Fi24Alpha.KV10 62
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1516 : Nat := CFSG.KD.Fi24Alpha.KV10 63
theorem CFSG.KD.Fi24Alpha.Pc.f103 : Nat.beq (runC AR SD 1501 (finC AR SD (nat_lit 103) 1501 1517) 2 1515 CFSG.KD.Fi24Alpha.Pc.l1515) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk103 : chk (nat_lit 103) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 103) (lo := 1501) (hi := 1517) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1503) CFSG.KD.Fi24Alpha.Pc.p1501 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1505) CFSG.KD.Fi24Alpha.Pc.p1503 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1507) CFSG.KD.Fi24Alpha.Pc.p1505 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1509) CFSG.KD.Fi24Alpha.Pc.p1507 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1511) CFSG.KD.Fi24Alpha.Pc.p1509 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1513) CFSG.KD.Fi24Alpha.Pc.p1511 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1515) CFSG.KD.Fi24Alpha.Pc.p1513 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f103

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1517 : Nat := CFSG.KD.Fi24Alpha.KV10 64
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1518 : Nat := CFSG.KD.Fi24Alpha.KV10 65
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1519 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1517, CFSG.KD.Fi24Alpha.Pc.v1518]
theorem CFSG.KD.Fi24Alpha.Pc.p1517 : Nat.beq (runC AR SD 1517 (ckL CFSG.KD.Fi24Alpha.Pc.l1519) 2 1517 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1519 : Nat := CFSG.KD.Fi24Alpha.KV10 66
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1520 : Nat := CFSG.KD.Fi24Alpha.KV10 67
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1521 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1517, CFSG.KD.Fi24Alpha.Pc.v1518, CFSG.KD.Fi24Alpha.Pc.v1519, CFSG.KD.Fi24Alpha.Pc.v1520]
theorem CFSG.KD.Fi24Alpha.Pc.p1519 : Nat.beq (runC AR SD 1517 (ckL CFSG.KD.Fi24Alpha.Pc.l1521) 2 1519 CFSG.KD.Fi24Alpha.Pc.l1519) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1521 : Nat := CFSG.KD.Fi24Alpha.KV10 68
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1522 : Nat := CFSG.KD.Fi24Alpha.KV10 69
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1523 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1517, CFSG.KD.Fi24Alpha.Pc.v1518, CFSG.KD.Fi24Alpha.Pc.v1519, CFSG.KD.Fi24Alpha.Pc.v1520, CFSG.KD.Fi24Alpha.Pc.v1521, CFSG.KD.Fi24Alpha.Pc.v1522]
theorem CFSG.KD.Fi24Alpha.Pc.p1521 : Nat.beq (runC AR SD 1517 (ckL CFSG.KD.Fi24Alpha.Pc.l1523) 2 1521 CFSG.KD.Fi24Alpha.Pc.l1521) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1523 : Nat := CFSG.KD.Fi24Alpha.KV10 70
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1524 : Nat := CFSG.KD.Fi24Alpha.KV10 71
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1525 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1517, CFSG.KD.Fi24Alpha.Pc.v1518, CFSG.KD.Fi24Alpha.Pc.v1519, CFSG.KD.Fi24Alpha.Pc.v1520, CFSG.KD.Fi24Alpha.Pc.v1521, CFSG.KD.Fi24Alpha.Pc.v1522, CFSG.KD.Fi24Alpha.Pc.v1523, CFSG.KD.Fi24Alpha.Pc.v1524]
theorem CFSG.KD.Fi24Alpha.Pc.p1523 : Nat.beq (runC AR SD 1517 (ckL CFSG.KD.Fi24Alpha.Pc.l1525) 2 1523 CFSG.KD.Fi24Alpha.Pc.l1523) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1525 : Nat := CFSG.KD.Fi24Alpha.KV10 72
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1526 : Nat := CFSG.KD.Fi24Alpha.KV10 73
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1527 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1517, CFSG.KD.Fi24Alpha.Pc.v1518, CFSG.KD.Fi24Alpha.Pc.v1519, CFSG.KD.Fi24Alpha.Pc.v1520, CFSG.KD.Fi24Alpha.Pc.v1521, CFSG.KD.Fi24Alpha.Pc.v1522, CFSG.KD.Fi24Alpha.Pc.v1523, CFSG.KD.Fi24Alpha.Pc.v1524, CFSG.KD.Fi24Alpha.Pc.v1525, CFSG.KD.Fi24Alpha.Pc.v1526]
theorem CFSG.KD.Fi24Alpha.Pc.p1525 : Nat.beq (runC AR SD 1517 (ckL CFSG.KD.Fi24Alpha.Pc.l1527) 2 1525 CFSG.KD.Fi24Alpha.Pc.l1525) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1527 : Nat := CFSG.KD.Fi24Alpha.KV10 74
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1528 : Nat := CFSG.KD.Fi24Alpha.KV10 75
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1529 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1517, CFSG.KD.Fi24Alpha.Pc.v1518, CFSG.KD.Fi24Alpha.Pc.v1519, CFSG.KD.Fi24Alpha.Pc.v1520, CFSG.KD.Fi24Alpha.Pc.v1521, CFSG.KD.Fi24Alpha.Pc.v1522, CFSG.KD.Fi24Alpha.Pc.v1523, CFSG.KD.Fi24Alpha.Pc.v1524, CFSG.KD.Fi24Alpha.Pc.v1525, CFSG.KD.Fi24Alpha.Pc.v1526, CFSG.KD.Fi24Alpha.Pc.v1527, CFSG.KD.Fi24Alpha.Pc.v1528]
theorem CFSG.KD.Fi24Alpha.Pc.p1527 : Nat.beq (runC AR SD 1517 (ckL CFSG.KD.Fi24Alpha.Pc.l1529) 2 1527 CFSG.KD.Fi24Alpha.Pc.l1527) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1529 : Nat := CFSG.KD.Fi24Alpha.KV10 76
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1530 : Nat := CFSG.KD.Fi24Alpha.KV10 77
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1531 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1517, CFSG.KD.Fi24Alpha.Pc.v1518, CFSG.KD.Fi24Alpha.Pc.v1519, CFSG.KD.Fi24Alpha.Pc.v1520, CFSG.KD.Fi24Alpha.Pc.v1521, CFSG.KD.Fi24Alpha.Pc.v1522, CFSG.KD.Fi24Alpha.Pc.v1523, CFSG.KD.Fi24Alpha.Pc.v1524, CFSG.KD.Fi24Alpha.Pc.v1525, CFSG.KD.Fi24Alpha.Pc.v1526, CFSG.KD.Fi24Alpha.Pc.v1527, CFSG.KD.Fi24Alpha.Pc.v1528, CFSG.KD.Fi24Alpha.Pc.v1529, CFSG.KD.Fi24Alpha.Pc.v1530]
theorem CFSG.KD.Fi24Alpha.Pc.p1529 : Nat.beq (runC AR SD 1517 (ckL CFSG.KD.Fi24Alpha.Pc.l1531) 2 1529 CFSG.KD.Fi24Alpha.Pc.l1529) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1531 : Nat := CFSG.KD.Fi24Alpha.KV10 78
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1532 : Nat := CFSG.KD.Fi24Alpha.KV10 79
theorem CFSG.KD.Fi24Alpha.Pc.f104 : Nat.beq (runC AR SD 1517 (finC AR SD (nat_lit 104) 1517 1533) 2 1531 CFSG.KD.Fi24Alpha.Pc.l1531) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk104 : chk (nat_lit 104) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 104) (lo := 1517) (hi := 1533) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1519) CFSG.KD.Fi24Alpha.Pc.p1517 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1521) CFSG.KD.Fi24Alpha.Pc.p1519 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1523) CFSG.KD.Fi24Alpha.Pc.p1521 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1525) CFSG.KD.Fi24Alpha.Pc.p1523 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1527) CFSG.KD.Fi24Alpha.Pc.p1525 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1529) CFSG.KD.Fi24Alpha.Pc.p1527 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1531) CFSG.KD.Fi24Alpha.Pc.p1529 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f104

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1533 : Nat := CFSG.KD.Fi24Alpha.KV10 80
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1534 : Nat := CFSG.KD.Fi24Alpha.KV10 81
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1535 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1533, CFSG.KD.Fi24Alpha.Pc.v1534]
theorem CFSG.KD.Fi24Alpha.Pc.p1533 : Nat.beq (runC AR SD 1533 (ckL CFSG.KD.Fi24Alpha.Pc.l1535) 2 1533 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1535 : Nat := CFSG.KD.Fi24Alpha.KV10 82
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1536 : Nat := CFSG.KD.Fi24Alpha.KV10 83
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1537 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1533, CFSG.KD.Fi24Alpha.Pc.v1534, CFSG.KD.Fi24Alpha.Pc.v1535, CFSG.KD.Fi24Alpha.Pc.v1536]
theorem CFSG.KD.Fi24Alpha.Pc.p1535 : Nat.beq (runC AR SD 1533 (ckL CFSG.KD.Fi24Alpha.Pc.l1537) 2 1535 CFSG.KD.Fi24Alpha.Pc.l1535) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1537 : Nat := CFSG.KD.Fi24Alpha.KV10 84
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1538 : Nat := CFSG.KD.Fi24Alpha.KV10 85
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1539 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1533, CFSG.KD.Fi24Alpha.Pc.v1534, CFSG.KD.Fi24Alpha.Pc.v1535, CFSG.KD.Fi24Alpha.Pc.v1536, CFSG.KD.Fi24Alpha.Pc.v1537, CFSG.KD.Fi24Alpha.Pc.v1538]
theorem CFSG.KD.Fi24Alpha.Pc.p1537 : Nat.beq (runC AR SD 1533 (ckL CFSG.KD.Fi24Alpha.Pc.l1539) 2 1537 CFSG.KD.Fi24Alpha.Pc.l1537) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1539 : Nat := CFSG.KD.Fi24Alpha.KV10 86
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1540 : Nat := CFSG.KD.Fi24Alpha.KV10 87
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1541 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1533, CFSG.KD.Fi24Alpha.Pc.v1534, CFSG.KD.Fi24Alpha.Pc.v1535, CFSG.KD.Fi24Alpha.Pc.v1536, CFSG.KD.Fi24Alpha.Pc.v1537, CFSG.KD.Fi24Alpha.Pc.v1538, CFSG.KD.Fi24Alpha.Pc.v1539, CFSG.KD.Fi24Alpha.Pc.v1540]
theorem CFSG.KD.Fi24Alpha.Pc.p1539 : Nat.beq (runC AR SD 1533 (ckL CFSG.KD.Fi24Alpha.Pc.l1541) 2 1539 CFSG.KD.Fi24Alpha.Pc.l1539) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1541 : Nat := CFSG.KD.Fi24Alpha.KV10 88
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1542 : Nat := CFSG.KD.Fi24Alpha.KV10 89
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1543 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1533, CFSG.KD.Fi24Alpha.Pc.v1534, CFSG.KD.Fi24Alpha.Pc.v1535, CFSG.KD.Fi24Alpha.Pc.v1536, CFSG.KD.Fi24Alpha.Pc.v1537, CFSG.KD.Fi24Alpha.Pc.v1538, CFSG.KD.Fi24Alpha.Pc.v1539, CFSG.KD.Fi24Alpha.Pc.v1540, CFSG.KD.Fi24Alpha.Pc.v1541, CFSG.KD.Fi24Alpha.Pc.v1542]
theorem CFSG.KD.Fi24Alpha.Pc.p1541 : Nat.beq (runC AR SD 1533 (ckL CFSG.KD.Fi24Alpha.Pc.l1543) 2 1541 CFSG.KD.Fi24Alpha.Pc.l1541) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1543 : Nat := CFSG.KD.Fi24Alpha.KV10 90
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1544 : Nat := CFSG.KD.Fi24Alpha.KV10 91
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1545 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1533, CFSG.KD.Fi24Alpha.Pc.v1534, CFSG.KD.Fi24Alpha.Pc.v1535, CFSG.KD.Fi24Alpha.Pc.v1536, CFSG.KD.Fi24Alpha.Pc.v1537, CFSG.KD.Fi24Alpha.Pc.v1538, CFSG.KD.Fi24Alpha.Pc.v1539, CFSG.KD.Fi24Alpha.Pc.v1540, CFSG.KD.Fi24Alpha.Pc.v1541, CFSG.KD.Fi24Alpha.Pc.v1542, CFSG.KD.Fi24Alpha.Pc.v1543, CFSG.KD.Fi24Alpha.Pc.v1544]
theorem CFSG.KD.Fi24Alpha.Pc.p1543 : Nat.beq (runC AR SD 1533 (ckL CFSG.KD.Fi24Alpha.Pc.l1545) 2 1543 CFSG.KD.Fi24Alpha.Pc.l1543) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1545 : Nat := CFSG.KD.Fi24Alpha.KV10 92
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1546 : Nat := CFSG.KD.Fi24Alpha.KV10 93
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1547 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1533, CFSG.KD.Fi24Alpha.Pc.v1534, CFSG.KD.Fi24Alpha.Pc.v1535, CFSG.KD.Fi24Alpha.Pc.v1536, CFSG.KD.Fi24Alpha.Pc.v1537, CFSG.KD.Fi24Alpha.Pc.v1538, CFSG.KD.Fi24Alpha.Pc.v1539, CFSG.KD.Fi24Alpha.Pc.v1540, CFSG.KD.Fi24Alpha.Pc.v1541, CFSG.KD.Fi24Alpha.Pc.v1542, CFSG.KD.Fi24Alpha.Pc.v1543, CFSG.KD.Fi24Alpha.Pc.v1544, CFSG.KD.Fi24Alpha.Pc.v1545, CFSG.KD.Fi24Alpha.Pc.v1546]
theorem CFSG.KD.Fi24Alpha.Pc.p1545 : Nat.beq (runC AR SD 1533 (ckL CFSG.KD.Fi24Alpha.Pc.l1547) 2 1545 CFSG.KD.Fi24Alpha.Pc.l1545) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1547 : Nat := CFSG.KD.Fi24Alpha.KV10 94
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1548 : Nat := CFSG.KD.Fi24Alpha.KV10 95
theorem CFSG.KD.Fi24Alpha.Pc.f105 : Nat.beq (runC AR SD 1533 (finC AR SD (nat_lit 105) 1533 1549) 2 1547 CFSG.KD.Fi24Alpha.Pc.l1547) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk105 : chk (nat_lit 105) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 105) (lo := 1533) (hi := 1549) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1535) CFSG.KD.Fi24Alpha.Pc.p1533 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1537) CFSG.KD.Fi24Alpha.Pc.p1535 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1539) CFSG.KD.Fi24Alpha.Pc.p1537 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1541) CFSG.KD.Fi24Alpha.Pc.p1539 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1543) CFSG.KD.Fi24Alpha.Pc.p1541 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1545) CFSG.KD.Fi24Alpha.Pc.p1543 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1547) CFSG.KD.Fi24Alpha.Pc.p1545 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f105

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1549 : Nat := CFSG.KD.Fi24Alpha.KV10 96
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1550 : Nat := CFSG.KD.Fi24Alpha.KV10 97
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1551 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1549, CFSG.KD.Fi24Alpha.Pc.v1550]
theorem CFSG.KD.Fi24Alpha.Pc.p1549 : Nat.beq (runC AR SD 1549 (ckL CFSG.KD.Fi24Alpha.Pc.l1551) 2 1549 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1551 : Nat := CFSG.KD.Fi24Alpha.KV10 98
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1552 : Nat := CFSG.KD.Fi24Alpha.KV10 99
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1553 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1549, CFSG.KD.Fi24Alpha.Pc.v1550, CFSG.KD.Fi24Alpha.Pc.v1551, CFSG.KD.Fi24Alpha.Pc.v1552]
theorem CFSG.KD.Fi24Alpha.Pc.p1551 : Nat.beq (runC AR SD 1549 (ckL CFSG.KD.Fi24Alpha.Pc.l1553) 2 1551 CFSG.KD.Fi24Alpha.Pc.l1551) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1553 : Nat := CFSG.KD.Fi24Alpha.KV10 100
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1554 : Nat := CFSG.KD.Fi24Alpha.KV10 101
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1555 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1549, CFSG.KD.Fi24Alpha.Pc.v1550, CFSG.KD.Fi24Alpha.Pc.v1551, CFSG.KD.Fi24Alpha.Pc.v1552, CFSG.KD.Fi24Alpha.Pc.v1553, CFSG.KD.Fi24Alpha.Pc.v1554]
theorem CFSG.KD.Fi24Alpha.Pc.p1553 : Nat.beq (runC AR SD 1549 (ckL CFSG.KD.Fi24Alpha.Pc.l1555) 2 1553 CFSG.KD.Fi24Alpha.Pc.l1553) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1555 : Nat := CFSG.KD.Fi24Alpha.KV10 102
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1556 : Nat := CFSG.KD.Fi24Alpha.KV10 103
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1557 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1549, CFSG.KD.Fi24Alpha.Pc.v1550, CFSG.KD.Fi24Alpha.Pc.v1551, CFSG.KD.Fi24Alpha.Pc.v1552, CFSG.KD.Fi24Alpha.Pc.v1553, CFSG.KD.Fi24Alpha.Pc.v1554, CFSG.KD.Fi24Alpha.Pc.v1555, CFSG.KD.Fi24Alpha.Pc.v1556]
theorem CFSG.KD.Fi24Alpha.Pc.p1555 : Nat.beq (runC AR SD 1549 (ckL CFSG.KD.Fi24Alpha.Pc.l1557) 2 1555 CFSG.KD.Fi24Alpha.Pc.l1555) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1557 : Nat := CFSG.KD.Fi24Alpha.KV10 104
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1558 : Nat := CFSG.KD.Fi24Alpha.KV10 105
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1559 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1549, CFSG.KD.Fi24Alpha.Pc.v1550, CFSG.KD.Fi24Alpha.Pc.v1551, CFSG.KD.Fi24Alpha.Pc.v1552, CFSG.KD.Fi24Alpha.Pc.v1553, CFSG.KD.Fi24Alpha.Pc.v1554, CFSG.KD.Fi24Alpha.Pc.v1555, CFSG.KD.Fi24Alpha.Pc.v1556, CFSG.KD.Fi24Alpha.Pc.v1557, CFSG.KD.Fi24Alpha.Pc.v1558]
theorem CFSG.KD.Fi24Alpha.Pc.p1557 : Nat.beq (runC AR SD 1549 (ckL CFSG.KD.Fi24Alpha.Pc.l1559) 2 1557 CFSG.KD.Fi24Alpha.Pc.l1557) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1559 : Nat := CFSG.KD.Fi24Alpha.KV10 106
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1560 : Nat := CFSG.KD.Fi24Alpha.KV10 107
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1561 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1549, CFSG.KD.Fi24Alpha.Pc.v1550, CFSG.KD.Fi24Alpha.Pc.v1551, CFSG.KD.Fi24Alpha.Pc.v1552, CFSG.KD.Fi24Alpha.Pc.v1553, CFSG.KD.Fi24Alpha.Pc.v1554, CFSG.KD.Fi24Alpha.Pc.v1555, CFSG.KD.Fi24Alpha.Pc.v1556, CFSG.KD.Fi24Alpha.Pc.v1557, CFSG.KD.Fi24Alpha.Pc.v1558, CFSG.KD.Fi24Alpha.Pc.v1559, CFSG.KD.Fi24Alpha.Pc.v1560]
theorem CFSG.KD.Fi24Alpha.Pc.p1559 : Nat.beq (runC AR SD 1549 (ckL CFSG.KD.Fi24Alpha.Pc.l1561) 2 1559 CFSG.KD.Fi24Alpha.Pc.l1559) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1561 : Nat := CFSG.KD.Fi24Alpha.KV10 108
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1562 : Nat := CFSG.KD.Fi24Alpha.KV10 109
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1563 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1549, CFSG.KD.Fi24Alpha.Pc.v1550, CFSG.KD.Fi24Alpha.Pc.v1551, CFSG.KD.Fi24Alpha.Pc.v1552, CFSG.KD.Fi24Alpha.Pc.v1553, CFSG.KD.Fi24Alpha.Pc.v1554, CFSG.KD.Fi24Alpha.Pc.v1555, CFSG.KD.Fi24Alpha.Pc.v1556, CFSG.KD.Fi24Alpha.Pc.v1557, CFSG.KD.Fi24Alpha.Pc.v1558, CFSG.KD.Fi24Alpha.Pc.v1559, CFSG.KD.Fi24Alpha.Pc.v1560, CFSG.KD.Fi24Alpha.Pc.v1561, CFSG.KD.Fi24Alpha.Pc.v1562]
theorem CFSG.KD.Fi24Alpha.Pc.p1561 : Nat.beq (runC AR SD 1549 (ckL CFSG.KD.Fi24Alpha.Pc.l1563) 2 1561 CFSG.KD.Fi24Alpha.Pc.l1561) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1563 : Nat := CFSG.KD.Fi24Alpha.KV10 110
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1564 : Nat := CFSG.KD.Fi24Alpha.KV10 111
theorem CFSG.KD.Fi24Alpha.Pc.f106 : Nat.beq (runC AR SD 1549 (finC AR SD (nat_lit 106) 1549 1565) 2 1563 CFSG.KD.Fi24Alpha.Pc.l1563) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk106 : chk (nat_lit 106) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 106) (lo := 1549) (hi := 1565) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1551) CFSG.KD.Fi24Alpha.Pc.p1549 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1553) CFSG.KD.Fi24Alpha.Pc.p1551 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1555) CFSG.KD.Fi24Alpha.Pc.p1553 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1557) CFSG.KD.Fi24Alpha.Pc.p1555 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1559) CFSG.KD.Fi24Alpha.Pc.p1557 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1561) CFSG.KD.Fi24Alpha.Pc.p1559 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1563) CFSG.KD.Fi24Alpha.Pc.p1561 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f106

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1565 : Nat := CFSG.KD.Fi24Alpha.KV10 112
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1566 : Nat := CFSG.KD.Fi24Alpha.KV10 113
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1567 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1565, CFSG.KD.Fi24Alpha.Pc.v1566]
theorem CFSG.KD.Fi24Alpha.Pc.p1565 : Nat.beq (runC AR SD 1565 (ckL CFSG.KD.Fi24Alpha.Pc.l1567) 2 1565 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1567 : Nat := CFSG.KD.Fi24Alpha.KV10 114
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1568 : Nat := CFSG.KD.Fi24Alpha.KV10 115
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1569 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1565, CFSG.KD.Fi24Alpha.Pc.v1566, CFSG.KD.Fi24Alpha.Pc.v1567, CFSG.KD.Fi24Alpha.Pc.v1568]
theorem CFSG.KD.Fi24Alpha.Pc.p1567 : Nat.beq (runC AR SD 1565 (ckL CFSG.KD.Fi24Alpha.Pc.l1569) 2 1567 CFSG.KD.Fi24Alpha.Pc.l1567) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1569 : Nat := CFSG.KD.Fi24Alpha.KV10 116
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1570 : Nat := CFSG.KD.Fi24Alpha.KV10 117
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1571 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1565, CFSG.KD.Fi24Alpha.Pc.v1566, CFSG.KD.Fi24Alpha.Pc.v1567, CFSG.KD.Fi24Alpha.Pc.v1568, CFSG.KD.Fi24Alpha.Pc.v1569, CFSG.KD.Fi24Alpha.Pc.v1570]
theorem CFSG.KD.Fi24Alpha.Pc.p1569 : Nat.beq (runC AR SD 1565 (ckL CFSG.KD.Fi24Alpha.Pc.l1571) 2 1569 CFSG.KD.Fi24Alpha.Pc.l1569) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1571 : Nat := CFSG.KD.Fi24Alpha.KV10 118
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1572 : Nat := CFSG.KD.Fi24Alpha.KV10 119
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1573 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1565, CFSG.KD.Fi24Alpha.Pc.v1566, CFSG.KD.Fi24Alpha.Pc.v1567, CFSG.KD.Fi24Alpha.Pc.v1568, CFSG.KD.Fi24Alpha.Pc.v1569, CFSG.KD.Fi24Alpha.Pc.v1570, CFSG.KD.Fi24Alpha.Pc.v1571, CFSG.KD.Fi24Alpha.Pc.v1572]
theorem CFSG.KD.Fi24Alpha.Pc.p1571 : Nat.beq (runC AR SD 1565 (ckL CFSG.KD.Fi24Alpha.Pc.l1573) 2 1571 CFSG.KD.Fi24Alpha.Pc.l1571) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1573 : Nat := CFSG.KD.Fi24Alpha.KV10 120
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1574 : Nat := CFSG.KD.Fi24Alpha.KV10 121
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1575 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1565, CFSG.KD.Fi24Alpha.Pc.v1566, CFSG.KD.Fi24Alpha.Pc.v1567, CFSG.KD.Fi24Alpha.Pc.v1568, CFSG.KD.Fi24Alpha.Pc.v1569, CFSG.KD.Fi24Alpha.Pc.v1570, CFSG.KD.Fi24Alpha.Pc.v1571, CFSG.KD.Fi24Alpha.Pc.v1572, CFSG.KD.Fi24Alpha.Pc.v1573, CFSG.KD.Fi24Alpha.Pc.v1574]
theorem CFSG.KD.Fi24Alpha.Pc.p1573 : Nat.beq (runC AR SD 1565 (ckL CFSG.KD.Fi24Alpha.Pc.l1575) 2 1573 CFSG.KD.Fi24Alpha.Pc.l1573) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1575 : Nat := CFSG.KD.Fi24Alpha.KV10 122
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1576 : Nat := CFSG.KD.Fi24Alpha.KV10 123
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1577 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1565, CFSG.KD.Fi24Alpha.Pc.v1566, CFSG.KD.Fi24Alpha.Pc.v1567, CFSG.KD.Fi24Alpha.Pc.v1568, CFSG.KD.Fi24Alpha.Pc.v1569, CFSG.KD.Fi24Alpha.Pc.v1570, CFSG.KD.Fi24Alpha.Pc.v1571, CFSG.KD.Fi24Alpha.Pc.v1572, CFSG.KD.Fi24Alpha.Pc.v1573, CFSG.KD.Fi24Alpha.Pc.v1574, CFSG.KD.Fi24Alpha.Pc.v1575, CFSG.KD.Fi24Alpha.Pc.v1576]
theorem CFSG.KD.Fi24Alpha.Pc.p1575 : Nat.beq (runC AR SD 1565 (ckL CFSG.KD.Fi24Alpha.Pc.l1577) 2 1575 CFSG.KD.Fi24Alpha.Pc.l1575) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1577 : Nat := CFSG.KD.Fi24Alpha.KV10 124
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1578 : Nat := CFSG.KD.Fi24Alpha.KV10 125
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1579 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1565, CFSG.KD.Fi24Alpha.Pc.v1566, CFSG.KD.Fi24Alpha.Pc.v1567, CFSG.KD.Fi24Alpha.Pc.v1568, CFSG.KD.Fi24Alpha.Pc.v1569, CFSG.KD.Fi24Alpha.Pc.v1570, CFSG.KD.Fi24Alpha.Pc.v1571, CFSG.KD.Fi24Alpha.Pc.v1572, CFSG.KD.Fi24Alpha.Pc.v1573, CFSG.KD.Fi24Alpha.Pc.v1574, CFSG.KD.Fi24Alpha.Pc.v1575, CFSG.KD.Fi24Alpha.Pc.v1576, CFSG.KD.Fi24Alpha.Pc.v1577, CFSG.KD.Fi24Alpha.Pc.v1578]
theorem CFSG.KD.Fi24Alpha.Pc.p1577 : Nat.beq (runC AR SD 1565 (ckL CFSG.KD.Fi24Alpha.Pc.l1579) 2 1577 CFSG.KD.Fi24Alpha.Pc.l1577) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1579 : Nat := CFSG.KD.Fi24Alpha.KV10 126
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1580 : Nat := CFSG.KD.Fi24Alpha.KV10 127
theorem CFSG.KD.Fi24Alpha.Pc.f107 : Nat.beq (runC AR SD 1565 (finC AR SD (nat_lit 107) 1565 1581) 2 1579 CFSG.KD.Fi24Alpha.Pc.l1579) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk107 : chk (nat_lit 107) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 107) (lo := 1565) (hi := 1581) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1567) CFSG.KD.Fi24Alpha.Pc.p1565 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1569) CFSG.KD.Fi24Alpha.Pc.p1567 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1571) CFSG.KD.Fi24Alpha.Pc.p1569 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1573) CFSG.KD.Fi24Alpha.Pc.p1571 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1575) CFSG.KD.Fi24Alpha.Pc.p1573 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1577) CFSG.KD.Fi24Alpha.Pc.p1575 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1579) CFSG.KD.Fi24Alpha.Pc.p1577 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f107

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1581 : Nat := CFSG.KD.Fi24Alpha.KV10 128
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1582 : Nat := CFSG.KD.Fi24Alpha.KV10 129
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1583 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1581, CFSG.KD.Fi24Alpha.Pc.v1582]
theorem CFSG.KD.Fi24Alpha.Pc.p1581 : Nat.beq (runC AR SD 1581 (ckL CFSG.KD.Fi24Alpha.Pc.l1583) 2 1581 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1583 : Nat := CFSG.KD.Fi24Alpha.KV10 130
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1584 : Nat := CFSG.KD.Fi24Alpha.KV10 131
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1585 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1581, CFSG.KD.Fi24Alpha.Pc.v1582, CFSG.KD.Fi24Alpha.Pc.v1583, CFSG.KD.Fi24Alpha.Pc.v1584]
theorem CFSG.KD.Fi24Alpha.Pc.p1583 : Nat.beq (runC AR SD 1581 (ckL CFSG.KD.Fi24Alpha.Pc.l1585) 2 1583 CFSG.KD.Fi24Alpha.Pc.l1583) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1585 : Nat := CFSG.KD.Fi24Alpha.KV10 132
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1586 : Nat := CFSG.KD.Fi24Alpha.KV10 133
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1587 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1581, CFSG.KD.Fi24Alpha.Pc.v1582, CFSG.KD.Fi24Alpha.Pc.v1583, CFSG.KD.Fi24Alpha.Pc.v1584, CFSG.KD.Fi24Alpha.Pc.v1585, CFSG.KD.Fi24Alpha.Pc.v1586]
theorem CFSG.KD.Fi24Alpha.Pc.p1585 : Nat.beq (runC AR SD 1581 (ckL CFSG.KD.Fi24Alpha.Pc.l1587) 2 1585 CFSG.KD.Fi24Alpha.Pc.l1585) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1587 : Nat := CFSG.KD.Fi24Alpha.KV10 134
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1588 : Nat := CFSG.KD.Fi24Alpha.KV10 135
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1589 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1581, CFSG.KD.Fi24Alpha.Pc.v1582, CFSG.KD.Fi24Alpha.Pc.v1583, CFSG.KD.Fi24Alpha.Pc.v1584, CFSG.KD.Fi24Alpha.Pc.v1585, CFSG.KD.Fi24Alpha.Pc.v1586, CFSG.KD.Fi24Alpha.Pc.v1587, CFSG.KD.Fi24Alpha.Pc.v1588]
theorem CFSG.KD.Fi24Alpha.Pc.p1587 : Nat.beq (runC AR SD 1581 (ckL CFSG.KD.Fi24Alpha.Pc.l1589) 2 1587 CFSG.KD.Fi24Alpha.Pc.l1587) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1589 : Nat := CFSG.KD.Fi24Alpha.KV10 136
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1590 : Nat := CFSG.KD.Fi24Alpha.KV10 137
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1591 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1581, CFSG.KD.Fi24Alpha.Pc.v1582, CFSG.KD.Fi24Alpha.Pc.v1583, CFSG.KD.Fi24Alpha.Pc.v1584, CFSG.KD.Fi24Alpha.Pc.v1585, CFSG.KD.Fi24Alpha.Pc.v1586, CFSG.KD.Fi24Alpha.Pc.v1587, CFSG.KD.Fi24Alpha.Pc.v1588, CFSG.KD.Fi24Alpha.Pc.v1589, CFSG.KD.Fi24Alpha.Pc.v1590]
theorem CFSG.KD.Fi24Alpha.Pc.p1589 : Nat.beq (runC AR SD 1581 (ckL CFSG.KD.Fi24Alpha.Pc.l1591) 2 1589 CFSG.KD.Fi24Alpha.Pc.l1589) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1591 : Nat := CFSG.KD.Fi24Alpha.KV10 138
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1592 : Nat := CFSG.KD.Fi24Alpha.KV10 139
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1593 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1581, CFSG.KD.Fi24Alpha.Pc.v1582, CFSG.KD.Fi24Alpha.Pc.v1583, CFSG.KD.Fi24Alpha.Pc.v1584, CFSG.KD.Fi24Alpha.Pc.v1585, CFSG.KD.Fi24Alpha.Pc.v1586, CFSG.KD.Fi24Alpha.Pc.v1587, CFSG.KD.Fi24Alpha.Pc.v1588, CFSG.KD.Fi24Alpha.Pc.v1589, CFSG.KD.Fi24Alpha.Pc.v1590, CFSG.KD.Fi24Alpha.Pc.v1591, CFSG.KD.Fi24Alpha.Pc.v1592]
theorem CFSG.KD.Fi24Alpha.Pc.p1591 : Nat.beq (runC AR SD 1581 (ckL CFSG.KD.Fi24Alpha.Pc.l1593) 2 1591 CFSG.KD.Fi24Alpha.Pc.l1591) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1593 : Nat := CFSG.KD.Fi24Alpha.KV10 140
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1594 : Nat := CFSG.KD.Fi24Alpha.KV10 141
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1595 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1581, CFSG.KD.Fi24Alpha.Pc.v1582, CFSG.KD.Fi24Alpha.Pc.v1583, CFSG.KD.Fi24Alpha.Pc.v1584, CFSG.KD.Fi24Alpha.Pc.v1585, CFSG.KD.Fi24Alpha.Pc.v1586, CFSG.KD.Fi24Alpha.Pc.v1587, CFSG.KD.Fi24Alpha.Pc.v1588, CFSG.KD.Fi24Alpha.Pc.v1589, CFSG.KD.Fi24Alpha.Pc.v1590, CFSG.KD.Fi24Alpha.Pc.v1591, CFSG.KD.Fi24Alpha.Pc.v1592, CFSG.KD.Fi24Alpha.Pc.v1593, CFSG.KD.Fi24Alpha.Pc.v1594]
theorem CFSG.KD.Fi24Alpha.Pc.p1593 : Nat.beq (runC AR SD 1581 (ckL CFSG.KD.Fi24Alpha.Pc.l1595) 2 1593 CFSG.KD.Fi24Alpha.Pc.l1593) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1595 : Nat := CFSG.KD.Fi24Alpha.KV10 142
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1596 : Nat := CFSG.KD.Fi24Alpha.KV10 143
theorem CFSG.KD.Fi24Alpha.Pc.f108 : Nat.beq (runC AR SD 1581 (finC AR SD (nat_lit 108) 1581 1597) 2 1595 CFSG.KD.Fi24Alpha.Pc.l1595) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk108 : chk (nat_lit 108) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 108) (lo := 1581) (hi := 1597) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1583) CFSG.KD.Fi24Alpha.Pc.p1581 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1585) CFSG.KD.Fi24Alpha.Pc.p1583 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1587) CFSG.KD.Fi24Alpha.Pc.p1585 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1589) CFSG.KD.Fi24Alpha.Pc.p1587 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1591) CFSG.KD.Fi24Alpha.Pc.p1589 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1593) CFSG.KD.Fi24Alpha.Pc.p1591 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1595) CFSG.KD.Fi24Alpha.Pc.p1593 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f108

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1597 : Nat := CFSG.KD.Fi24Alpha.KV10 144
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1598 : Nat := CFSG.KD.Fi24Alpha.KV10 145
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1599 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1597, CFSG.KD.Fi24Alpha.Pc.v1598]
theorem CFSG.KD.Fi24Alpha.Pc.p1597 : Nat.beq (runC AR SD 1597 (ckL CFSG.KD.Fi24Alpha.Pc.l1599) 2 1597 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1599 : Nat := CFSG.KD.Fi24Alpha.KV10 146
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1600 : Nat := CFSG.KD.Fi24Alpha.KV10 147
theorem CFSG.KD.Fi24Alpha.Pc.f109 : Nat.beq (runC AR SD 1597 (finC AR SD (nat_lit 109) 1597 1601) 2 1599 CFSG.KD.Fi24Alpha.Pc.l1599) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk109 : chk (nat_lit 109) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 109) (lo := 1597) (hi := 1601) (m := 4) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_seq (m := 4) (m2 := 2) (j2 := 1599) CFSG.KD.Fi24Alpha.Pc.p1597 rfl rfl))).trans CFSG.KD.Fi24Alpha.Pc.f109

end
