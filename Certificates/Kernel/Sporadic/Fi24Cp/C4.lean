module

public import Certificates.Kernel.Sporadic.Fi24Cp.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Cp KV4 "Certificates/Kernel/Sporadic/Fi24Cp/data/v4.bin" 152491 4 21348740 14563274703718966353

public section

open CFSG.KD.Fi24Cp CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v516 : Nat := CFSG.KD.Fi24Cp.KV4 0
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v517 : Nat := CFSG.KD.Fi24Cp.KV4 1
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l518 : List Nat := [CFSG.KD.Fi24Cp.Pc.v516, CFSG.KD.Fi24Cp.Pc.v517]
theorem CFSG.KD.Fi24Cp.Pc.p516 : Nat.beq (runC AR SD 516 (ckL CFSG.KD.Fi24Cp.Pc.l518) 2 516 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v518 : Nat := CFSG.KD.Fi24Cp.KV4 2
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v519 : Nat := CFSG.KD.Fi24Cp.KV4 3
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l520 : List Nat := [CFSG.KD.Fi24Cp.Pc.v516, CFSG.KD.Fi24Cp.Pc.v517, CFSG.KD.Fi24Cp.Pc.v518, CFSG.KD.Fi24Cp.Pc.v519]
theorem CFSG.KD.Fi24Cp.Pc.p518 : Nat.beq (runC AR SD 516 (ckL CFSG.KD.Fi24Cp.Pc.l520) 2 518 CFSG.KD.Fi24Cp.Pc.l518) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v520 : Nat := CFSG.KD.Fi24Cp.KV4 4
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v521 : Nat := CFSG.KD.Fi24Cp.KV4 5
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l522 : List Nat := [CFSG.KD.Fi24Cp.Pc.v516, CFSG.KD.Fi24Cp.Pc.v517, CFSG.KD.Fi24Cp.Pc.v518, CFSG.KD.Fi24Cp.Pc.v519, CFSG.KD.Fi24Cp.Pc.v520, CFSG.KD.Fi24Cp.Pc.v521]
theorem CFSG.KD.Fi24Cp.Pc.p520 : Nat.beq (runC AR SD 516 (ckL CFSG.KD.Fi24Cp.Pc.l522) 2 520 CFSG.KD.Fi24Cp.Pc.l520) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v522 : Nat := CFSG.KD.Fi24Cp.KV4 6
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v523 : Nat := CFSG.KD.Fi24Cp.KV4 7
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l524 : List Nat := [CFSG.KD.Fi24Cp.Pc.v516, CFSG.KD.Fi24Cp.Pc.v517, CFSG.KD.Fi24Cp.Pc.v518, CFSG.KD.Fi24Cp.Pc.v519, CFSG.KD.Fi24Cp.Pc.v520, CFSG.KD.Fi24Cp.Pc.v521, CFSG.KD.Fi24Cp.Pc.v522, CFSG.KD.Fi24Cp.Pc.v523]
theorem CFSG.KD.Fi24Cp.Pc.p522 : Nat.beq (runC AR SD 516 (ckL CFSG.KD.Fi24Cp.Pc.l524) 2 522 CFSG.KD.Fi24Cp.Pc.l522) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v524 : Nat := CFSG.KD.Fi24Cp.KV4 8
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v525 : Nat := CFSG.KD.Fi24Cp.KV4 9
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l526 : List Nat := [CFSG.KD.Fi24Cp.Pc.v516, CFSG.KD.Fi24Cp.Pc.v517, CFSG.KD.Fi24Cp.Pc.v518, CFSG.KD.Fi24Cp.Pc.v519, CFSG.KD.Fi24Cp.Pc.v520, CFSG.KD.Fi24Cp.Pc.v521, CFSG.KD.Fi24Cp.Pc.v522, CFSG.KD.Fi24Cp.Pc.v523, CFSG.KD.Fi24Cp.Pc.v524, CFSG.KD.Fi24Cp.Pc.v525]
theorem CFSG.KD.Fi24Cp.Pc.p524 : Nat.beq (runC AR SD 516 (ckL CFSG.KD.Fi24Cp.Pc.l526) 2 524 CFSG.KD.Fi24Cp.Pc.l524) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v526 : Nat := CFSG.KD.Fi24Cp.KV4 10
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v527 : Nat := CFSG.KD.Fi24Cp.KV4 11
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l528 : List Nat := [CFSG.KD.Fi24Cp.Pc.v516, CFSG.KD.Fi24Cp.Pc.v517, CFSG.KD.Fi24Cp.Pc.v518, CFSG.KD.Fi24Cp.Pc.v519, CFSG.KD.Fi24Cp.Pc.v520, CFSG.KD.Fi24Cp.Pc.v521, CFSG.KD.Fi24Cp.Pc.v522, CFSG.KD.Fi24Cp.Pc.v523, CFSG.KD.Fi24Cp.Pc.v524, CFSG.KD.Fi24Cp.Pc.v525, CFSG.KD.Fi24Cp.Pc.v526, CFSG.KD.Fi24Cp.Pc.v527]
theorem CFSG.KD.Fi24Cp.Pc.p526 : Nat.beq (runC AR SD 516 (ckL CFSG.KD.Fi24Cp.Pc.l528) 2 526 CFSG.KD.Fi24Cp.Pc.l526) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v528 : Nat := CFSG.KD.Fi24Cp.KV4 12
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v529 : Nat := CFSG.KD.Fi24Cp.KV4 13
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l530 : List Nat := [CFSG.KD.Fi24Cp.Pc.v516, CFSG.KD.Fi24Cp.Pc.v517, CFSG.KD.Fi24Cp.Pc.v518, CFSG.KD.Fi24Cp.Pc.v519, CFSG.KD.Fi24Cp.Pc.v520, CFSG.KD.Fi24Cp.Pc.v521, CFSG.KD.Fi24Cp.Pc.v522, CFSG.KD.Fi24Cp.Pc.v523, CFSG.KD.Fi24Cp.Pc.v524, CFSG.KD.Fi24Cp.Pc.v525, CFSG.KD.Fi24Cp.Pc.v526, CFSG.KD.Fi24Cp.Pc.v527, CFSG.KD.Fi24Cp.Pc.v528, CFSG.KD.Fi24Cp.Pc.v529]
theorem CFSG.KD.Fi24Cp.Pc.p528 : Nat.beq (runC AR SD 516 (ckL CFSG.KD.Fi24Cp.Pc.l530) 2 528 CFSG.KD.Fi24Cp.Pc.l528) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v530 : Nat := CFSG.KD.Fi24Cp.KV4 14
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v531 : Nat := CFSG.KD.Fi24Cp.KV4 15
theorem CFSG.KD.Fi24Cp.Pc.f40 : Nat.beq (runC AR SD 516 (finC AR SD (nat_lit 40) 516 532) 2 530 CFSG.KD.Fi24Cp.Pc.l530) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk40 : chk (nat_lit 40) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 40) (lo := 516) (hi := 532) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 518) CFSG.KD.Fi24Cp.Pc.p516 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 520) CFSG.KD.Fi24Cp.Pc.p518 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 522) CFSG.KD.Fi24Cp.Pc.p520 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 524) CFSG.KD.Fi24Cp.Pc.p522 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 526) CFSG.KD.Fi24Cp.Pc.p524 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 528) CFSG.KD.Fi24Cp.Pc.p526 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 530) CFSG.KD.Fi24Cp.Pc.p528 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f40

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v532 : Nat := CFSG.KD.Fi24Cp.KV4 16
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l533 : List Nat := [CFSG.KD.Fi24Cp.Pc.v532]
theorem CFSG.KD.Fi24Cp.Pc.p532 : Nat.beq (runC AR SD 532 (ckL CFSG.KD.Fi24Cp.Pc.l533) 1 532 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a533_2 : Nat := CFSG.KD.Fi24Cp.KV4 17
theorem CFSG.KD.Fi24Cp.Pc.q533_2 : Nat.beq (powTop AR.mul (getV AR SD 532 CFSG.KD.Fi24Cp.Pc.l533 (SD.na.getD 533 0)) (SD.nk.getD 533 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a533_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v533 : Nat := CFSG.KD.Fi24Cp.KV4 18
theorem CFSG.KD.Fi24Cp.Pc.r533 : Nat.beq (powR AR.mul AR.one (getV AR SD 532 CFSG.KD.Fi24Cp.Pc.l533 (SD.na.getD 533 0)) (SD.nk.getD 533 1) 2 CFSG.KD.Fi24Cp.Pc.a533_2 true) CFSG.KD.Fi24Cp.Pc.v533 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v534 : Nat := CFSG.KD.Fi24Cp.KV4 19
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v535 : Nat := CFSG.KD.Fi24Cp.KV4 20
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l534 : List Nat := [CFSG.KD.Fi24Cp.Pc.v532, CFSG.KD.Fi24Cp.Pc.v533]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l536 : List Nat := [CFSG.KD.Fi24Cp.Pc.v532, CFSG.KD.Fi24Cp.Pc.v533, CFSG.KD.Fi24Cp.Pc.v534, CFSG.KD.Fi24Cp.Pc.v535]
theorem CFSG.KD.Fi24Cp.Pc.p534 : Nat.beq (runC AR SD 532 (ckL CFSG.KD.Fi24Cp.Pc.l536) 2 534 CFSG.KD.Fi24Cp.Pc.l534) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v536 : Nat := CFSG.KD.Fi24Cp.KV4 21
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v537 : Nat := CFSG.KD.Fi24Cp.KV4 22
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l538 : List Nat := [CFSG.KD.Fi24Cp.Pc.v532, CFSG.KD.Fi24Cp.Pc.v533, CFSG.KD.Fi24Cp.Pc.v534, CFSG.KD.Fi24Cp.Pc.v535, CFSG.KD.Fi24Cp.Pc.v536, CFSG.KD.Fi24Cp.Pc.v537]
theorem CFSG.KD.Fi24Cp.Pc.p536 : Nat.beq (runC AR SD 532 (ckL CFSG.KD.Fi24Cp.Pc.l538) 2 536 CFSG.KD.Fi24Cp.Pc.l536) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v538 : Nat := CFSG.KD.Fi24Cp.KV4 23
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v539 : Nat := CFSG.KD.Fi24Cp.KV4 24
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l540 : List Nat := [CFSG.KD.Fi24Cp.Pc.v532, CFSG.KD.Fi24Cp.Pc.v533, CFSG.KD.Fi24Cp.Pc.v534, CFSG.KD.Fi24Cp.Pc.v535, CFSG.KD.Fi24Cp.Pc.v536, CFSG.KD.Fi24Cp.Pc.v537, CFSG.KD.Fi24Cp.Pc.v538, CFSG.KD.Fi24Cp.Pc.v539]
theorem CFSG.KD.Fi24Cp.Pc.p538 : Nat.beq (runC AR SD 532 (ckL CFSG.KD.Fi24Cp.Pc.l540) 2 538 CFSG.KD.Fi24Cp.Pc.l538) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v540 : Nat := CFSG.KD.Fi24Cp.KV4 25
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v541 : Nat := CFSG.KD.Fi24Cp.KV4 26
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l542 : List Nat := [CFSG.KD.Fi24Cp.Pc.v532, CFSG.KD.Fi24Cp.Pc.v533, CFSG.KD.Fi24Cp.Pc.v534, CFSG.KD.Fi24Cp.Pc.v535, CFSG.KD.Fi24Cp.Pc.v536, CFSG.KD.Fi24Cp.Pc.v537, CFSG.KD.Fi24Cp.Pc.v538, CFSG.KD.Fi24Cp.Pc.v539, CFSG.KD.Fi24Cp.Pc.v540, CFSG.KD.Fi24Cp.Pc.v541]
theorem CFSG.KD.Fi24Cp.Pc.p540 : Nat.beq (runC AR SD 532 (ckL CFSG.KD.Fi24Cp.Pc.l542) 2 540 CFSG.KD.Fi24Cp.Pc.l540) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v542 : Nat := CFSG.KD.Fi24Cp.KV4 27
theorem CFSG.KD.Fi24Cp.Pc.f41 : Nat.beq (runC AR SD 532 (finC AR SD (nat_lit 41) 532 543) 1 542 CFSG.KD.Fi24Cp.Pc.l542) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk41 : chk (nat_lit 41) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 41) (lo := 532) (hi := 543) (m := 11) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 11) (m2 := 10) (j2 := 533) CFSG.KD.Fi24Cp.Pc.p532 rfl rfl).trans ((runC_node (m := 10) (m2 := 9) (j2 := 534) (Lr := CFSG.KD.Fi24Cp.Pc.l534) ((nodeV_pow (R := AR) (D := SD) (lo := 532) (L := CFSG.KD.Fi24Cp.Pc.l533) (j := 533) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 532 CFSG.KD.Fi24Cp.Pc.l533 (SD.na.getD 533 0)) (SD.nk.getD 533 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q533_2 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r533)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 536) CFSG.KD.Fi24Cp.Pc.p534 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 538) CFSG.KD.Fi24Cp.Pc.p536 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 540) CFSG.KD.Fi24Cp.Pc.p538 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 542) CFSG.KD.Fi24Cp.Pc.p540 rfl rfl)))))))).trans CFSG.KD.Fi24Cp.Pc.f41

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a543_3 : Nat := CFSG.KD.Fi24Cp.KV4 28
theorem CFSG.KD.Fi24Cp.Pc.q543_3 : Nat.beq (powTop AR.mul (getV AR SD 543 [] (SD.na.getD 543 0)) (SD.nk.getD 543 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a543_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a543_2 : Nat := CFSG.KD.Fi24Cp.KV4 29
theorem CFSG.KD.Fi24Cp.Pc.q543_2 : Nat.beq (powTop AR.mul (getV AR SD 543 [] (SD.na.getD 543 0)) (SD.nk.getD 543 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a543_2) 1 CFSG.KD.Fi24Cp.Pc.a543_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a543_1 : Nat := CFSG.KD.Fi24Cp.KV4 30
theorem CFSG.KD.Fi24Cp.Pc.q543_1 : Nat.beq (powTop AR.mul (getV AR SD 543 [] (SD.na.getD 543 0)) (SD.nk.getD 543 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a543_1) 1 CFSG.KD.Fi24Cp.Pc.a543_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v543 : Nat := CFSG.KD.Fi24Cp.KV4 31
theorem CFSG.KD.Fi24Cp.Pc.r543 : Nat.beq (powR AR.mul AR.one (getV AR SD 543 [] (SD.na.getD 543 0)) (SD.nk.getD 543 1) 1 CFSG.KD.Fi24Cp.Pc.a543_1 true) CFSG.KD.Fi24Cp.Pc.v543 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v544 : Nat := CFSG.KD.Fi24Cp.KV4 32
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v545 : Nat := CFSG.KD.Fi24Cp.KV4 33
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l544 : List Nat := [CFSG.KD.Fi24Cp.Pc.v543]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l546 : List Nat := [CFSG.KD.Fi24Cp.Pc.v543, CFSG.KD.Fi24Cp.Pc.v544, CFSG.KD.Fi24Cp.Pc.v545]
theorem CFSG.KD.Fi24Cp.Pc.p544 : Nat.beq (runC AR SD 543 (ckL CFSG.KD.Fi24Cp.Pc.l546) 2 544 CFSG.KD.Fi24Cp.Pc.l544) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v546 : Nat := CFSG.KD.Fi24Cp.KV4 34
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v547 : Nat := CFSG.KD.Fi24Cp.KV4 35
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l548 : List Nat := [CFSG.KD.Fi24Cp.Pc.v543, CFSG.KD.Fi24Cp.Pc.v544, CFSG.KD.Fi24Cp.Pc.v545, CFSG.KD.Fi24Cp.Pc.v546, CFSG.KD.Fi24Cp.Pc.v547]
theorem CFSG.KD.Fi24Cp.Pc.p546 : Nat.beq (runC AR SD 543 (ckL CFSG.KD.Fi24Cp.Pc.l548) 2 546 CFSG.KD.Fi24Cp.Pc.l546) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v548 : Nat := CFSG.KD.Fi24Cp.KV4 36
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v549 : Nat := CFSG.KD.Fi24Cp.KV4 37
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l550 : List Nat := [CFSG.KD.Fi24Cp.Pc.v543, CFSG.KD.Fi24Cp.Pc.v544, CFSG.KD.Fi24Cp.Pc.v545, CFSG.KD.Fi24Cp.Pc.v546, CFSG.KD.Fi24Cp.Pc.v547, CFSG.KD.Fi24Cp.Pc.v548, CFSG.KD.Fi24Cp.Pc.v549]
theorem CFSG.KD.Fi24Cp.Pc.p548 : Nat.beq (runC AR SD 543 (ckL CFSG.KD.Fi24Cp.Pc.l550) 2 548 CFSG.KD.Fi24Cp.Pc.l548) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v550 : Nat := CFSG.KD.Fi24Cp.KV4 38
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v551 : Nat := CFSG.KD.Fi24Cp.KV4 39
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l552 : List Nat := [CFSG.KD.Fi24Cp.Pc.v543, CFSG.KD.Fi24Cp.Pc.v544, CFSG.KD.Fi24Cp.Pc.v545, CFSG.KD.Fi24Cp.Pc.v546, CFSG.KD.Fi24Cp.Pc.v547, CFSG.KD.Fi24Cp.Pc.v548, CFSG.KD.Fi24Cp.Pc.v549, CFSG.KD.Fi24Cp.Pc.v550, CFSG.KD.Fi24Cp.Pc.v551]
theorem CFSG.KD.Fi24Cp.Pc.p550 : Nat.beq (runC AR SD 543 (ckL CFSG.KD.Fi24Cp.Pc.l552) 2 550 CFSG.KD.Fi24Cp.Pc.l550) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v552 : Nat := CFSG.KD.Fi24Cp.KV4 40
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v553 : Nat := CFSG.KD.Fi24Cp.KV4 41
theorem CFSG.KD.Fi24Cp.Pc.f42 : Nat.beq (runC AR SD 543 (finC AR SD (nat_lit 42) 543 554) 2 552 CFSG.KD.Fi24Cp.Pc.l552) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk42 : chk (nat_lit 42) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 42) (lo := 543) (hi := 554) (m := 11) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 11) (m2 := 10) (j2 := 544) (Lr := CFSG.KD.Fi24Cp.Pc.l544) ((nodeV_pow (R := AR) (D := SD) (lo := 543) (L := []) (j := 543) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 543 [] (SD.na.getD 543 0)) (SD.nk.getD 543 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q543_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q543_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q543_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r543)))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 546) CFSG.KD.Fi24Cp.Pc.p544 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 548) CFSG.KD.Fi24Cp.Pc.p546 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 550) CFSG.KD.Fi24Cp.Pc.p548 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 552) CFSG.KD.Fi24Cp.Pc.p550 rfl rfl))))))).trans CFSG.KD.Fi24Cp.Pc.f42

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v554 : Nat := CFSG.KD.Fi24Cp.KV4 42
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v555 : Nat := CFSG.KD.Fi24Cp.KV4 43
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l556 : List Nat := [CFSG.KD.Fi24Cp.Pc.v554, CFSG.KD.Fi24Cp.Pc.v555]
theorem CFSG.KD.Fi24Cp.Pc.p554 : Nat.beq (runC AR SD 554 (ckL CFSG.KD.Fi24Cp.Pc.l556) 2 554 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v556 : Nat := CFSG.KD.Fi24Cp.KV4 44
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v557 : Nat := CFSG.KD.Fi24Cp.KV4 45
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l558 : List Nat := [CFSG.KD.Fi24Cp.Pc.v554, CFSG.KD.Fi24Cp.Pc.v555, CFSG.KD.Fi24Cp.Pc.v556, CFSG.KD.Fi24Cp.Pc.v557]
theorem CFSG.KD.Fi24Cp.Pc.p556 : Nat.beq (runC AR SD 554 (ckL CFSG.KD.Fi24Cp.Pc.l558) 2 556 CFSG.KD.Fi24Cp.Pc.l556) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v558 : Nat := CFSG.KD.Fi24Cp.KV4 46
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v559 : Nat := CFSG.KD.Fi24Cp.KV4 47
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l560 : List Nat := [CFSG.KD.Fi24Cp.Pc.v554, CFSG.KD.Fi24Cp.Pc.v555, CFSG.KD.Fi24Cp.Pc.v556, CFSG.KD.Fi24Cp.Pc.v557, CFSG.KD.Fi24Cp.Pc.v558, CFSG.KD.Fi24Cp.Pc.v559]
theorem CFSG.KD.Fi24Cp.Pc.p558 : Nat.beq (runC AR SD 554 (ckL CFSG.KD.Fi24Cp.Pc.l560) 2 558 CFSG.KD.Fi24Cp.Pc.l558) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v560 : Nat := CFSG.KD.Fi24Cp.KV4 48
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v561 : Nat := CFSG.KD.Fi24Cp.KV4 49
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l562 : List Nat := [CFSG.KD.Fi24Cp.Pc.v554, CFSG.KD.Fi24Cp.Pc.v555, CFSG.KD.Fi24Cp.Pc.v556, CFSG.KD.Fi24Cp.Pc.v557, CFSG.KD.Fi24Cp.Pc.v558, CFSG.KD.Fi24Cp.Pc.v559, CFSG.KD.Fi24Cp.Pc.v560, CFSG.KD.Fi24Cp.Pc.v561]
theorem CFSG.KD.Fi24Cp.Pc.p560 : Nat.beq (runC AR SD 554 (ckL CFSG.KD.Fi24Cp.Pc.l562) 2 560 CFSG.KD.Fi24Cp.Pc.l560) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v562 : Nat := CFSG.KD.Fi24Cp.KV4 50
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v563 : Nat := CFSG.KD.Fi24Cp.KV4 51
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l564 : List Nat := [CFSG.KD.Fi24Cp.Pc.v554, CFSG.KD.Fi24Cp.Pc.v555, CFSG.KD.Fi24Cp.Pc.v556, CFSG.KD.Fi24Cp.Pc.v557, CFSG.KD.Fi24Cp.Pc.v558, CFSG.KD.Fi24Cp.Pc.v559, CFSG.KD.Fi24Cp.Pc.v560, CFSG.KD.Fi24Cp.Pc.v561, CFSG.KD.Fi24Cp.Pc.v562, CFSG.KD.Fi24Cp.Pc.v563]
theorem CFSG.KD.Fi24Cp.Pc.p562 : Nat.beq (runC AR SD 554 (ckL CFSG.KD.Fi24Cp.Pc.l564) 2 562 CFSG.KD.Fi24Cp.Pc.l562) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v564 : Nat := CFSG.KD.Fi24Cp.KV4 52
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v565 : Nat := CFSG.KD.Fi24Cp.KV4 53
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l566 : List Nat := [CFSG.KD.Fi24Cp.Pc.v554, CFSG.KD.Fi24Cp.Pc.v555, CFSG.KD.Fi24Cp.Pc.v556, CFSG.KD.Fi24Cp.Pc.v557, CFSG.KD.Fi24Cp.Pc.v558, CFSG.KD.Fi24Cp.Pc.v559, CFSG.KD.Fi24Cp.Pc.v560, CFSG.KD.Fi24Cp.Pc.v561, CFSG.KD.Fi24Cp.Pc.v562, CFSG.KD.Fi24Cp.Pc.v563, CFSG.KD.Fi24Cp.Pc.v564, CFSG.KD.Fi24Cp.Pc.v565]
theorem CFSG.KD.Fi24Cp.Pc.p564 : Nat.beq (runC AR SD 554 (ckL CFSG.KD.Fi24Cp.Pc.l566) 2 564 CFSG.KD.Fi24Cp.Pc.l564) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v566 : Nat := CFSG.KD.Fi24Cp.KV4 54
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v567 : Nat := CFSG.KD.Fi24Cp.KV4 55
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l568 : List Nat := [CFSG.KD.Fi24Cp.Pc.v554, CFSG.KD.Fi24Cp.Pc.v555, CFSG.KD.Fi24Cp.Pc.v556, CFSG.KD.Fi24Cp.Pc.v557, CFSG.KD.Fi24Cp.Pc.v558, CFSG.KD.Fi24Cp.Pc.v559, CFSG.KD.Fi24Cp.Pc.v560, CFSG.KD.Fi24Cp.Pc.v561, CFSG.KD.Fi24Cp.Pc.v562, CFSG.KD.Fi24Cp.Pc.v563, CFSG.KD.Fi24Cp.Pc.v564, CFSG.KD.Fi24Cp.Pc.v565, CFSG.KD.Fi24Cp.Pc.v566, CFSG.KD.Fi24Cp.Pc.v567]
theorem CFSG.KD.Fi24Cp.Pc.p566 : Nat.beq (runC AR SD 554 (ckL CFSG.KD.Fi24Cp.Pc.l568) 2 566 CFSG.KD.Fi24Cp.Pc.l566) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v568 : Nat := CFSG.KD.Fi24Cp.KV4 56
theorem CFSG.KD.Fi24Cp.Pc.f43 : Nat.beq (runC AR SD 554 (finC AR SD (nat_lit 43) 554 569) 1 568 CFSG.KD.Fi24Cp.Pc.l568) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk43 : chk (nat_lit 43) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 43) (lo := 554) (hi := 569) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 556) CFSG.KD.Fi24Cp.Pc.p554 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 558) CFSG.KD.Fi24Cp.Pc.p556 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 560) CFSG.KD.Fi24Cp.Pc.p558 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 562) CFSG.KD.Fi24Cp.Pc.p560 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 564) CFSG.KD.Fi24Cp.Pc.p562 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 566) CFSG.KD.Fi24Cp.Pc.p564 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 568) CFSG.KD.Fi24Cp.Pc.p566 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f43

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a569_3 : Nat := CFSG.KD.Fi24Cp.KV4 57
theorem CFSG.KD.Fi24Cp.Pc.q569_3 : Nat.beq (powTop AR.mul (getV AR SD 569 [] (SD.na.getD 569 0)) (SD.nk.getD 569 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a569_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a569_2 : Nat := CFSG.KD.Fi24Cp.KV4 58
theorem CFSG.KD.Fi24Cp.Pc.q569_2 : Nat.beq (powTop AR.mul (getV AR SD 569 [] (SD.na.getD 569 0)) (SD.nk.getD 569 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a569_2) 1 CFSG.KD.Fi24Cp.Pc.a569_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a569_1 : Nat := CFSG.KD.Fi24Cp.KV4 59
theorem CFSG.KD.Fi24Cp.Pc.q569_1 : Nat.beq (powTop AR.mul (getV AR SD 569 [] (SD.na.getD 569 0)) (SD.nk.getD 569 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a569_1) 1 CFSG.KD.Fi24Cp.Pc.a569_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v569 : Nat := CFSG.KD.Fi24Cp.KV4 60
theorem CFSG.KD.Fi24Cp.Pc.r569 : Nat.beq (powR AR.mul AR.one (getV AR SD 569 [] (SD.na.getD 569 0)) (SD.nk.getD 569 1) 1 CFSG.KD.Fi24Cp.Pc.a569_1 true) CFSG.KD.Fi24Cp.Pc.v569 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v570 : Nat := CFSG.KD.Fi24Cp.KV4 61
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v571 : Nat := CFSG.KD.Fi24Cp.KV4 62
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l570 : List Nat := [CFSG.KD.Fi24Cp.Pc.v569]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l572 : List Nat := [CFSG.KD.Fi24Cp.Pc.v569, CFSG.KD.Fi24Cp.Pc.v570, CFSG.KD.Fi24Cp.Pc.v571]
theorem CFSG.KD.Fi24Cp.Pc.p570 : Nat.beq (runC AR SD 569 (ckL CFSG.KD.Fi24Cp.Pc.l572) 2 570 CFSG.KD.Fi24Cp.Pc.l570) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v572 : Nat := CFSG.KD.Fi24Cp.KV4 63
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v573 : Nat := CFSG.KD.Fi24Cp.KV4 64
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l574 : List Nat := [CFSG.KD.Fi24Cp.Pc.v569, CFSG.KD.Fi24Cp.Pc.v570, CFSG.KD.Fi24Cp.Pc.v571, CFSG.KD.Fi24Cp.Pc.v572, CFSG.KD.Fi24Cp.Pc.v573]
theorem CFSG.KD.Fi24Cp.Pc.p572 : Nat.beq (runC AR SD 569 (ckL CFSG.KD.Fi24Cp.Pc.l574) 2 572 CFSG.KD.Fi24Cp.Pc.l572) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v574 : Nat := CFSG.KD.Fi24Cp.KV4 65
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v575 : Nat := CFSG.KD.Fi24Cp.KV4 66
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l576 : List Nat := [CFSG.KD.Fi24Cp.Pc.v569, CFSG.KD.Fi24Cp.Pc.v570, CFSG.KD.Fi24Cp.Pc.v571, CFSG.KD.Fi24Cp.Pc.v572, CFSG.KD.Fi24Cp.Pc.v573, CFSG.KD.Fi24Cp.Pc.v574, CFSG.KD.Fi24Cp.Pc.v575]
theorem CFSG.KD.Fi24Cp.Pc.p574 : Nat.beq (runC AR SD 569 (ckL CFSG.KD.Fi24Cp.Pc.l576) 2 574 CFSG.KD.Fi24Cp.Pc.l574) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v576 : Nat := CFSG.KD.Fi24Cp.KV4 67
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v577 : Nat := CFSG.KD.Fi24Cp.KV4 68
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l578 : List Nat := [CFSG.KD.Fi24Cp.Pc.v569, CFSG.KD.Fi24Cp.Pc.v570, CFSG.KD.Fi24Cp.Pc.v571, CFSG.KD.Fi24Cp.Pc.v572, CFSG.KD.Fi24Cp.Pc.v573, CFSG.KD.Fi24Cp.Pc.v574, CFSG.KD.Fi24Cp.Pc.v575, CFSG.KD.Fi24Cp.Pc.v576, CFSG.KD.Fi24Cp.Pc.v577]
theorem CFSG.KD.Fi24Cp.Pc.p576 : Nat.beq (runC AR SD 569 (ckL CFSG.KD.Fi24Cp.Pc.l578) 2 576 CFSG.KD.Fi24Cp.Pc.l576) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v578 : Nat := CFSG.KD.Fi24Cp.KV4 69
theorem CFSG.KD.Fi24Cp.Pc.f44 : Nat.beq (runC AR SD 569 (finC AR SD (nat_lit 44) 569 579) 1 578 CFSG.KD.Fi24Cp.Pc.l578) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk44 : chk (nat_lit 44) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 44) (lo := 569) (hi := 579) (m := 10) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 10) (m2 := 9) (j2 := 570) (Lr := CFSG.KD.Fi24Cp.Pc.l570) ((nodeV_pow (R := AR) (D := SD) (lo := 569) (L := []) (j := 569) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 569 [] (SD.na.getD 569 0)) (SD.nk.getD 569 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q569_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q569_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q569_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r569)))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 572) CFSG.KD.Fi24Cp.Pc.p570 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 574) CFSG.KD.Fi24Cp.Pc.p572 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 576) CFSG.KD.Fi24Cp.Pc.p574 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 578) CFSG.KD.Fi24Cp.Pc.p576 rfl rfl))))))).trans CFSG.KD.Fi24Cp.Pc.f44

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v579 : Nat := CFSG.KD.Fi24Cp.KV4 70
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v580 : Nat := CFSG.KD.Fi24Cp.KV4 71
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l581 : List Nat := [CFSG.KD.Fi24Cp.Pc.v579, CFSG.KD.Fi24Cp.Pc.v580]
theorem CFSG.KD.Fi24Cp.Pc.p579 : Nat.beq (runC AR SD 579 (ckL CFSG.KD.Fi24Cp.Pc.l581) 2 579 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v581 : Nat := CFSG.KD.Fi24Cp.KV4 72
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v582 : Nat := CFSG.KD.Fi24Cp.KV4 73
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l583 : List Nat := [CFSG.KD.Fi24Cp.Pc.v579, CFSG.KD.Fi24Cp.Pc.v580, CFSG.KD.Fi24Cp.Pc.v581, CFSG.KD.Fi24Cp.Pc.v582]
theorem CFSG.KD.Fi24Cp.Pc.p581 : Nat.beq (runC AR SD 579 (ckL CFSG.KD.Fi24Cp.Pc.l583) 2 581 CFSG.KD.Fi24Cp.Pc.l581) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v583 : Nat := CFSG.KD.Fi24Cp.KV4 74
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v584 : Nat := CFSG.KD.Fi24Cp.KV4 75
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l585 : List Nat := [CFSG.KD.Fi24Cp.Pc.v579, CFSG.KD.Fi24Cp.Pc.v580, CFSG.KD.Fi24Cp.Pc.v581, CFSG.KD.Fi24Cp.Pc.v582, CFSG.KD.Fi24Cp.Pc.v583, CFSG.KD.Fi24Cp.Pc.v584]
theorem CFSG.KD.Fi24Cp.Pc.p583 : Nat.beq (runC AR SD 579 (ckL CFSG.KD.Fi24Cp.Pc.l585) 2 583 CFSG.KD.Fi24Cp.Pc.l583) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v585 : Nat := CFSG.KD.Fi24Cp.KV4 76
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v586 : Nat := CFSG.KD.Fi24Cp.KV4 77
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l587 : List Nat := [CFSG.KD.Fi24Cp.Pc.v579, CFSG.KD.Fi24Cp.Pc.v580, CFSG.KD.Fi24Cp.Pc.v581, CFSG.KD.Fi24Cp.Pc.v582, CFSG.KD.Fi24Cp.Pc.v583, CFSG.KD.Fi24Cp.Pc.v584, CFSG.KD.Fi24Cp.Pc.v585, CFSG.KD.Fi24Cp.Pc.v586]
theorem CFSG.KD.Fi24Cp.Pc.p585 : Nat.beq (runC AR SD 579 (ckL CFSG.KD.Fi24Cp.Pc.l587) 2 585 CFSG.KD.Fi24Cp.Pc.l585) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v587 : Nat := CFSG.KD.Fi24Cp.KV4 78
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v588 : Nat := CFSG.KD.Fi24Cp.KV4 79
theorem CFSG.KD.Fi24Cp.Pc.f45 : Nat.beq (runC AR SD 579 (finC AR SD (nat_lit 45) 579 589) 2 587 CFSG.KD.Fi24Cp.Pc.l587) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk45 : chk (nat_lit 45) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 45) (lo := 579) (hi := 589) (m := 10) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 10) (m2 := 8) (j2 := 581) CFSG.KD.Fi24Cp.Pc.p579 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 583) CFSG.KD.Fi24Cp.Pc.p581 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 585) CFSG.KD.Fi24Cp.Pc.p583 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 587) CFSG.KD.Fi24Cp.Pc.p585 rfl rfl)))))).trans CFSG.KD.Fi24Cp.Pc.f45

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a589_3 : Nat := CFSG.KD.Fi24Cp.KV4 80
theorem CFSG.KD.Fi24Cp.Pc.q589_3 : Nat.beq (powTop AR.mul (getV AR SD 589 [] (SD.na.getD 589 0)) (SD.nk.getD 589 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a589_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a589_2 : Nat := CFSG.KD.Fi24Cp.KV4 81
theorem CFSG.KD.Fi24Cp.Pc.q589_2 : Nat.beq (powTop AR.mul (getV AR SD 589 [] (SD.na.getD 589 0)) (SD.nk.getD 589 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a589_2) 1 CFSG.KD.Fi24Cp.Pc.a589_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a589_1 : Nat := CFSG.KD.Fi24Cp.KV4 82
theorem CFSG.KD.Fi24Cp.Pc.q589_1 : Nat.beq (powTop AR.mul (getV AR SD 589 [] (SD.na.getD 589 0)) (SD.nk.getD 589 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a589_1) 1 CFSG.KD.Fi24Cp.Pc.a589_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v589 : Nat := CFSG.KD.Fi24Cp.KV4 83
theorem CFSG.KD.Fi24Cp.Pc.r589 : Nat.beq (powR AR.mul AR.one (getV AR SD 589 [] (SD.na.getD 589 0)) (SD.nk.getD 589 1) 1 CFSG.KD.Fi24Cp.Pc.a589_1 true) CFSG.KD.Fi24Cp.Pc.v589 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v590 : Nat := CFSG.KD.Fi24Cp.KV4 84
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v591 : Nat := CFSG.KD.Fi24Cp.KV4 85
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l590 : List Nat := [CFSG.KD.Fi24Cp.Pc.v589]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l592 : List Nat := [CFSG.KD.Fi24Cp.Pc.v589, CFSG.KD.Fi24Cp.Pc.v590, CFSG.KD.Fi24Cp.Pc.v591]
theorem CFSG.KD.Fi24Cp.Pc.p590 : Nat.beq (runC AR SD 589 (ckL CFSG.KD.Fi24Cp.Pc.l592) 2 590 CFSG.KD.Fi24Cp.Pc.l590) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v592 : Nat := CFSG.KD.Fi24Cp.KV4 86
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v593 : Nat := CFSG.KD.Fi24Cp.KV4 87
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l594 : List Nat := [CFSG.KD.Fi24Cp.Pc.v589, CFSG.KD.Fi24Cp.Pc.v590, CFSG.KD.Fi24Cp.Pc.v591, CFSG.KD.Fi24Cp.Pc.v592, CFSG.KD.Fi24Cp.Pc.v593]
theorem CFSG.KD.Fi24Cp.Pc.p592 : Nat.beq (runC AR SD 589 (ckL CFSG.KD.Fi24Cp.Pc.l594) 2 592 CFSG.KD.Fi24Cp.Pc.l592) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v594 : Nat := CFSG.KD.Fi24Cp.KV4 88
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v595 : Nat := CFSG.KD.Fi24Cp.KV4 89
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l596 : List Nat := [CFSG.KD.Fi24Cp.Pc.v589, CFSG.KD.Fi24Cp.Pc.v590, CFSG.KD.Fi24Cp.Pc.v591, CFSG.KD.Fi24Cp.Pc.v592, CFSG.KD.Fi24Cp.Pc.v593, CFSG.KD.Fi24Cp.Pc.v594, CFSG.KD.Fi24Cp.Pc.v595]
theorem CFSG.KD.Fi24Cp.Pc.p594 : Nat.beq (runC AR SD 589 (ckL CFSG.KD.Fi24Cp.Pc.l596) 2 594 CFSG.KD.Fi24Cp.Pc.l594) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v596 : Nat := CFSG.KD.Fi24Cp.KV4 90
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v597 : Nat := CFSG.KD.Fi24Cp.KV4 91
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l598 : List Nat := [CFSG.KD.Fi24Cp.Pc.v589, CFSG.KD.Fi24Cp.Pc.v590, CFSG.KD.Fi24Cp.Pc.v591, CFSG.KD.Fi24Cp.Pc.v592, CFSG.KD.Fi24Cp.Pc.v593, CFSG.KD.Fi24Cp.Pc.v594, CFSG.KD.Fi24Cp.Pc.v595, CFSG.KD.Fi24Cp.Pc.v596, CFSG.KD.Fi24Cp.Pc.v597]
theorem CFSG.KD.Fi24Cp.Pc.p596 : Nat.beq (runC AR SD 589 (ckL CFSG.KD.Fi24Cp.Pc.l598) 2 596 CFSG.KD.Fi24Cp.Pc.l596) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v598 : Nat := CFSG.KD.Fi24Cp.KV4 92
theorem CFSG.KD.Fi24Cp.Pc.f46 : Nat.beq (runC AR SD 589 (finC AR SD (nat_lit 46) 589 599) 1 598 CFSG.KD.Fi24Cp.Pc.l598) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk46 : chk (nat_lit 46) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 46) (lo := 589) (hi := 599) (m := 10) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 10) (m2 := 9) (j2 := 590) (Lr := CFSG.KD.Fi24Cp.Pc.l590) ((nodeV_pow (R := AR) (D := SD) (lo := 589) (L := []) (j := 589) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 589 [] (SD.na.getD 589 0)) (SD.nk.getD 589 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q589_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q589_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q589_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r589)))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 592) CFSG.KD.Fi24Cp.Pc.p590 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 594) CFSG.KD.Fi24Cp.Pc.p592 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 596) CFSG.KD.Fi24Cp.Pc.p594 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 598) CFSG.KD.Fi24Cp.Pc.p596 rfl rfl))))))).trans CFSG.KD.Fi24Cp.Pc.f46

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v599 : Nat := CFSG.KD.Fi24Cp.KV4 93
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v600 : Nat := CFSG.KD.Fi24Cp.KV4 94
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l601 : List Nat := [CFSG.KD.Fi24Cp.Pc.v599, CFSG.KD.Fi24Cp.Pc.v600]
theorem CFSG.KD.Fi24Cp.Pc.p599 : Nat.beq (runC AR SD 599 (ckL CFSG.KD.Fi24Cp.Pc.l601) 2 599 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v601 : Nat := CFSG.KD.Fi24Cp.KV4 95
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v602 : Nat := CFSG.KD.Fi24Cp.KV4 96
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l603 : List Nat := [CFSG.KD.Fi24Cp.Pc.v599, CFSG.KD.Fi24Cp.Pc.v600, CFSG.KD.Fi24Cp.Pc.v601, CFSG.KD.Fi24Cp.Pc.v602]
theorem CFSG.KD.Fi24Cp.Pc.p601 : Nat.beq (runC AR SD 599 (ckL CFSG.KD.Fi24Cp.Pc.l603) 2 601 CFSG.KD.Fi24Cp.Pc.l601) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v603 : Nat := CFSG.KD.Fi24Cp.KV4 97
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v604 : Nat := CFSG.KD.Fi24Cp.KV4 98
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l605 : List Nat := [CFSG.KD.Fi24Cp.Pc.v599, CFSG.KD.Fi24Cp.Pc.v600, CFSG.KD.Fi24Cp.Pc.v601, CFSG.KD.Fi24Cp.Pc.v602, CFSG.KD.Fi24Cp.Pc.v603, CFSG.KD.Fi24Cp.Pc.v604]
theorem CFSG.KD.Fi24Cp.Pc.p603 : Nat.beq (runC AR SD 599 (ckL CFSG.KD.Fi24Cp.Pc.l605) 2 603 CFSG.KD.Fi24Cp.Pc.l603) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v605 : Nat := CFSG.KD.Fi24Cp.KV4 99
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v606 : Nat := CFSG.KD.Fi24Cp.KV4 100
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l607 : List Nat := [CFSG.KD.Fi24Cp.Pc.v599, CFSG.KD.Fi24Cp.Pc.v600, CFSG.KD.Fi24Cp.Pc.v601, CFSG.KD.Fi24Cp.Pc.v602, CFSG.KD.Fi24Cp.Pc.v603, CFSG.KD.Fi24Cp.Pc.v604, CFSG.KD.Fi24Cp.Pc.v605, CFSG.KD.Fi24Cp.Pc.v606]
theorem CFSG.KD.Fi24Cp.Pc.p605 : Nat.beq (runC AR SD 599 (ckL CFSG.KD.Fi24Cp.Pc.l607) 2 605 CFSG.KD.Fi24Cp.Pc.l605) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v607 : Nat := CFSG.KD.Fi24Cp.KV4 101
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v608 : Nat := CFSG.KD.Fi24Cp.KV4 102
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l609 : List Nat := [CFSG.KD.Fi24Cp.Pc.v599, CFSG.KD.Fi24Cp.Pc.v600, CFSG.KD.Fi24Cp.Pc.v601, CFSG.KD.Fi24Cp.Pc.v602, CFSG.KD.Fi24Cp.Pc.v603, CFSG.KD.Fi24Cp.Pc.v604, CFSG.KD.Fi24Cp.Pc.v605, CFSG.KD.Fi24Cp.Pc.v606, CFSG.KD.Fi24Cp.Pc.v607, CFSG.KD.Fi24Cp.Pc.v608]
theorem CFSG.KD.Fi24Cp.Pc.p607 : Nat.beq (runC AR SD 599 (ckL CFSG.KD.Fi24Cp.Pc.l609) 2 607 CFSG.KD.Fi24Cp.Pc.l607) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v609 : Nat := CFSG.KD.Fi24Cp.KV4 103
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v610 : Nat := CFSG.KD.Fi24Cp.KV4 104
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l611 : List Nat := [CFSG.KD.Fi24Cp.Pc.v599, CFSG.KD.Fi24Cp.Pc.v600, CFSG.KD.Fi24Cp.Pc.v601, CFSG.KD.Fi24Cp.Pc.v602, CFSG.KD.Fi24Cp.Pc.v603, CFSG.KD.Fi24Cp.Pc.v604, CFSG.KD.Fi24Cp.Pc.v605, CFSG.KD.Fi24Cp.Pc.v606, CFSG.KD.Fi24Cp.Pc.v607, CFSG.KD.Fi24Cp.Pc.v608, CFSG.KD.Fi24Cp.Pc.v609, CFSG.KD.Fi24Cp.Pc.v610]
theorem CFSG.KD.Fi24Cp.Pc.p609 : Nat.beq (runC AR SD 599 (ckL CFSG.KD.Fi24Cp.Pc.l611) 2 609 CFSG.KD.Fi24Cp.Pc.l609) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v611 : Nat := CFSG.KD.Fi24Cp.KV4 105
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v612 : Nat := CFSG.KD.Fi24Cp.KV4 106
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l613 : List Nat := [CFSG.KD.Fi24Cp.Pc.v599, CFSG.KD.Fi24Cp.Pc.v600, CFSG.KD.Fi24Cp.Pc.v601, CFSG.KD.Fi24Cp.Pc.v602, CFSG.KD.Fi24Cp.Pc.v603, CFSG.KD.Fi24Cp.Pc.v604, CFSG.KD.Fi24Cp.Pc.v605, CFSG.KD.Fi24Cp.Pc.v606, CFSG.KD.Fi24Cp.Pc.v607, CFSG.KD.Fi24Cp.Pc.v608, CFSG.KD.Fi24Cp.Pc.v609, CFSG.KD.Fi24Cp.Pc.v610, CFSG.KD.Fi24Cp.Pc.v611, CFSG.KD.Fi24Cp.Pc.v612]
theorem CFSG.KD.Fi24Cp.Pc.p611 : Nat.beq (runC AR SD 599 (ckL CFSG.KD.Fi24Cp.Pc.l613) 2 611 CFSG.KD.Fi24Cp.Pc.l611) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v613 : Nat := CFSG.KD.Fi24Cp.KV4 107
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v614 : Nat := CFSG.KD.Fi24Cp.KV4 108
theorem CFSG.KD.Fi24Cp.Pc.f47 : Nat.beq (runC AR SD 599 (finC AR SD (nat_lit 47) 599 615) 2 613 CFSG.KD.Fi24Cp.Pc.l613) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk47 : chk (nat_lit 47) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 47) (lo := 599) (hi := 615) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 601) CFSG.KD.Fi24Cp.Pc.p599 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 603) CFSG.KD.Fi24Cp.Pc.p601 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 605) CFSG.KD.Fi24Cp.Pc.p603 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 607) CFSG.KD.Fi24Cp.Pc.p605 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 609) CFSG.KD.Fi24Cp.Pc.p607 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 611) CFSG.KD.Fi24Cp.Pc.p609 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 613) CFSG.KD.Fi24Cp.Pc.p611 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f47

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v615 : Nat := CFSG.KD.Fi24Cp.KV4 109
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v616 : Nat := CFSG.KD.Fi24Cp.KV4 110
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l617 : List Nat := [CFSG.KD.Fi24Cp.Pc.v615, CFSG.KD.Fi24Cp.Pc.v616]
theorem CFSG.KD.Fi24Cp.Pc.p615 : Nat.beq (runC AR SD 615 (ckL CFSG.KD.Fi24Cp.Pc.l617) 2 615 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v617 : Nat := CFSG.KD.Fi24Cp.KV4 111
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v618 : Nat := CFSG.KD.Fi24Cp.KV4 112
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l619 : List Nat := [CFSG.KD.Fi24Cp.Pc.v615, CFSG.KD.Fi24Cp.Pc.v616, CFSG.KD.Fi24Cp.Pc.v617, CFSG.KD.Fi24Cp.Pc.v618]
theorem CFSG.KD.Fi24Cp.Pc.p617 : Nat.beq (runC AR SD 615 (ckL CFSG.KD.Fi24Cp.Pc.l619) 2 617 CFSG.KD.Fi24Cp.Pc.l617) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v619 : Nat := CFSG.KD.Fi24Cp.KV4 113
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v620 : Nat := CFSG.KD.Fi24Cp.KV4 114
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l621 : List Nat := [CFSG.KD.Fi24Cp.Pc.v615, CFSG.KD.Fi24Cp.Pc.v616, CFSG.KD.Fi24Cp.Pc.v617, CFSG.KD.Fi24Cp.Pc.v618, CFSG.KD.Fi24Cp.Pc.v619, CFSG.KD.Fi24Cp.Pc.v620]
theorem CFSG.KD.Fi24Cp.Pc.p619 : Nat.beq (runC AR SD 615 (ckL CFSG.KD.Fi24Cp.Pc.l621) 2 619 CFSG.KD.Fi24Cp.Pc.l619) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v621 : Nat := CFSG.KD.Fi24Cp.KV4 115
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v622 : Nat := CFSG.KD.Fi24Cp.KV4 116
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l623 : List Nat := [CFSG.KD.Fi24Cp.Pc.v615, CFSG.KD.Fi24Cp.Pc.v616, CFSG.KD.Fi24Cp.Pc.v617, CFSG.KD.Fi24Cp.Pc.v618, CFSG.KD.Fi24Cp.Pc.v619, CFSG.KD.Fi24Cp.Pc.v620, CFSG.KD.Fi24Cp.Pc.v621, CFSG.KD.Fi24Cp.Pc.v622]
theorem CFSG.KD.Fi24Cp.Pc.p621 : Nat.beq (runC AR SD 615 (ckL CFSG.KD.Fi24Cp.Pc.l623) 2 621 CFSG.KD.Fi24Cp.Pc.l621) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a623_1 : Nat := CFSG.KD.Fi24Cp.KV4 117
theorem CFSG.KD.Fi24Cp.Pc.q623_1 : Nat.beq (powTop AR.mul (getV AR SD 615 CFSG.KD.Fi24Cp.Pc.l623 (SD.na.getD 623 0)) (SD.nk.getD 623 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a623_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v623 : Nat := CFSG.KD.Fi24Cp.KV4 118
theorem CFSG.KD.Fi24Cp.Pc.r623 : Nat.beq (powR AR.mul AR.one (getV AR SD 615 CFSG.KD.Fi24Cp.Pc.l623 (SD.na.getD 623 0)) (SD.nk.getD 623 1) 1 CFSG.KD.Fi24Cp.Pc.a623_1 true) CFSG.KD.Fi24Cp.Pc.v623 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v624 : Nat := CFSG.KD.Fi24Cp.KV4 119
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v625 : Nat := CFSG.KD.Fi24Cp.KV4 120
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l624 : List Nat := [CFSG.KD.Fi24Cp.Pc.v615, CFSG.KD.Fi24Cp.Pc.v616, CFSG.KD.Fi24Cp.Pc.v617, CFSG.KD.Fi24Cp.Pc.v618, CFSG.KD.Fi24Cp.Pc.v619, CFSG.KD.Fi24Cp.Pc.v620, CFSG.KD.Fi24Cp.Pc.v621, CFSG.KD.Fi24Cp.Pc.v622, CFSG.KD.Fi24Cp.Pc.v623]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l626 : List Nat := [CFSG.KD.Fi24Cp.Pc.v615, CFSG.KD.Fi24Cp.Pc.v616, CFSG.KD.Fi24Cp.Pc.v617, CFSG.KD.Fi24Cp.Pc.v618, CFSG.KD.Fi24Cp.Pc.v619, CFSG.KD.Fi24Cp.Pc.v620, CFSG.KD.Fi24Cp.Pc.v621, CFSG.KD.Fi24Cp.Pc.v622, CFSG.KD.Fi24Cp.Pc.v623, CFSG.KD.Fi24Cp.Pc.v624, CFSG.KD.Fi24Cp.Pc.v625]
theorem CFSG.KD.Fi24Cp.Pc.p624 : Nat.beq (runC AR SD 615 (ckL CFSG.KD.Fi24Cp.Pc.l626) 2 624 CFSG.KD.Fi24Cp.Pc.l624) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v626 : Nat := CFSG.KD.Fi24Cp.KV4 121
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v627 : Nat := CFSG.KD.Fi24Cp.KV4 122
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l628 : List Nat := [CFSG.KD.Fi24Cp.Pc.v615, CFSG.KD.Fi24Cp.Pc.v616, CFSG.KD.Fi24Cp.Pc.v617, CFSG.KD.Fi24Cp.Pc.v618, CFSG.KD.Fi24Cp.Pc.v619, CFSG.KD.Fi24Cp.Pc.v620, CFSG.KD.Fi24Cp.Pc.v621, CFSG.KD.Fi24Cp.Pc.v622, CFSG.KD.Fi24Cp.Pc.v623, CFSG.KD.Fi24Cp.Pc.v624, CFSG.KD.Fi24Cp.Pc.v625, CFSG.KD.Fi24Cp.Pc.v626, CFSG.KD.Fi24Cp.Pc.v627]
theorem CFSG.KD.Fi24Cp.Pc.p626 : Nat.beq (runC AR SD 615 (ckL CFSG.KD.Fi24Cp.Pc.l628) 2 626 CFSG.KD.Fi24Cp.Pc.l626) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v628 : Nat := CFSG.KD.Fi24Cp.KV4 123
theorem CFSG.KD.Fi24Cp.Pc.f48 : Nat.beq (runC AR SD 615 (finC AR SD (nat_lit 48) 615 629) 1 628 CFSG.KD.Fi24Cp.Pc.l628) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk48 : chk (nat_lit 48) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 48) (lo := 615) (hi := 629) (m := 14) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 14) (m2 := 12) (j2 := 617) CFSG.KD.Fi24Cp.Pc.p615 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 619) CFSG.KD.Fi24Cp.Pc.p617 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 621) CFSG.KD.Fi24Cp.Pc.p619 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 623) CFSG.KD.Fi24Cp.Pc.p621 rfl rfl).trans ((runC_node (m := 6) (m2 := 5) (j2 := 624) (Lr := CFSG.KD.Fi24Cp.Pc.l624) ((nodeV_pow (R := AR) (D := SD) (lo := 615) (L := CFSG.KD.Fi24Cp.Pc.l623) (j := 623) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 615 CFSG.KD.Fi24Cp.Pc.l623 (SD.na.getD 623 0)) (SD.nk.getD 623 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q623_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r623)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 626) CFSG.KD.Fi24Cp.Pc.p624 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 628) CFSG.KD.Fi24Cp.Pc.p626 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f48

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v629 : Nat := CFSG.KD.Fi24Cp.KV4 124
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v630 : Nat := CFSG.KD.Fi24Cp.KV4 125
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l631 : List Nat := [CFSG.KD.Fi24Cp.Pc.v629, CFSG.KD.Fi24Cp.Pc.v630]
theorem CFSG.KD.Fi24Cp.Pc.p629 : Nat.beq (runC AR SD 629 (ckL CFSG.KD.Fi24Cp.Pc.l631) 2 629 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v631 : Nat := CFSG.KD.Fi24Cp.KV4 126
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v632 : Nat := CFSG.KD.Fi24Cp.KV4 127
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l633 : List Nat := [CFSG.KD.Fi24Cp.Pc.v629, CFSG.KD.Fi24Cp.Pc.v630, CFSG.KD.Fi24Cp.Pc.v631, CFSG.KD.Fi24Cp.Pc.v632]
theorem CFSG.KD.Fi24Cp.Pc.p631 : Nat.beq (runC AR SD 629 (ckL CFSG.KD.Fi24Cp.Pc.l633) 2 631 CFSG.KD.Fi24Cp.Pc.l631) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v633 : Nat := CFSG.KD.Fi24Cp.KV4 128
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v634 : Nat := CFSG.KD.Fi24Cp.KV4 129
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l635 : List Nat := [CFSG.KD.Fi24Cp.Pc.v629, CFSG.KD.Fi24Cp.Pc.v630, CFSG.KD.Fi24Cp.Pc.v631, CFSG.KD.Fi24Cp.Pc.v632, CFSG.KD.Fi24Cp.Pc.v633, CFSG.KD.Fi24Cp.Pc.v634]
theorem CFSG.KD.Fi24Cp.Pc.p633 : Nat.beq (runC AR SD 629 (ckL CFSG.KD.Fi24Cp.Pc.l635) 2 633 CFSG.KD.Fi24Cp.Pc.l633) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v635 : Nat := CFSG.KD.Fi24Cp.KV4 130
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v636 : Nat := CFSG.KD.Fi24Cp.KV4 131
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l637 : List Nat := [CFSG.KD.Fi24Cp.Pc.v629, CFSG.KD.Fi24Cp.Pc.v630, CFSG.KD.Fi24Cp.Pc.v631, CFSG.KD.Fi24Cp.Pc.v632, CFSG.KD.Fi24Cp.Pc.v633, CFSG.KD.Fi24Cp.Pc.v634, CFSG.KD.Fi24Cp.Pc.v635, CFSG.KD.Fi24Cp.Pc.v636]
theorem CFSG.KD.Fi24Cp.Pc.p635 : Nat.beq (runC AR SD 629 (ckL CFSG.KD.Fi24Cp.Pc.l637) 2 635 CFSG.KD.Fi24Cp.Pc.l635) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v637 : Nat := CFSG.KD.Fi24Cp.KV4 132
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v638 : Nat := CFSG.KD.Fi24Cp.KV4 133
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l639 : List Nat := [CFSG.KD.Fi24Cp.Pc.v629, CFSG.KD.Fi24Cp.Pc.v630, CFSG.KD.Fi24Cp.Pc.v631, CFSG.KD.Fi24Cp.Pc.v632, CFSG.KD.Fi24Cp.Pc.v633, CFSG.KD.Fi24Cp.Pc.v634, CFSG.KD.Fi24Cp.Pc.v635, CFSG.KD.Fi24Cp.Pc.v636, CFSG.KD.Fi24Cp.Pc.v637, CFSG.KD.Fi24Cp.Pc.v638]
theorem CFSG.KD.Fi24Cp.Pc.p637 : Nat.beq (runC AR SD 629 (ckL CFSG.KD.Fi24Cp.Pc.l639) 2 637 CFSG.KD.Fi24Cp.Pc.l637) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v639 : Nat := CFSG.KD.Fi24Cp.KV4 134
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v640 : Nat := CFSG.KD.Fi24Cp.KV4 135
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l641 : List Nat := [CFSG.KD.Fi24Cp.Pc.v629, CFSG.KD.Fi24Cp.Pc.v630, CFSG.KD.Fi24Cp.Pc.v631, CFSG.KD.Fi24Cp.Pc.v632, CFSG.KD.Fi24Cp.Pc.v633, CFSG.KD.Fi24Cp.Pc.v634, CFSG.KD.Fi24Cp.Pc.v635, CFSG.KD.Fi24Cp.Pc.v636, CFSG.KD.Fi24Cp.Pc.v637, CFSG.KD.Fi24Cp.Pc.v638, CFSG.KD.Fi24Cp.Pc.v639, CFSG.KD.Fi24Cp.Pc.v640]
theorem CFSG.KD.Fi24Cp.Pc.p639 : Nat.beq (runC AR SD 629 (ckL CFSG.KD.Fi24Cp.Pc.l641) 2 639 CFSG.KD.Fi24Cp.Pc.l639) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v641 : Nat := CFSG.KD.Fi24Cp.KV4 136
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v642 : Nat := CFSG.KD.Fi24Cp.KV4 137
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l643 : List Nat := [CFSG.KD.Fi24Cp.Pc.v629, CFSG.KD.Fi24Cp.Pc.v630, CFSG.KD.Fi24Cp.Pc.v631, CFSG.KD.Fi24Cp.Pc.v632, CFSG.KD.Fi24Cp.Pc.v633, CFSG.KD.Fi24Cp.Pc.v634, CFSG.KD.Fi24Cp.Pc.v635, CFSG.KD.Fi24Cp.Pc.v636, CFSG.KD.Fi24Cp.Pc.v637, CFSG.KD.Fi24Cp.Pc.v638, CFSG.KD.Fi24Cp.Pc.v639, CFSG.KD.Fi24Cp.Pc.v640, CFSG.KD.Fi24Cp.Pc.v641, CFSG.KD.Fi24Cp.Pc.v642]
theorem CFSG.KD.Fi24Cp.Pc.p641 : Nat.beq (runC AR SD 629 (ckL CFSG.KD.Fi24Cp.Pc.l643) 2 641 CFSG.KD.Fi24Cp.Pc.l641) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v643 : Nat := CFSG.KD.Fi24Cp.KV4 138
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v644 : Nat := CFSG.KD.Fi24Cp.KV4 139
theorem CFSG.KD.Fi24Cp.Pc.f49 : Nat.beq (runC AR SD 629 (finC AR SD (nat_lit 49) 629 645) 2 643 CFSG.KD.Fi24Cp.Pc.l643) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk49 : chk (nat_lit 49) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 49) (lo := 629) (hi := 645) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 631) CFSG.KD.Fi24Cp.Pc.p629 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 633) CFSG.KD.Fi24Cp.Pc.p631 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 635) CFSG.KD.Fi24Cp.Pc.p633 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 637) CFSG.KD.Fi24Cp.Pc.p635 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 639) CFSG.KD.Fi24Cp.Pc.p637 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 641) CFSG.KD.Fi24Cp.Pc.p639 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 643) CFSG.KD.Fi24Cp.Pc.p641 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f49

end
