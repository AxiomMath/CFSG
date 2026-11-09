module

public import Certificates.Kernel.Sporadic.Fi24Tc.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Tc KV11 "Certificates/Kernel/Sporadic/Fi24Tc/data/v11.bin" 152491 4 9759424 16556002540262995286

public section

open CFSG.KD.Fi24Tc CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1530 : Nat := CFSG.KD.Fi24Tc.KV11 0
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1531 : Nat := CFSG.KD.Fi24Tc.KV11 1
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1532 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1530, CFSG.KD.Fi24Tc.Pc.v1531]
theorem CFSG.KD.Fi24Tc.Pc.p1530 : Nat.beq (runC AR SD 1530 (ckL CFSG.KD.Fi24Tc.Pc.l1532) 2 1530 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1532_2 : Nat := CFSG.KD.Fi24Tc.KV11 2
theorem CFSG.KD.Fi24Tc.Pc.q1532_2 : Nat.beq (powTop AR.mul (getV AR SD 1530 CFSG.KD.Fi24Tc.Pc.l1532 (SD.na.getD 1532 0)) (SD.nk.getD 1532 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1532_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1532 : Nat := CFSG.KD.Fi24Tc.KV11 3
theorem CFSG.KD.Fi24Tc.Pc.r1532 : Nat.beq (powR AR.mul AR.one (getV AR SD 1530 CFSG.KD.Fi24Tc.Pc.l1532 (SD.na.getD 1532 0)) (SD.nk.getD 1532 1) 2 CFSG.KD.Fi24Tc.Pc.a1532_2 true) CFSG.KD.Fi24Tc.Pc.v1532 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1533 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1530, CFSG.KD.Fi24Tc.Pc.v1531, CFSG.KD.Fi24Tc.Pc.v1532]
theorem CFSG.KD.Fi24Tc.Pc.f220 : Nat.beq (runC AR SD 1530 (finC AR SD (nat_lit 220) 1530 1533) 0 1533 CFSG.KD.Fi24Tc.Pc.l1533) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk220 : chk (nat_lit 220) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 220) (lo := 1530) (hi := 1533) (m := 3) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 3) (m2 := 1) (j2 := 1532) CFSG.KD.Fi24Tc.Pc.p1530 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 1533) (Lr := CFSG.KD.Fi24Tc.Pc.l1533) ((nodeV_pow (R := AR) (D := SD) (lo := 1530) (L := CFSG.KD.Fi24Tc.Pc.l1532) (j := 1532) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1530 CFSG.KD.Fi24Tc.Pc.l1532 (SD.na.getD 1532 0)) (SD.nk.getD 1532 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1532_2 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1532)))) (by quickRfl) rfl rfl rfl)))).trans CFSG.KD.Fi24Tc.Pc.f220

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1533_3 : Nat := CFSG.KD.Fi24Tc.KV11 4
theorem CFSG.KD.Fi24Tc.Pc.q1533_3 : Nat.beq (powTop AR.mul (getV AR SD 1533 [] (SD.na.getD 1533 0)) (SD.nk.getD 1533 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a1533_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1533_2 : Nat := CFSG.KD.Fi24Tc.KV11 5
theorem CFSG.KD.Fi24Tc.Pc.q1533_2 : Nat.beq (powTop AR.mul (getV AR SD 1533 [] (SD.na.getD 1533 0)) (SD.nk.getD 1533 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1533_2) 1 CFSG.KD.Fi24Tc.Pc.a1533_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1533_1 : Nat := CFSG.KD.Fi24Tc.KV11 6
theorem CFSG.KD.Fi24Tc.Pc.q1533_1 : Nat.beq (powTop AR.mul (getV AR SD 1533 [] (SD.na.getD 1533 0)) (SD.nk.getD 1533 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a1533_1) 1 CFSG.KD.Fi24Tc.Pc.a1533_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1533 : Nat := CFSG.KD.Fi24Tc.KV11 7
theorem CFSG.KD.Fi24Tc.Pc.r1533 : Nat.beq (powR AR.mul AR.one (getV AR SD 1533 [] (SD.na.getD 1533 0)) (SD.nk.getD 1533 1) 1 CFSG.KD.Fi24Tc.Pc.a1533_1 true) CFSG.KD.Fi24Tc.Pc.v1533 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1534 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1533]
theorem CFSG.KD.Fi24Tc.Pc.f221 : Nat.beq (runC AR SD 1533 (finC AR SD (nat_lit 221) 1533 1534) 0 1534 CFSG.KD.Fi24Tc.Pc.l1534) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk221 : chk (nat_lit 221) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 221) (lo := 1533) (hi := 1534) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 1534) (Lr := CFSG.KD.Fi24Tc.Pc.l1534) ((nodeV_pow (R := AR) (D := SD) (lo := 1533) (L := []) (j := 1533) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1533 [] (SD.na.getD 1533 0)) (SD.nk.getD 1533 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1533_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q1533_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q1533_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1533)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f221

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1534_3 : Nat := CFSG.KD.Fi24Tc.KV11 8
theorem CFSG.KD.Fi24Tc.Pc.q1534_3 : Nat.beq (powTop AR.mul (getV AR SD 1534 [] (SD.na.getD 1534 0)) (SD.nk.getD 1534 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a1534_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1534_2 : Nat := CFSG.KD.Fi24Tc.KV11 9
theorem CFSG.KD.Fi24Tc.Pc.q1534_2 : Nat.beq (powTop AR.mul (getV AR SD 1534 [] (SD.na.getD 1534 0)) (SD.nk.getD 1534 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1534_2) 1 CFSG.KD.Fi24Tc.Pc.a1534_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1534_1 : Nat := CFSG.KD.Fi24Tc.KV11 10
theorem CFSG.KD.Fi24Tc.Pc.q1534_1 : Nat.beq (powTop AR.mul (getV AR SD 1534 [] (SD.na.getD 1534 0)) (SD.nk.getD 1534 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a1534_1) 1 CFSG.KD.Fi24Tc.Pc.a1534_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1534 : Nat := CFSG.KD.Fi24Tc.KV11 11
theorem CFSG.KD.Fi24Tc.Pc.r1534 : Nat.beq (powR AR.mul AR.one (getV AR SD 1534 [] (SD.na.getD 1534 0)) (SD.nk.getD 1534 1) 1 CFSG.KD.Fi24Tc.Pc.a1534_1 true) CFSG.KD.Fi24Tc.Pc.v1534 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1535 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1534]
theorem CFSG.KD.Fi24Tc.Pc.f222 : Nat.beq (runC AR SD 1534 (finC AR SD (nat_lit 222) 1534 1535) 0 1535 CFSG.KD.Fi24Tc.Pc.l1535) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk222 : chk (nat_lit 222) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 222) (lo := 1534) (hi := 1535) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 1535) (Lr := CFSG.KD.Fi24Tc.Pc.l1535) ((nodeV_pow (R := AR) (D := SD) (lo := 1534) (L := []) (j := 1534) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1534 [] (SD.na.getD 1534 0)) (SD.nk.getD 1534 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1534_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q1534_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q1534_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1534)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f222

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1535_3 : Nat := CFSG.KD.Fi24Tc.KV11 12
theorem CFSG.KD.Fi24Tc.Pc.q1535_3 : Nat.beq (powTop AR.mul (getV AR SD 1535 [] (SD.na.getD 1535 0)) (SD.nk.getD 1535 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a1535_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1535_2 : Nat := CFSG.KD.Fi24Tc.KV11 13
theorem CFSG.KD.Fi24Tc.Pc.q1535_2 : Nat.beq (powTop AR.mul (getV AR SD 1535 [] (SD.na.getD 1535 0)) (SD.nk.getD 1535 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1535_2) 1 CFSG.KD.Fi24Tc.Pc.a1535_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1535 : Nat := CFSG.KD.Fi24Tc.KV11 14
theorem CFSG.KD.Fi24Tc.Pc.r1535 : Nat.beq (powR AR.mul AR.one (getV AR SD 1535 [] (SD.na.getD 1535 0)) (SD.nk.getD 1535 1) 2 CFSG.KD.Fi24Tc.Pc.a1535_2 true) CFSG.KD.Fi24Tc.Pc.v1535 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1536 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1535]
theorem CFSG.KD.Fi24Tc.Pc.f223 : Nat.beq (runC AR SD 1535 (finC AR SD (nat_lit 223) 1535 1536) 0 1536 CFSG.KD.Fi24Tc.Pc.l1536) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk223 : chk (nat_lit 223) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 223) (lo := 1535) (hi := 1536) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 1536) (Lr := CFSG.KD.Fi24Tc.Pc.l1536) ((nodeV_pow (R := AR) (D := SD) (lo := 1535) (L := []) (j := 1535) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1535 [] (SD.na.getD 1535 0)) (SD.nk.getD 1535 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1535_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q1535_2 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1535))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f223

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1536_3 : Nat := CFSG.KD.Fi24Tc.KV11 46
theorem CFSG.KD.Fi24Tc.Pc.q1536_3 : Nat.beq (powTop AR.mul (getV AR SD 1536 [] (SD.na.getD 1536 0)) (SD.nk.getD 1536 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a1536_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1536_1 : Nat := CFSG.KD.Fi24Tc.KV11 47
theorem CFSG.KD.Fi24Tc.Pc.q1536_1 : Nat.beq (powTop AR.mul (getV AR SD 1536 [] (SD.na.getD 1536 0)) (SD.nk.getD 1536 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a1536_1) 2 CFSG.KD.Fi24Tc.Pc.a1536_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1536 : Nat := CFSG.KD.Fi24Tc.KV11 48
theorem CFSG.KD.Fi24Tc.Pc.r1536 : Nat.beq (powR AR.mul AR.one (getV AR SD 1536 [] (SD.na.getD 1536 0)) (SD.nk.getD 1536 1) 1 CFSG.KD.Fi24Tc.Pc.a1536_1 true) CFSG.KD.Fi24Tc.Pc.v1536 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1537 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1536]
theorem CFSG.KD.Fi24Tc.Pc.f224 : Nat.beq (runC AR SD 1536 (finC AR SD (nat_lit 224) 1536 1537) 0 1537 CFSG.KD.Fi24Tc.Pc.l1537) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk224 : chk (nat_lit 224) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 224) (lo := 1536) (hi := 1537) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 1537) (Lr := CFSG.KD.Fi24Tc.Pc.l1537) ((nodeV_pow (R := AR) (D := SD) (lo := 1536) (L := []) (j := 1536) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1536 [] (SD.na.getD 1536 0)) (SD.nk.getD 1536 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1536_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q1536_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1536))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f224

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1537_3 : Nat := CFSG.KD.Fi24Tc.KV11 49
theorem CFSG.KD.Fi24Tc.Pc.q1537_3 : Nat.beq (powTop AR.mul (getV AR SD 1537 [] (SD.na.getD 1537 0)) (SD.nk.getD 1537 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a1537_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1537_1 : Nat := CFSG.KD.Fi24Tc.KV11 50
theorem CFSG.KD.Fi24Tc.Pc.q1537_1 : Nat.beq (powTop AR.mul (getV AR SD 1537 [] (SD.na.getD 1537 0)) (SD.nk.getD 1537 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a1537_1) 2 CFSG.KD.Fi24Tc.Pc.a1537_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1537 : Nat := CFSG.KD.Fi24Tc.KV11 51
theorem CFSG.KD.Fi24Tc.Pc.r1537 : Nat.beq (powR AR.mul AR.one (getV AR SD 1537 [] (SD.na.getD 1537 0)) (SD.nk.getD 1537 1) 1 CFSG.KD.Fi24Tc.Pc.a1537_1 true) CFSG.KD.Fi24Tc.Pc.v1537 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1538 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1537]
theorem CFSG.KD.Fi24Tc.Pc.f225 : Nat.beq (runC AR SD 1537 (finC AR SD (nat_lit 225) 1537 1538) 0 1538 CFSG.KD.Fi24Tc.Pc.l1538) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk225 : chk (nat_lit 225) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 225) (lo := 1537) (hi := 1538) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 1538) (Lr := CFSG.KD.Fi24Tc.Pc.l1538) ((nodeV_pow (R := AR) (D := SD) (lo := 1537) (L := []) (j := 1537) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1537 [] (SD.na.getD 1537 0)) (SD.nk.getD 1537 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1537_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q1537_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1537))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f225

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1538_2 : Nat := CFSG.KD.Fi24Tc.KV11 52
theorem CFSG.KD.Fi24Tc.Pc.q1538_2 : Nat.beq (powTop AR.mul (getV AR SD 1538 [] (SD.na.getD 1538 0)) (SD.nk.getD 1538 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1538_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1538_1 : Nat := CFSG.KD.Fi24Tc.KV11 53
theorem CFSG.KD.Fi24Tc.Pc.q1538_1 : Nat.beq (powTop AR.mul (getV AR SD 1538 [] (SD.na.getD 1538 0)) (SD.nk.getD 1538 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a1538_1) 1 CFSG.KD.Fi24Tc.Pc.a1538_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1538 : Nat := CFSG.KD.Fi24Tc.KV11 54
theorem CFSG.KD.Fi24Tc.Pc.r1538 : Nat.beq (powR AR.mul AR.one (getV AR SD 1538 [] (SD.na.getD 1538 0)) (SD.nk.getD 1538 1) 1 CFSG.KD.Fi24Tc.Pc.a1538_1 true) CFSG.KD.Fi24Tc.Pc.v1538 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1539 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1538]
theorem CFSG.KD.Fi24Tc.Pc.f226 : Nat.beq (runC AR SD 1538 (finC AR SD (nat_lit 226) 1538 1539) 0 1539 CFSG.KD.Fi24Tc.Pc.l1539) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk226 : chk (nat_lit 226) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 226) (lo := 1538) (hi := 1539) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 1539) (Lr := CFSG.KD.Fi24Tc.Pc.l1539) ((nodeV_pow (R := AR) (D := SD) (lo := 1538) (L := []) (j := 1538) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1538 [] (SD.na.getD 1538 0)) (SD.nk.getD 1538 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1538_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q1538_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1538))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f226

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1539_2 : Nat := CFSG.KD.Fi24Tc.KV11 55
theorem CFSG.KD.Fi24Tc.Pc.q1539_2 : Nat.beq (powTop AR.mul (getV AR SD 1539 [] (SD.na.getD 1539 0)) (SD.nk.getD 1539 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1539_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1539_1 : Nat := CFSG.KD.Fi24Tc.KV11 56
theorem CFSG.KD.Fi24Tc.Pc.q1539_1 : Nat.beq (powTop AR.mul (getV AR SD 1539 [] (SD.na.getD 1539 0)) (SD.nk.getD 1539 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a1539_1) 1 CFSG.KD.Fi24Tc.Pc.a1539_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1539 : Nat := CFSG.KD.Fi24Tc.KV11 57
theorem CFSG.KD.Fi24Tc.Pc.r1539 : Nat.beq (powR AR.mul AR.one (getV AR SD 1539 [] (SD.na.getD 1539 0)) (SD.nk.getD 1539 1) 1 CFSG.KD.Fi24Tc.Pc.a1539_1 true) CFSG.KD.Fi24Tc.Pc.v1539 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1540 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1539]
theorem CFSG.KD.Fi24Tc.Pc.f227 : Nat.beq (runC AR SD 1539 (finC AR SD (nat_lit 227) 1539 1540) 0 1540 CFSG.KD.Fi24Tc.Pc.l1540) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk227 : chk (nat_lit 227) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 227) (lo := 1539) (hi := 1540) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 1540) (Lr := CFSG.KD.Fi24Tc.Pc.l1540) ((nodeV_pow (R := AR) (D := SD) (lo := 1539) (L := []) (j := 1539) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1539 [] (SD.na.getD 1539 0)) (SD.nk.getD 1539 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1539_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q1539_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1539))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f227

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1540_3 : Nat := CFSG.KD.Fi24Tc.KV11 15
theorem CFSG.KD.Fi24Tc.Pc.q1540_3 : Nat.beq (powTop AR.mul (getV AR SD 1540 [] (SD.na.getD 1540 0)) (SD.nk.getD 1540 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a1540_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1540_2 : Nat := CFSG.KD.Fi24Tc.KV11 16
theorem CFSG.KD.Fi24Tc.Pc.q1540_2 : Nat.beq (powTop AR.mul (getV AR SD 1540 [] (SD.na.getD 1540 0)) (SD.nk.getD 1540 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1540_2) 1 CFSG.KD.Fi24Tc.Pc.a1540_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1540_1 : Nat := CFSG.KD.Fi24Tc.KV11 17
theorem CFSG.KD.Fi24Tc.Pc.q1540_1 : Nat.beq (powTop AR.mul (getV AR SD 1540 [] (SD.na.getD 1540 0)) (SD.nk.getD 1540 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a1540_1) 1 CFSG.KD.Fi24Tc.Pc.a1540_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1540 : Nat := CFSG.KD.Fi24Tc.KV11 18
theorem CFSG.KD.Fi24Tc.Pc.r1540 : Nat.beq (powR AR.mul AR.one (getV AR SD 1540 [] (SD.na.getD 1540 0)) (SD.nk.getD 1540 1) 1 CFSG.KD.Fi24Tc.Pc.a1540_1 true) CFSG.KD.Fi24Tc.Pc.v1540 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1541 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1540]
theorem CFSG.KD.Fi24Tc.Pc.f228 : Nat.beq (runC AR SD 1540 (finC AR SD (nat_lit 228) 1540 1541) 0 1541 CFSG.KD.Fi24Tc.Pc.l1541) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk228 : chk (nat_lit 228) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 228) (lo := 1540) (hi := 1541) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 1541) (Lr := CFSG.KD.Fi24Tc.Pc.l1541) ((nodeV_pow (R := AR) (D := SD) (lo := 1540) (L := []) (j := 1540) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1540 [] (SD.na.getD 1540 0)) (SD.nk.getD 1540 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1540_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q1540_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q1540_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1540)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f228

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1541_3 : Nat := CFSG.KD.Fi24Tc.KV11 19
theorem CFSG.KD.Fi24Tc.Pc.q1541_3 : Nat.beq (powTop AR.mul (getV AR SD 1541 [] (SD.na.getD 1541 0)) (SD.nk.getD 1541 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a1541_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1541_2 : Nat := CFSG.KD.Fi24Tc.KV11 20
theorem CFSG.KD.Fi24Tc.Pc.q1541_2 : Nat.beq (powTop AR.mul (getV AR SD 1541 [] (SD.na.getD 1541 0)) (SD.nk.getD 1541 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1541_2) 1 CFSG.KD.Fi24Tc.Pc.a1541_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1541_1 : Nat := CFSG.KD.Fi24Tc.KV11 21
theorem CFSG.KD.Fi24Tc.Pc.q1541_1 : Nat.beq (powTop AR.mul (getV AR SD 1541 [] (SD.na.getD 1541 0)) (SD.nk.getD 1541 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a1541_1) 1 CFSG.KD.Fi24Tc.Pc.a1541_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1541 : Nat := CFSG.KD.Fi24Tc.KV11 22
theorem CFSG.KD.Fi24Tc.Pc.r1541 : Nat.beq (powR AR.mul AR.one (getV AR SD 1541 [] (SD.na.getD 1541 0)) (SD.nk.getD 1541 1) 1 CFSG.KD.Fi24Tc.Pc.a1541_1 true) CFSG.KD.Fi24Tc.Pc.v1541 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1542 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1541]
theorem CFSG.KD.Fi24Tc.Pc.f229 : Nat.beq (runC AR SD 1541 (finC AR SD (nat_lit 229) 1541 1542) 0 1542 CFSG.KD.Fi24Tc.Pc.l1542) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk229 : chk (nat_lit 229) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 229) (lo := 1541) (hi := 1542) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 1542) (Lr := CFSG.KD.Fi24Tc.Pc.l1542) ((nodeV_pow (R := AR) (D := SD) (lo := 1541) (L := []) (j := 1541) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1541 [] (SD.na.getD 1541 0)) (SD.nk.getD 1541 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1541_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q1541_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q1541_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1541)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f229

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1542_3 : Nat := CFSG.KD.Fi24Tc.KV11 23
theorem CFSG.KD.Fi24Tc.Pc.q1542_3 : Nat.beq (powTop AR.mul (getV AR SD 1542 [] (SD.na.getD 1542 0)) (SD.nk.getD 1542 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a1542_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1542_2 : Nat := CFSG.KD.Fi24Tc.KV11 24
theorem CFSG.KD.Fi24Tc.Pc.q1542_2 : Nat.beq (powTop AR.mul (getV AR SD 1542 [] (SD.na.getD 1542 0)) (SD.nk.getD 1542 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1542_2) 1 CFSG.KD.Fi24Tc.Pc.a1542_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1542_1 : Nat := CFSG.KD.Fi24Tc.KV11 25
theorem CFSG.KD.Fi24Tc.Pc.q1542_1 : Nat.beq (powTop AR.mul (getV AR SD 1542 [] (SD.na.getD 1542 0)) (SD.nk.getD 1542 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a1542_1) 1 CFSG.KD.Fi24Tc.Pc.a1542_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1542 : Nat := CFSG.KD.Fi24Tc.KV11 26
theorem CFSG.KD.Fi24Tc.Pc.r1542 : Nat.beq (powR AR.mul AR.one (getV AR SD 1542 [] (SD.na.getD 1542 0)) (SD.nk.getD 1542 1) 1 CFSG.KD.Fi24Tc.Pc.a1542_1 true) CFSG.KD.Fi24Tc.Pc.v1542 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1543 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1542]
theorem CFSG.KD.Fi24Tc.Pc.f230 : Nat.beq (runC AR SD 1542 (finC AR SD (nat_lit 230) 1542 1543) 0 1543 CFSG.KD.Fi24Tc.Pc.l1543) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk230 : chk (nat_lit 230) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 230) (lo := 1542) (hi := 1543) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 1543) (Lr := CFSG.KD.Fi24Tc.Pc.l1543) ((nodeV_pow (R := AR) (D := SD) (lo := 1542) (L := []) (j := 1542) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1542 [] (SD.na.getD 1542 0)) (SD.nk.getD 1542 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1542_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q1542_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q1542_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1542)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f230

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1543_3 : Nat := CFSG.KD.Fi24Tc.KV11 27
theorem CFSG.KD.Fi24Tc.Pc.q1543_3 : Nat.beq (powTop AR.mul (getV AR SD 1543 [] (SD.na.getD 1543 0)) (SD.nk.getD 1543 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a1543_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1543_2 : Nat := CFSG.KD.Fi24Tc.KV11 28
theorem CFSG.KD.Fi24Tc.Pc.q1543_2 : Nat.beq (powTop AR.mul (getV AR SD 1543 [] (SD.na.getD 1543 0)) (SD.nk.getD 1543 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1543_2) 1 CFSG.KD.Fi24Tc.Pc.a1543_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1543_1 : Nat := CFSG.KD.Fi24Tc.KV11 29
theorem CFSG.KD.Fi24Tc.Pc.q1543_1 : Nat.beq (powTop AR.mul (getV AR SD 1543 [] (SD.na.getD 1543 0)) (SD.nk.getD 1543 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a1543_1) 1 CFSG.KD.Fi24Tc.Pc.a1543_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1543 : Nat := CFSG.KD.Fi24Tc.KV11 30
theorem CFSG.KD.Fi24Tc.Pc.r1543 : Nat.beq (powR AR.mul AR.one (getV AR SD 1543 [] (SD.na.getD 1543 0)) (SD.nk.getD 1543 1) 1 CFSG.KD.Fi24Tc.Pc.a1543_1 true) CFSG.KD.Fi24Tc.Pc.v1543 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1544 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1543]
theorem CFSG.KD.Fi24Tc.Pc.f231 : Nat.beq (runC AR SD 1543 (finC AR SD (nat_lit 231) 1543 1544) 0 1544 CFSG.KD.Fi24Tc.Pc.l1544) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk231 : chk (nat_lit 231) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 231) (lo := 1543) (hi := 1544) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 1544) (Lr := CFSG.KD.Fi24Tc.Pc.l1544) ((nodeV_pow (R := AR) (D := SD) (lo := 1543) (L := []) (j := 1543) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1543 [] (SD.na.getD 1543 0)) (SD.nk.getD 1543 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1543_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q1543_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q1543_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1543)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f231

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1544_2 : Nat := CFSG.KD.Fi24Tc.KV11 58
theorem CFSG.KD.Fi24Tc.Pc.q1544_2 : Nat.beq (powTop AR.mul (getV AR SD 1544 [] (SD.na.getD 1544 0)) (SD.nk.getD 1544 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1544_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1544_1 : Nat := CFSG.KD.Fi24Tc.KV11 59
theorem CFSG.KD.Fi24Tc.Pc.q1544_1 : Nat.beq (powTop AR.mul (getV AR SD 1544 [] (SD.na.getD 1544 0)) (SD.nk.getD 1544 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a1544_1) 1 CFSG.KD.Fi24Tc.Pc.a1544_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1544 : Nat := CFSG.KD.Fi24Tc.KV11 60
theorem CFSG.KD.Fi24Tc.Pc.r1544 : Nat.beq (powR AR.mul AR.one (getV AR SD 1544 [] (SD.na.getD 1544 0)) (SD.nk.getD 1544 1) 1 CFSG.KD.Fi24Tc.Pc.a1544_1 true) CFSG.KD.Fi24Tc.Pc.v1544 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1545 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1544]
theorem CFSG.KD.Fi24Tc.Pc.f232 : Nat.beq (runC AR SD 1544 (finC AR SD (nat_lit 232) 1544 1545) 0 1545 CFSG.KD.Fi24Tc.Pc.l1545) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk232 : chk (nat_lit 232) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 232) (lo := 1544) (hi := 1545) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 1545) (Lr := CFSG.KD.Fi24Tc.Pc.l1545) ((nodeV_pow (R := AR) (D := SD) (lo := 1544) (L := []) (j := 1544) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1544 [] (SD.na.getD 1544 0)) (SD.nk.getD 1544 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1544_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q1544_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1544))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f232

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1545_2 : Nat := CFSG.KD.Fi24Tc.KV11 61
theorem CFSG.KD.Fi24Tc.Pc.q1545_2 : Nat.beq (powTop AR.mul (getV AR SD 1545 [] (SD.na.getD 1545 0)) (SD.nk.getD 1545 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1545_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1545_1 : Nat := CFSG.KD.Fi24Tc.KV11 62
theorem CFSG.KD.Fi24Tc.Pc.q1545_1 : Nat.beq (powTop AR.mul (getV AR SD 1545 [] (SD.na.getD 1545 0)) (SD.nk.getD 1545 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a1545_1) 1 CFSG.KD.Fi24Tc.Pc.a1545_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1545 : Nat := CFSG.KD.Fi24Tc.KV11 63
theorem CFSG.KD.Fi24Tc.Pc.r1545 : Nat.beq (powR AR.mul AR.one (getV AR SD 1545 [] (SD.na.getD 1545 0)) (SD.nk.getD 1545 1) 1 CFSG.KD.Fi24Tc.Pc.a1545_1 true) CFSG.KD.Fi24Tc.Pc.v1545 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1546 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1545]
theorem CFSG.KD.Fi24Tc.Pc.f233 : Nat.beq (runC AR SD 1545 (finC AR SD (nat_lit 233) 1545 1546) 0 1546 CFSG.KD.Fi24Tc.Pc.l1546) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk233 : chk (nat_lit 233) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 233) (lo := 1545) (hi := 1546) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 1546) (Lr := CFSG.KD.Fi24Tc.Pc.l1546) ((nodeV_pow (R := AR) (D := SD) (lo := 1545) (L := []) (j := 1545) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1545 [] (SD.na.getD 1545 0)) (SD.nk.getD 1545 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1545_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q1545_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1545))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f233

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1546_1 : Nat := CFSG.KD.Fi24Tc.KV11 31
theorem CFSG.KD.Fi24Tc.Pc.q1546_1 : Nat.beq (powTop AR.mul (getV AR SD 1546 [] (SD.na.getD 1546 0)) (SD.nk.getD 1546 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a1546_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1546 : Nat := CFSG.KD.Fi24Tc.KV11 32
theorem CFSG.KD.Fi24Tc.Pc.r1546 : Nat.beq (powR AR.mul AR.one (getV AR SD 1546 [] (SD.na.getD 1546 0)) (SD.nk.getD 1546 1) 1 CFSG.KD.Fi24Tc.Pc.a1546_1 true) CFSG.KD.Fi24Tc.Pc.v1546 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1547 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1546]
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1547_1 : Nat := CFSG.KD.Fi24Tc.KV11 33
theorem CFSG.KD.Fi24Tc.Pc.q1547_1 : Nat.beq (powTop AR.mul (getV AR SD 1546 CFSG.KD.Fi24Tc.Pc.l1547 (SD.na.getD 1547 0)) (SD.nk.getD 1547 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a1547_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1547 : Nat := CFSG.KD.Fi24Tc.KV11 34
theorem CFSG.KD.Fi24Tc.Pc.r1547 : Nat.beq (powR AR.mul AR.one (getV AR SD 1546 CFSG.KD.Fi24Tc.Pc.l1547 (SD.na.getD 1547 0)) (SD.nk.getD 1547 1) 1 CFSG.KD.Fi24Tc.Pc.a1547_1 true) CFSG.KD.Fi24Tc.Pc.v1547 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1548 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1546, CFSG.KD.Fi24Tc.Pc.v1547]
theorem CFSG.KD.Fi24Tc.Pc.f234 : Nat.beq (runC AR SD 1546 (finC AR SD (nat_lit 234) 1546 1548) 0 1548 CFSG.KD.Fi24Tc.Pc.l1548) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk234 : chk (nat_lit 234) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 234) (lo := 1546) (hi := 1548) (m := 2) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 2) (m2 := 1) (j2 := 1547) (Lr := CFSG.KD.Fi24Tc.Pc.l1547) ((nodeV_pow (R := AR) (D := SD) (lo := 1546) (L := []) (j := 1546) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1546 [] (SD.na.getD 1546 0)) (SD.nk.getD 1546 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1546_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1546)))) (by quickRfl) rfl rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 1548) (Lr := CFSG.KD.Fi24Tc.Pc.l1548) ((nodeV_pow (R := AR) (D := SD) (lo := 1546) (L := CFSG.KD.Fi24Tc.Pc.l1547) (j := 1547) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1546 CFSG.KD.Fi24Tc.Pc.l1547 (SD.na.getD 1547 0)) (SD.nk.getD 1547 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1547_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1547)))) (by quickRfl) rfl rfl rfl)))).trans CFSG.KD.Fi24Tc.Pc.f234

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1548 : Nat := CFSG.KD.Fi24Tc.KV11 35
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1549 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1548]
theorem CFSG.KD.Fi24Tc.Pc.p1548 : Nat.beq (runC AR SD 1548 (ckL CFSG.KD.Fi24Tc.Pc.l1549) 1 1548 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1549 : Nat := CFSG.KD.Fi24Tc.KV11 36
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1550 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1548, CFSG.KD.Fi24Tc.Pc.v1549]
theorem CFSG.KD.Fi24Tc.Pc.p1549 : Nat.beq (runC AR SD 1548 (ckL CFSG.KD.Fi24Tc.Pc.l1550) 1 1549 CFSG.KD.Fi24Tc.Pc.l1549) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1550_2 : Nat := CFSG.KD.Fi24Tc.KV11 37
theorem CFSG.KD.Fi24Tc.Pc.q1550_2 : Nat.beq (powTop AR.mul (getV AR SD 1548 CFSG.KD.Fi24Tc.Pc.l1550 (SD.na.getD 1550 0)) (SD.nk.getD 1550 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1550_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1550 : Nat := CFSG.KD.Fi24Tc.KV11 38
theorem CFSG.KD.Fi24Tc.Pc.r1550 : Nat.beq (powR AR.mul AR.one (getV AR SD 1548 CFSG.KD.Fi24Tc.Pc.l1550 (SD.na.getD 1550 0)) (SD.nk.getD 1550 1) 2 CFSG.KD.Fi24Tc.Pc.a1550_2 true) CFSG.KD.Fi24Tc.Pc.v1550 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1551 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1548, CFSG.KD.Fi24Tc.Pc.v1549, CFSG.KD.Fi24Tc.Pc.v1550]
theorem CFSG.KD.Fi24Tc.Pc.f235 : Nat.beq (runC AR SD 1548 (finC AR SD (nat_lit 235) 1548 1551) 0 1551 CFSG.KD.Fi24Tc.Pc.l1551) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk235 : chk (nat_lit 235) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 235) (lo := 1548) (hi := 1551) (m := 3) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 3) (m2 := 2) (j2 := 1549) CFSG.KD.Fi24Tc.Pc.p1548 rfl rfl).trans ((runC_seq (m := 2) (m2 := 1) (j2 := 1550) CFSG.KD.Fi24Tc.Pc.p1549 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 1551) (Lr := CFSG.KD.Fi24Tc.Pc.l1551) ((nodeV_pow (R := AR) (D := SD) (lo := 1548) (L := CFSG.KD.Fi24Tc.Pc.l1550) (j := 1550) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1548 CFSG.KD.Fi24Tc.Pc.l1550 (SD.na.getD 1550 0)) (SD.nk.getD 1550 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1550_2 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1550)))) (by quickRfl) rfl rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f235

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1551_2 : Nat := CFSG.KD.Fi24Tc.KV11 39
theorem CFSG.KD.Fi24Tc.Pc.q1551_2 : Nat.beq (powTop AR.mul (getV AR SD 1551 [] (SD.na.getD 1551 0)) (SD.nk.getD 1551 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1551_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1551 : Nat := CFSG.KD.Fi24Tc.KV11 40
theorem CFSG.KD.Fi24Tc.Pc.r1551 : Nat.beq (powR AR.mul AR.one (getV AR SD 1551 [] (SD.na.getD 1551 0)) (SD.nk.getD 1551 1) 2 CFSG.KD.Fi24Tc.Pc.a1551_2 true) CFSG.KD.Fi24Tc.Pc.v1551 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1552 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1551]
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1552_2 : Nat := CFSG.KD.Fi24Tc.KV11 41
theorem CFSG.KD.Fi24Tc.Pc.q1552_2 : Nat.beq (powTop AR.mul (getV AR SD 1551 CFSG.KD.Fi24Tc.Pc.l1552 (SD.na.getD 1552 0)) (SD.nk.getD 1552 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1552_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1552 : Nat := CFSG.KD.Fi24Tc.KV11 42
theorem CFSG.KD.Fi24Tc.Pc.r1552 : Nat.beq (powR AR.mul AR.one (getV AR SD 1551 CFSG.KD.Fi24Tc.Pc.l1552 (SD.na.getD 1552 0)) (SD.nk.getD 1552 1) 2 CFSG.KD.Fi24Tc.Pc.a1552_2 true) CFSG.KD.Fi24Tc.Pc.v1552 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1553 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1551, CFSG.KD.Fi24Tc.Pc.v1552]
theorem CFSG.KD.Fi24Tc.Pc.f236 : Nat.beq (runC AR SD 1551 (finC AR SD (nat_lit 236) 1551 1553) 0 1553 CFSG.KD.Fi24Tc.Pc.l1553) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk236 : chk (nat_lit 236) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 236) (lo := 1551) (hi := 1553) (m := 2) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 2) (m2 := 1) (j2 := 1552) (Lr := CFSG.KD.Fi24Tc.Pc.l1552) ((nodeV_pow (R := AR) (D := SD) (lo := 1551) (L := []) (j := 1551) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1551 [] (SD.na.getD 1551 0)) (SD.nk.getD 1551 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1551_2 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1551)))) (by quickRfl) rfl rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 1553) (Lr := CFSG.KD.Fi24Tc.Pc.l1553) ((nodeV_pow (R := AR) (D := SD) (lo := 1551) (L := CFSG.KD.Fi24Tc.Pc.l1552) (j := 1552) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1551 CFSG.KD.Fi24Tc.Pc.l1552 (SD.na.getD 1552 0)) (SD.nk.getD 1552 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1552_2 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1552)))) (by quickRfl) rfl rfl rfl)))).trans CFSG.KD.Fi24Tc.Pc.f236

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1553_2 : Nat := CFSG.KD.Fi24Tc.KV11 43
theorem CFSG.KD.Fi24Tc.Pc.q1553_2 : Nat.beq (powTop AR.mul (getV AR SD 1553 [] (SD.na.getD 1553 0)) (SD.nk.getD 1553 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1553_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1553 : Nat := CFSG.KD.Fi24Tc.KV11 44
theorem CFSG.KD.Fi24Tc.Pc.r1553 : Nat.beq (powR AR.mul AR.one (getV AR SD 1553 [] (SD.na.getD 1553 0)) (SD.nk.getD 1553 1) 2 CFSG.KD.Fi24Tc.Pc.a1553_2 true) CFSG.KD.Fi24Tc.Pc.v1553 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1554 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1553]
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1554 : Nat := CFSG.KD.Fi24Tc.KV11 45
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1555 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1553, CFSG.KD.Fi24Tc.Pc.v1554]
theorem CFSG.KD.Fi24Tc.Pc.p1554 : Nat.beq (runC AR SD 1553 (ckL CFSG.KD.Fi24Tc.Pc.l1555) 1 1554 CFSG.KD.Fi24Tc.Pc.l1554) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f237 : Nat.beq (runC AR SD 1553 (finC AR SD (nat_lit 237) 1553 1556) 1 1555 CFSG.KD.Fi24Tc.Pc.l1555) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk237 : chk (nat_lit 237) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 237) (lo := 1553) (hi := 1556) (m := 3) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 3) (m2 := 2) (j2 := 1554) (Lr := CFSG.KD.Fi24Tc.Pc.l1554) ((nodeV_pow (R := AR) (D := SD) (lo := 1553) (L := []) (j := 1553) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1553 [] (SD.na.getD 1553 0)) (SD.nk.getD 1553 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1553_2 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1553)))) (by quickRfl) rfl rfl rfl).trans (runC_seq (m := 2) (m2 := 1) (j2 := 1555) CFSG.KD.Fi24Tc.Pc.p1554 rfl rfl)))).trans CFSG.KD.Fi24Tc.Pc.f237

theorem CFSG.KD.Fi24Tc.Pc.f238 : Nat.beq (runC AR SD 1556 (finC AR SD (nat_lit 238) 1556 1557) 1 1556 []) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk238 : chk (nat_lit 238) = true :=
  (chunkOK_eq (R := AR) (D := SD) (c := nat_lit 238) (lo := 1556) (hi := 1557) (m := 1) rfl rfl rfl).trans CFSG.KD.Fi24Tc.Pc.f238

end
