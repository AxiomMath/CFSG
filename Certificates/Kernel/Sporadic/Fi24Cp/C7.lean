module

public import Certificates.Kernel.Sporadic.Fi24Cp.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Cp KV7 "Certificates/Kernel/Sporadic/Fi24Cp/data/v7.bin" 152491 4 11436825 2305647703083431015

public section

open CFSG.KD.Fi24Cp CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v939 : Nat := CFSG.KD.Fi24Cp.KV7 0
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l940 : List Nat := [CFSG.KD.Fi24Cp.Pc.v939]
theorem CFSG.KD.Fi24Cp.Pc.p939 : Nat.beq (runC AR SD 939 (ckL CFSG.KD.Fi24Cp.Pc.l940) 1 939 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a940_3 : Nat := CFSG.KD.Fi24Cp.KV7 1
theorem CFSG.KD.Fi24Cp.Pc.q940_3 : Nat.beq (powTop AR.mul (getV AR SD 939 CFSG.KD.Fi24Cp.Pc.l940 (SD.na.getD 940 0)) (SD.nk.getD 940 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a940_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a940_2 : Nat := CFSG.KD.Fi24Cp.KV7 2
theorem CFSG.KD.Fi24Cp.Pc.q940_2 : Nat.beq (powTop AR.mul (getV AR SD 939 CFSG.KD.Fi24Cp.Pc.l940 (SD.na.getD 940 0)) (SD.nk.getD 940 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a940_2) 1 CFSG.KD.Fi24Cp.Pc.a940_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v940 : Nat := CFSG.KD.Fi24Cp.KV7 3
theorem CFSG.KD.Fi24Cp.Pc.r940 : Nat.beq (powR AR.mul AR.one (getV AR SD 939 CFSG.KD.Fi24Cp.Pc.l940 (SD.na.getD 940 0)) (SD.nk.getD 940 1) 2 CFSG.KD.Fi24Cp.Pc.a940_2 true) CFSG.KD.Fi24Cp.Pc.v940 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v941 : Nat := CFSG.KD.Fi24Cp.KV7 4
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v942 : Nat := CFSG.KD.Fi24Cp.KV7 5
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l941 : List Nat := [CFSG.KD.Fi24Cp.Pc.v939, CFSG.KD.Fi24Cp.Pc.v940]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l943 : List Nat := [CFSG.KD.Fi24Cp.Pc.v939, CFSG.KD.Fi24Cp.Pc.v940, CFSG.KD.Fi24Cp.Pc.v941, CFSG.KD.Fi24Cp.Pc.v942]
theorem CFSG.KD.Fi24Cp.Pc.p941 : Nat.beq (runC AR SD 939 (ckL CFSG.KD.Fi24Cp.Pc.l943) 2 941 CFSG.KD.Fi24Cp.Pc.l941) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v943 : Nat := CFSG.KD.Fi24Cp.KV7 6
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l944 : List Nat := [CFSG.KD.Fi24Cp.Pc.v939, CFSG.KD.Fi24Cp.Pc.v940, CFSG.KD.Fi24Cp.Pc.v941, CFSG.KD.Fi24Cp.Pc.v942, CFSG.KD.Fi24Cp.Pc.v943]
theorem CFSG.KD.Fi24Cp.Pc.p943 : Nat.beq (runC AR SD 939 (ckL CFSG.KD.Fi24Cp.Pc.l944) 1 943 CFSG.KD.Fi24Cp.Pc.l943) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a944_2 : Nat := CFSG.KD.Fi24Cp.KV7 7
theorem CFSG.KD.Fi24Cp.Pc.q944_2 : Nat.beq (powTop AR.mul (getV AR SD 939 CFSG.KD.Fi24Cp.Pc.l944 (SD.na.getD 944 0)) (SD.nk.getD 944 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a944_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v944 : Nat := CFSG.KD.Fi24Cp.KV7 8
theorem CFSG.KD.Fi24Cp.Pc.r944 : Nat.beq (powR AR.mul AR.one (getV AR SD 939 CFSG.KD.Fi24Cp.Pc.l944 (SD.na.getD 944 0)) (SD.nk.getD 944 1) 2 CFSG.KD.Fi24Cp.Pc.a944_2 true) CFSG.KD.Fi24Cp.Pc.v944 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v945 : Nat := CFSG.KD.Fi24Cp.KV7 9
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l945 : List Nat := [CFSG.KD.Fi24Cp.Pc.v939, CFSG.KD.Fi24Cp.Pc.v940, CFSG.KD.Fi24Cp.Pc.v941, CFSG.KD.Fi24Cp.Pc.v942, CFSG.KD.Fi24Cp.Pc.v943, CFSG.KD.Fi24Cp.Pc.v944]
theorem CFSG.KD.Fi24Cp.Pc.f70 : Nat.beq (runC AR SD 939 (finC AR SD (nat_lit 70) 939 946) 1 945 CFSG.KD.Fi24Cp.Pc.l945) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk70 : chk (nat_lit 70) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 70) (lo := 939) (hi := 946) (m := 7) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 7) (m2 := 6) (j2 := 940) CFSG.KD.Fi24Cp.Pc.p939 rfl rfl).trans ((runC_node (m := 6) (m2 := 5) (j2 := 941) (Lr := CFSG.KD.Fi24Cp.Pc.l941) ((nodeV_pow (R := AR) (D := SD) (lo := 939) (L := CFSG.KD.Fi24Cp.Pc.l940) (j := 940) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 939 CFSG.KD.Fi24Cp.Pc.l940 (SD.na.getD 940 0)) (SD.nk.getD 940 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q940_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q940_2 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r940))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 943) CFSG.KD.Fi24Cp.Pc.p941 rfl rfl).trans ((runC_seq (m := 3) (m2 := 2) (j2 := 944) CFSG.KD.Fi24Cp.Pc.p943 rfl rfl).trans (runC_node (m := 2) (m2 := 1) (j2 := 945) (Lr := CFSG.KD.Fi24Cp.Pc.l945) ((nodeV_pow (R := AR) (D := SD) (lo := 939) (L := CFSG.KD.Fi24Cp.Pc.l944) (j := 944) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 939 CFSG.KD.Fi24Cp.Pc.l944 (SD.na.getD 944 0)) (SD.nk.getD 944 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q944_2 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r944)))) (by quickRfl) rfl rfl rfl))))))).trans CFSG.KD.Fi24Cp.Pc.f70

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v946 : Nat := CFSG.KD.Fi24Cp.KV7 10
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l947 : List Nat := [CFSG.KD.Fi24Cp.Pc.v946]
theorem CFSG.KD.Fi24Cp.Pc.p946 : Nat.beq (runC AR SD 946 (ckL CFSG.KD.Fi24Cp.Pc.l947) 1 946 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a947_3 : Nat := CFSG.KD.Fi24Cp.KV7 11
theorem CFSG.KD.Fi24Cp.Pc.q947_3 : Nat.beq (powTop AR.mul (getV AR SD 946 CFSG.KD.Fi24Cp.Pc.l947 (SD.na.getD 947 0)) (SD.nk.getD 947 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a947_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a947_2 : Nat := CFSG.KD.Fi24Cp.KV7 12
theorem CFSG.KD.Fi24Cp.Pc.q947_2 : Nat.beq (powTop AR.mul (getV AR SD 946 CFSG.KD.Fi24Cp.Pc.l947 (SD.na.getD 947 0)) (SD.nk.getD 947 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a947_2) 1 CFSG.KD.Fi24Cp.Pc.a947_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a947_1 : Nat := CFSG.KD.Fi24Cp.KV7 13
theorem CFSG.KD.Fi24Cp.Pc.q947_1 : Nat.beq (powTop AR.mul (getV AR SD 946 CFSG.KD.Fi24Cp.Pc.l947 (SD.na.getD 947 0)) (SD.nk.getD 947 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a947_1) 1 CFSG.KD.Fi24Cp.Pc.a947_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v947 : Nat := CFSG.KD.Fi24Cp.KV7 14
theorem CFSG.KD.Fi24Cp.Pc.r947 : Nat.beq (powR AR.mul AR.one (getV AR SD 946 CFSG.KD.Fi24Cp.Pc.l947 (SD.na.getD 947 0)) (SD.nk.getD 947 1) 1 CFSG.KD.Fi24Cp.Pc.a947_1 true) CFSG.KD.Fi24Cp.Pc.v947 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l948 : List Nat := [CFSG.KD.Fi24Cp.Pc.v946, CFSG.KD.Fi24Cp.Pc.v947]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a948_3 : Nat := CFSG.KD.Fi24Cp.KV7 15
theorem CFSG.KD.Fi24Cp.Pc.q948_3 : Nat.beq (powTop AR.mul (getV AR SD 946 CFSG.KD.Fi24Cp.Pc.l948 (SD.na.getD 948 0)) (SD.nk.getD 948 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a948_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a948_2 : Nat := CFSG.KD.Fi24Cp.KV7 16
theorem CFSG.KD.Fi24Cp.Pc.q948_2 : Nat.beq (powTop AR.mul (getV AR SD 946 CFSG.KD.Fi24Cp.Pc.l948 (SD.na.getD 948 0)) (SD.nk.getD 948 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a948_2) 1 CFSG.KD.Fi24Cp.Pc.a948_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v948 : Nat := CFSG.KD.Fi24Cp.KV7 17
theorem CFSG.KD.Fi24Cp.Pc.r948 : Nat.beq (powR AR.mul AR.one (getV AR SD 946 CFSG.KD.Fi24Cp.Pc.l948 (SD.na.getD 948 0)) (SD.nk.getD 948 1) 2 CFSG.KD.Fi24Cp.Pc.a948_2 true) CFSG.KD.Fi24Cp.Pc.v948 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l949 : List Nat := [CFSG.KD.Fi24Cp.Pc.v946, CFSG.KD.Fi24Cp.Pc.v947, CFSG.KD.Fi24Cp.Pc.v948]
theorem CFSG.KD.Fi24Cp.Pc.f71 : Nat.beq (runC AR SD 946 (finC AR SD (nat_lit 71) 946 949) 0 949 CFSG.KD.Fi24Cp.Pc.l949) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk71 : chk (nat_lit 71) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 71) (lo := 946) (hi := 949) (m := 3) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 3) (m2 := 2) (j2 := 947) CFSG.KD.Fi24Cp.Pc.p946 rfl rfl).trans ((runC_node (m := 2) (m2 := 1) (j2 := 948) (Lr := CFSG.KD.Fi24Cp.Pc.l948) ((nodeV_pow (R := AR) (D := SD) (lo := 946) (L := CFSG.KD.Fi24Cp.Pc.l947) (j := 947) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 946 CFSG.KD.Fi24Cp.Pc.l947 (SD.na.getD 947 0)) (SD.nk.getD 947 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q947_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q947_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q947_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r947)))))) (by quickRfl) rfl rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 949) (Lr := CFSG.KD.Fi24Cp.Pc.l949) ((nodeV_pow (R := AR) (D := SD) (lo := 946) (L := CFSG.KD.Fi24Cp.Pc.l948) (j := 948) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 946 CFSG.KD.Fi24Cp.Pc.l948 (SD.na.getD 948 0)) (SD.nk.getD 948 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q948_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q948_2 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r948))))) (by quickRfl) rfl rfl rfl))))).trans CFSG.KD.Fi24Cp.Pc.f71

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a949_2 : Nat := CFSG.KD.Fi24Cp.KV7 18
theorem CFSG.KD.Fi24Cp.Pc.q949_2 : Nat.beq (powTop AR.mul (getV AR SD 949 [] (SD.na.getD 949 0)) (SD.nk.getD 949 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a949_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v949 : Nat := CFSG.KD.Fi24Cp.KV7 19
theorem CFSG.KD.Fi24Cp.Pc.r949 : Nat.beq (powR AR.mul AR.one (getV AR SD 949 [] (SD.na.getD 949 0)) (SD.nk.getD 949 1) 2 CFSG.KD.Fi24Cp.Pc.a949_2 true) CFSG.KD.Fi24Cp.Pc.v949 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l950 : List Nat := [CFSG.KD.Fi24Cp.Pc.v949]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a950_3 : Nat := CFSG.KD.Fi24Cp.KV7 20
theorem CFSG.KD.Fi24Cp.Pc.q950_3 : Nat.beq (powTop AR.mul (getV AR SD 949 CFSG.KD.Fi24Cp.Pc.l950 (SD.na.getD 950 0)) (SD.nk.getD 950 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a950_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a950_2 : Nat := CFSG.KD.Fi24Cp.KV7 21
theorem CFSG.KD.Fi24Cp.Pc.q950_2 : Nat.beq (powTop AR.mul (getV AR SD 949 CFSG.KD.Fi24Cp.Pc.l950 (SD.na.getD 950 0)) (SD.nk.getD 950 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a950_2) 1 CFSG.KD.Fi24Cp.Pc.a950_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a950_1 : Nat := CFSG.KD.Fi24Cp.KV7 22
theorem CFSG.KD.Fi24Cp.Pc.q950_1 : Nat.beq (powTop AR.mul (getV AR SD 949 CFSG.KD.Fi24Cp.Pc.l950 (SD.na.getD 950 0)) (SD.nk.getD 950 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a950_1) 1 CFSG.KD.Fi24Cp.Pc.a950_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v950 : Nat := CFSG.KD.Fi24Cp.KV7 23
theorem CFSG.KD.Fi24Cp.Pc.r950 : Nat.beq (powR AR.mul AR.one (getV AR SD 949 CFSG.KD.Fi24Cp.Pc.l950 (SD.na.getD 950 0)) (SD.nk.getD 950 1) 1 CFSG.KD.Fi24Cp.Pc.a950_1 true) CFSG.KD.Fi24Cp.Pc.v950 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l951 : List Nat := [CFSG.KD.Fi24Cp.Pc.v949, CFSG.KD.Fi24Cp.Pc.v950]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a951_2 : Nat := CFSG.KD.Fi24Cp.KV7 24
theorem CFSG.KD.Fi24Cp.Pc.q951_2 : Nat.beq (powTop AR.mul (getV AR SD 949 CFSG.KD.Fi24Cp.Pc.l951 (SD.na.getD 951 0)) (SD.nk.getD 951 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a951_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a951_1 : Nat := CFSG.KD.Fi24Cp.KV7 25
theorem CFSG.KD.Fi24Cp.Pc.q951_1 : Nat.beq (powTop AR.mul (getV AR SD 949 CFSG.KD.Fi24Cp.Pc.l951 (SD.na.getD 951 0)) (SD.nk.getD 951 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a951_1) 1 CFSG.KD.Fi24Cp.Pc.a951_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v951 : Nat := CFSG.KD.Fi24Cp.KV7 26
theorem CFSG.KD.Fi24Cp.Pc.r951 : Nat.beq (powR AR.mul AR.one (getV AR SD 949 CFSG.KD.Fi24Cp.Pc.l951 (SD.na.getD 951 0)) (SD.nk.getD 951 1) 1 CFSG.KD.Fi24Cp.Pc.a951_1 true) CFSG.KD.Fi24Cp.Pc.v951 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l952 : List Nat := [CFSG.KD.Fi24Cp.Pc.v949, CFSG.KD.Fi24Cp.Pc.v950, CFSG.KD.Fi24Cp.Pc.v951]
theorem CFSG.KD.Fi24Cp.Pc.f72 : Nat.beq (runC AR SD 949 (finC AR SD (nat_lit 72) 949 952) 0 952 CFSG.KD.Fi24Cp.Pc.l952) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk72 : chk (nat_lit 72) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 72) (lo := 949) (hi := 952) (m := 3) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 3) (m2 := 2) (j2 := 950) (Lr := CFSG.KD.Fi24Cp.Pc.l950) ((nodeV_pow (R := AR) (D := SD) (lo := 949) (L := []) (j := 949) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 949 [] (SD.na.getD 949 0)) (SD.nk.getD 949 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q949_2 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r949)))) (by quickRfl) rfl rfl rfl).trans ((runC_node (m := 2) (m2 := 1) (j2 := 951) (Lr := CFSG.KD.Fi24Cp.Pc.l951) ((nodeV_pow (R := AR) (D := SD) (lo := 949) (L := CFSG.KD.Fi24Cp.Pc.l950) (j := 950) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 949 CFSG.KD.Fi24Cp.Pc.l950 (SD.na.getD 950 0)) (SD.nk.getD 950 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q950_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q950_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q950_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r950)))))) (by quickRfl) rfl rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 952) (Lr := CFSG.KD.Fi24Cp.Pc.l952) ((nodeV_pow (R := AR) (D := SD) (lo := 949) (L := CFSG.KD.Fi24Cp.Pc.l951) (j := 951) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 949 CFSG.KD.Fi24Cp.Pc.l951 (SD.na.getD 951 0)) (SD.nk.getD 951 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q951_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q951_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r951))))) (by quickRfl) rfl rfl rfl))))).trans CFSG.KD.Fi24Cp.Pc.f72

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a952_2 : Nat := CFSG.KD.Fi24Cp.KV7 27
theorem CFSG.KD.Fi24Cp.Pc.q952_2 : Nat.beq (powTop AR.mul (getV AR SD 952 [] (SD.na.getD 952 0)) (SD.nk.getD 952 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a952_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a952_1 : Nat := CFSG.KD.Fi24Cp.KV7 28
theorem CFSG.KD.Fi24Cp.Pc.q952_1 : Nat.beq (powTop AR.mul (getV AR SD 952 [] (SD.na.getD 952 0)) (SD.nk.getD 952 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a952_1) 1 CFSG.KD.Fi24Cp.Pc.a952_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v952 : Nat := CFSG.KD.Fi24Cp.KV7 29
theorem CFSG.KD.Fi24Cp.Pc.r952 : Nat.beq (powR AR.mul AR.one (getV AR SD 952 [] (SD.na.getD 952 0)) (SD.nk.getD 952 1) 1 CFSG.KD.Fi24Cp.Pc.a952_1 true) CFSG.KD.Fi24Cp.Pc.v952 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l953 : List Nat := [CFSG.KD.Fi24Cp.Pc.v952]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a953_3 : Nat := CFSG.KD.Fi24Cp.KV7 30
theorem CFSG.KD.Fi24Cp.Pc.q953_3 : Nat.beq (powTop AR.mul (getV AR SD 952 CFSG.KD.Fi24Cp.Pc.l953 (SD.na.getD 953 0)) (SD.nk.getD 953 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a953_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a953_2 : Nat := CFSG.KD.Fi24Cp.KV7 31
theorem CFSG.KD.Fi24Cp.Pc.q953_2 : Nat.beq (powTop AR.mul (getV AR SD 952 CFSG.KD.Fi24Cp.Pc.l953 (SD.na.getD 953 0)) (SD.nk.getD 953 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a953_2) 1 CFSG.KD.Fi24Cp.Pc.a953_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a953_1 : Nat := CFSG.KD.Fi24Cp.KV7 32
theorem CFSG.KD.Fi24Cp.Pc.q953_1 : Nat.beq (powTop AR.mul (getV AR SD 952 CFSG.KD.Fi24Cp.Pc.l953 (SD.na.getD 953 0)) (SD.nk.getD 953 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a953_1) 1 CFSG.KD.Fi24Cp.Pc.a953_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v953 : Nat := CFSG.KD.Fi24Cp.KV7 33
theorem CFSG.KD.Fi24Cp.Pc.r953 : Nat.beq (powR AR.mul AR.one (getV AR SD 952 CFSG.KD.Fi24Cp.Pc.l953 (SD.na.getD 953 0)) (SD.nk.getD 953 1) 1 CFSG.KD.Fi24Cp.Pc.a953_1 true) CFSG.KD.Fi24Cp.Pc.v953 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l954 : List Nat := [CFSG.KD.Fi24Cp.Pc.v952, CFSG.KD.Fi24Cp.Pc.v953]
theorem CFSG.KD.Fi24Cp.Pc.f73 : Nat.beq (runC AR SD 952 (finC AR SD (nat_lit 73) 952 954) 0 954 CFSG.KD.Fi24Cp.Pc.l954) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk73 : chk (nat_lit 73) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 73) (lo := 952) (hi := 954) (m := 2) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 2) (m2 := 1) (j2 := 953) (Lr := CFSG.KD.Fi24Cp.Pc.l953) ((nodeV_pow (R := AR) (D := SD) (lo := 952) (L := []) (j := 952) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 952 [] (SD.na.getD 952 0)) (SD.nk.getD 952 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q952_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q952_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r952))))) (by quickRfl) rfl rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 954) (Lr := CFSG.KD.Fi24Cp.Pc.l954) ((nodeV_pow (R := AR) (D := SD) (lo := 952) (L := CFSG.KD.Fi24Cp.Pc.l953) (j := 953) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 952 CFSG.KD.Fi24Cp.Pc.l953 (SD.na.getD 953 0)) (SD.nk.getD 953 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q953_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q953_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q953_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r953)))))) (by quickRfl) rfl rfl rfl)))).trans CFSG.KD.Fi24Cp.Pc.f73

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a954_3 : Nat := CFSG.KD.Fi24Cp.KV7 34
theorem CFSG.KD.Fi24Cp.Pc.q954_3 : Nat.beq (powTop AR.mul (getV AR SD 954 [] (SD.na.getD 954 0)) (SD.nk.getD 954 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a954_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a954_2 : Nat := CFSG.KD.Fi24Cp.KV7 35
theorem CFSG.KD.Fi24Cp.Pc.q954_2 : Nat.beq (powTop AR.mul (getV AR SD 954 [] (SD.na.getD 954 0)) (SD.nk.getD 954 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a954_2) 1 CFSG.KD.Fi24Cp.Pc.a954_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a954_1 : Nat := CFSG.KD.Fi24Cp.KV7 36
theorem CFSG.KD.Fi24Cp.Pc.q954_1 : Nat.beq (powTop AR.mul (getV AR SD 954 [] (SD.na.getD 954 0)) (SD.nk.getD 954 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a954_1) 1 CFSG.KD.Fi24Cp.Pc.a954_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v954 : Nat := CFSG.KD.Fi24Cp.KV7 37
theorem CFSG.KD.Fi24Cp.Pc.r954 : Nat.beq (powR AR.mul AR.one (getV AR SD 954 [] (SD.na.getD 954 0)) (SD.nk.getD 954 1) 1 CFSG.KD.Fi24Cp.Pc.a954_1 true) CFSG.KD.Fi24Cp.Pc.v954 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l955 : List Nat := [CFSG.KD.Fi24Cp.Pc.v954]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a955_3 : Nat := CFSG.KD.Fi24Cp.KV7 38
theorem CFSG.KD.Fi24Cp.Pc.q955_3 : Nat.beq (powTop AR.mul (getV AR SD 954 CFSG.KD.Fi24Cp.Pc.l955 (SD.na.getD 955 0)) (SD.nk.getD 955 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a955_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a955_2 : Nat := CFSG.KD.Fi24Cp.KV7 39
theorem CFSG.KD.Fi24Cp.Pc.q955_2 : Nat.beq (powTop AR.mul (getV AR SD 954 CFSG.KD.Fi24Cp.Pc.l955 (SD.na.getD 955 0)) (SD.nk.getD 955 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a955_2) 1 CFSG.KD.Fi24Cp.Pc.a955_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a955_1 : Nat := CFSG.KD.Fi24Cp.KV7 40
theorem CFSG.KD.Fi24Cp.Pc.q955_1 : Nat.beq (powTop AR.mul (getV AR SD 954 CFSG.KD.Fi24Cp.Pc.l955 (SD.na.getD 955 0)) (SD.nk.getD 955 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a955_1) 1 CFSG.KD.Fi24Cp.Pc.a955_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v955 : Nat := CFSG.KD.Fi24Cp.KV7 41
theorem CFSG.KD.Fi24Cp.Pc.r955 : Nat.beq (powR AR.mul AR.one (getV AR SD 954 CFSG.KD.Fi24Cp.Pc.l955 (SD.na.getD 955 0)) (SD.nk.getD 955 1) 1 CFSG.KD.Fi24Cp.Pc.a955_1 true) CFSG.KD.Fi24Cp.Pc.v955 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l956 : List Nat := [CFSG.KD.Fi24Cp.Pc.v954, CFSG.KD.Fi24Cp.Pc.v955]
theorem CFSG.KD.Fi24Cp.Pc.f74 : Nat.beq (runC AR SD 954 (finC AR SD (nat_lit 74) 954 956) 0 956 CFSG.KD.Fi24Cp.Pc.l956) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk74 : chk (nat_lit 74) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 74) (lo := 954) (hi := 956) (m := 2) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 2) (m2 := 1) (j2 := 955) (Lr := CFSG.KD.Fi24Cp.Pc.l955) ((nodeV_pow (R := AR) (D := SD) (lo := 954) (L := []) (j := 954) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 954 [] (SD.na.getD 954 0)) (SD.nk.getD 954 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q954_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q954_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q954_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r954)))))) (by quickRfl) rfl rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 956) (Lr := CFSG.KD.Fi24Cp.Pc.l956) ((nodeV_pow (R := AR) (D := SD) (lo := 954) (L := CFSG.KD.Fi24Cp.Pc.l955) (j := 955) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 954 CFSG.KD.Fi24Cp.Pc.l955 (SD.na.getD 955 0)) (SD.nk.getD 955 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q955_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q955_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q955_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r955)))))) (by quickRfl) rfl rfl rfl)))).trans CFSG.KD.Fi24Cp.Pc.f74

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a956_3 : Nat := CFSG.KD.Fi24Cp.KV7 42
theorem CFSG.KD.Fi24Cp.Pc.q956_3 : Nat.beq (powTop AR.mul (getV AR SD 956 [] (SD.na.getD 956 0)) (SD.nk.getD 956 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a956_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a956_2 : Nat := CFSG.KD.Fi24Cp.KV7 43
theorem CFSG.KD.Fi24Cp.Pc.q956_2 : Nat.beq (powTop AR.mul (getV AR SD 956 [] (SD.na.getD 956 0)) (SD.nk.getD 956 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a956_2) 1 CFSG.KD.Fi24Cp.Pc.a956_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a956_1 : Nat := CFSG.KD.Fi24Cp.KV7 44
theorem CFSG.KD.Fi24Cp.Pc.q956_1 : Nat.beq (powTop AR.mul (getV AR SD 956 [] (SD.na.getD 956 0)) (SD.nk.getD 956 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a956_1) 1 CFSG.KD.Fi24Cp.Pc.a956_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v956 : Nat := CFSG.KD.Fi24Cp.KV7 45
theorem CFSG.KD.Fi24Cp.Pc.r956 : Nat.beq (powR AR.mul AR.one (getV AR SD 956 [] (SD.na.getD 956 0)) (SD.nk.getD 956 1) 1 CFSG.KD.Fi24Cp.Pc.a956_1 true) CFSG.KD.Fi24Cp.Pc.v956 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l957 : List Nat := [CFSG.KD.Fi24Cp.Pc.v956]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a957_3 : Nat := CFSG.KD.Fi24Cp.KV7 46
theorem CFSG.KD.Fi24Cp.Pc.q957_3 : Nat.beq (powTop AR.mul (getV AR SD 956 CFSG.KD.Fi24Cp.Pc.l957 (SD.na.getD 957 0)) (SD.nk.getD 957 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a957_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a957_2 : Nat := CFSG.KD.Fi24Cp.KV7 47
theorem CFSG.KD.Fi24Cp.Pc.q957_2 : Nat.beq (powTop AR.mul (getV AR SD 956 CFSG.KD.Fi24Cp.Pc.l957 (SD.na.getD 957 0)) (SD.nk.getD 957 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a957_2) 1 CFSG.KD.Fi24Cp.Pc.a957_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a957_1 : Nat := CFSG.KD.Fi24Cp.KV7 48
theorem CFSG.KD.Fi24Cp.Pc.q957_1 : Nat.beq (powTop AR.mul (getV AR SD 956 CFSG.KD.Fi24Cp.Pc.l957 (SD.na.getD 957 0)) (SD.nk.getD 957 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a957_1) 1 CFSG.KD.Fi24Cp.Pc.a957_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v957 : Nat := CFSG.KD.Fi24Cp.KV7 49
theorem CFSG.KD.Fi24Cp.Pc.r957 : Nat.beq (powR AR.mul AR.one (getV AR SD 956 CFSG.KD.Fi24Cp.Pc.l957 (SD.na.getD 957 0)) (SD.nk.getD 957 1) 1 CFSG.KD.Fi24Cp.Pc.a957_1 true) CFSG.KD.Fi24Cp.Pc.v957 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l958 : List Nat := [CFSG.KD.Fi24Cp.Pc.v956, CFSG.KD.Fi24Cp.Pc.v957]
theorem CFSG.KD.Fi24Cp.Pc.f75 : Nat.beq (runC AR SD 956 (finC AR SD (nat_lit 75) 956 958) 0 958 CFSG.KD.Fi24Cp.Pc.l958) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk75 : chk (nat_lit 75) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 75) (lo := 956) (hi := 958) (m := 2) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 2) (m2 := 1) (j2 := 957) (Lr := CFSG.KD.Fi24Cp.Pc.l957) ((nodeV_pow (R := AR) (D := SD) (lo := 956) (L := []) (j := 956) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 956 [] (SD.na.getD 956 0)) (SD.nk.getD 956 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q956_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q956_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q956_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r956)))))) (by quickRfl) rfl rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 958) (Lr := CFSG.KD.Fi24Cp.Pc.l958) ((nodeV_pow (R := AR) (D := SD) (lo := 956) (L := CFSG.KD.Fi24Cp.Pc.l957) (j := 957) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 956 CFSG.KD.Fi24Cp.Pc.l957 (SD.na.getD 957 0)) (SD.nk.getD 957 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q957_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q957_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q957_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r957)))))) (by quickRfl) rfl rfl rfl)))).trans CFSG.KD.Fi24Cp.Pc.f75

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a958_3 : Nat := CFSG.KD.Fi24Cp.KV7 50
theorem CFSG.KD.Fi24Cp.Pc.q958_3 : Nat.beq (powTop AR.mul (getV AR SD 958 [] (SD.na.getD 958 0)) (SD.nk.getD 958 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a958_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a958_2 : Nat := CFSG.KD.Fi24Cp.KV7 51
theorem CFSG.KD.Fi24Cp.Pc.q958_2 : Nat.beq (powTop AR.mul (getV AR SD 958 [] (SD.na.getD 958 0)) (SD.nk.getD 958 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a958_2) 1 CFSG.KD.Fi24Cp.Pc.a958_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a958_1 : Nat := CFSG.KD.Fi24Cp.KV7 52
theorem CFSG.KD.Fi24Cp.Pc.q958_1 : Nat.beq (powTop AR.mul (getV AR SD 958 [] (SD.na.getD 958 0)) (SD.nk.getD 958 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a958_1) 1 CFSG.KD.Fi24Cp.Pc.a958_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v958 : Nat := CFSG.KD.Fi24Cp.KV7 53
theorem CFSG.KD.Fi24Cp.Pc.r958 : Nat.beq (powR AR.mul AR.one (getV AR SD 958 [] (SD.na.getD 958 0)) (SD.nk.getD 958 1) 1 CFSG.KD.Fi24Cp.Pc.a958_1 true) CFSG.KD.Fi24Cp.Pc.v958 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l959 : List Nat := [CFSG.KD.Fi24Cp.Pc.v958]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a959_1 : Nat := CFSG.KD.Fi24Cp.KV7 54
theorem CFSG.KD.Fi24Cp.Pc.q959_1 : Nat.beq (powTop AR.mul (getV AR SD 958 CFSG.KD.Fi24Cp.Pc.l959 (SD.na.getD 959 0)) (SD.nk.getD 959 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a959_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v959 : Nat := CFSG.KD.Fi24Cp.KV7 55
theorem CFSG.KD.Fi24Cp.Pc.r959 : Nat.beq (powR AR.mul AR.one (getV AR SD 958 CFSG.KD.Fi24Cp.Pc.l959 (SD.na.getD 959 0)) (SD.nk.getD 959 1) 1 CFSG.KD.Fi24Cp.Pc.a959_1 true) CFSG.KD.Fi24Cp.Pc.v959 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l960 : List Nat := [CFSG.KD.Fi24Cp.Pc.v958, CFSG.KD.Fi24Cp.Pc.v959]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a960_1 : Nat := CFSG.KD.Fi24Cp.KV7 56
theorem CFSG.KD.Fi24Cp.Pc.q960_1 : Nat.beq (powTop AR.mul (getV AR SD 958 CFSG.KD.Fi24Cp.Pc.l960 (SD.na.getD 960 0)) (SD.nk.getD 960 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a960_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v960 : Nat := CFSG.KD.Fi24Cp.KV7 57
theorem CFSG.KD.Fi24Cp.Pc.r960 : Nat.beq (powR AR.mul AR.one (getV AR SD 958 CFSG.KD.Fi24Cp.Pc.l960 (SD.na.getD 960 0)) (SD.nk.getD 960 1) 1 CFSG.KD.Fi24Cp.Pc.a960_1 true) CFSG.KD.Fi24Cp.Pc.v960 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l961 : List Nat := [CFSG.KD.Fi24Cp.Pc.v958, CFSG.KD.Fi24Cp.Pc.v959, CFSG.KD.Fi24Cp.Pc.v960]
theorem CFSG.KD.Fi24Cp.Pc.f76 : Nat.beq (runC AR SD 958 (finC AR SD (nat_lit 76) 958 961) 0 961 CFSG.KD.Fi24Cp.Pc.l961) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk76 : chk (nat_lit 76) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 76) (lo := 958) (hi := 961) (m := 3) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 3) (m2 := 2) (j2 := 959) (Lr := CFSG.KD.Fi24Cp.Pc.l959) ((nodeV_pow (R := AR) (D := SD) (lo := 958) (L := []) (j := 958) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 958 [] (SD.na.getD 958 0)) (SD.nk.getD 958 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q958_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q958_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q958_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r958)))))) (by quickRfl) rfl rfl rfl).trans ((runC_node (m := 2) (m2 := 1) (j2 := 960) (Lr := CFSG.KD.Fi24Cp.Pc.l960) ((nodeV_pow (R := AR) (D := SD) (lo := 958) (L := CFSG.KD.Fi24Cp.Pc.l959) (j := 959) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 958 CFSG.KD.Fi24Cp.Pc.l959 (SD.na.getD 959 0)) (SD.nk.getD 959 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q959_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r959)))) (by quickRfl) rfl rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 961) (Lr := CFSG.KD.Fi24Cp.Pc.l961) ((nodeV_pow (R := AR) (D := SD) (lo := 958) (L := CFSG.KD.Fi24Cp.Pc.l960) (j := 960) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 958 CFSG.KD.Fi24Cp.Pc.l960 (SD.na.getD 960 0)) (SD.nk.getD 960 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q960_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r960)))) (by quickRfl) rfl rfl rfl))))).trans CFSG.KD.Fi24Cp.Pc.f76

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a961_2 : Nat := CFSG.KD.Fi24Cp.KV7 58
theorem CFSG.KD.Fi24Cp.Pc.q961_2 : Nat.beq (powTop AR.mul (getV AR SD 961 [] (SD.na.getD 961 0)) (SD.nk.getD 961 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a961_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a961_1 : Nat := CFSG.KD.Fi24Cp.KV7 59
theorem CFSG.KD.Fi24Cp.Pc.q961_1 : Nat.beq (powTop AR.mul (getV AR SD 961 [] (SD.na.getD 961 0)) (SD.nk.getD 961 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a961_1) 1 CFSG.KD.Fi24Cp.Pc.a961_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v961 : Nat := CFSG.KD.Fi24Cp.KV7 60
theorem CFSG.KD.Fi24Cp.Pc.r961 : Nat.beq (powR AR.mul AR.one (getV AR SD 961 [] (SD.na.getD 961 0)) (SD.nk.getD 961 1) 1 CFSG.KD.Fi24Cp.Pc.a961_1 true) CFSG.KD.Fi24Cp.Pc.v961 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l962 : List Nat := [CFSG.KD.Fi24Cp.Pc.v961]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a962_2 : Nat := CFSG.KD.Fi24Cp.KV7 61
theorem CFSG.KD.Fi24Cp.Pc.q962_2 : Nat.beq (powTop AR.mul (getV AR SD 961 CFSG.KD.Fi24Cp.Pc.l962 (SD.na.getD 962 0)) (SD.nk.getD 962 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a962_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a962_1 : Nat := CFSG.KD.Fi24Cp.KV7 62
theorem CFSG.KD.Fi24Cp.Pc.q962_1 : Nat.beq (powTop AR.mul (getV AR SD 961 CFSG.KD.Fi24Cp.Pc.l962 (SD.na.getD 962 0)) (SD.nk.getD 962 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a962_1) 1 CFSG.KD.Fi24Cp.Pc.a962_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v962 : Nat := CFSG.KD.Fi24Cp.KV7 63
theorem CFSG.KD.Fi24Cp.Pc.r962 : Nat.beq (powR AR.mul AR.one (getV AR SD 961 CFSG.KD.Fi24Cp.Pc.l962 (SD.na.getD 962 0)) (SD.nk.getD 962 1) 1 CFSG.KD.Fi24Cp.Pc.a962_1 true) CFSG.KD.Fi24Cp.Pc.v962 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l963 : List Nat := [CFSG.KD.Fi24Cp.Pc.v961, CFSG.KD.Fi24Cp.Pc.v962]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a963_2 : Nat := CFSG.KD.Fi24Cp.KV7 64
theorem CFSG.KD.Fi24Cp.Pc.q963_2 : Nat.beq (powTop AR.mul (getV AR SD 961 CFSG.KD.Fi24Cp.Pc.l963 (SD.na.getD 963 0)) (SD.nk.getD 963 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a963_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v963 : Nat := CFSG.KD.Fi24Cp.KV7 65
theorem CFSG.KD.Fi24Cp.Pc.r963 : Nat.beq (powR AR.mul AR.one (getV AR SD 961 CFSG.KD.Fi24Cp.Pc.l963 (SD.na.getD 963 0)) (SD.nk.getD 963 1) 2 CFSG.KD.Fi24Cp.Pc.a963_2 true) CFSG.KD.Fi24Cp.Pc.v963 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l964 : List Nat := [CFSG.KD.Fi24Cp.Pc.v961, CFSG.KD.Fi24Cp.Pc.v962, CFSG.KD.Fi24Cp.Pc.v963]
theorem CFSG.KD.Fi24Cp.Pc.f77 : Nat.beq (runC AR SD 961 (finC AR SD (nat_lit 77) 961 964) 0 964 CFSG.KD.Fi24Cp.Pc.l964) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk77 : chk (nat_lit 77) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 77) (lo := 961) (hi := 964) (m := 3) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 3) (m2 := 2) (j2 := 962) (Lr := CFSG.KD.Fi24Cp.Pc.l962) ((nodeV_pow (R := AR) (D := SD) (lo := 961) (L := []) (j := 961) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 961 [] (SD.na.getD 961 0)) (SD.nk.getD 961 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q961_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q961_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r961))))) (by quickRfl) rfl rfl rfl).trans ((runC_node (m := 2) (m2 := 1) (j2 := 963) (Lr := CFSG.KD.Fi24Cp.Pc.l963) ((nodeV_pow (R := AR) (D := SD) (lo := 961) (L := CFSG.KD.Fi24Cp.Pc.l962) (j := 962) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 961 CFSG.KD.Fi24Cp.Pc.l962 (SD.na.getD 962 0)) (SD.nk.getD 962 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q962_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q962_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r962))))) (by quickRfl) rfl rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 964) (Lr := CFSG.KD.Fi24Cp.Pc.l964) ((nodeV_pow (R := AR) (D := SD) (lo := 961) (L := CFSG.KD.Fi24Cp.Pc.l963) (j := 963) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 961 CFSG.KD.Fi24Cp.Pc.l963 (SD.na.getD 963 0)) (SD.nk.getD 963 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q963_2 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r963)))) (by quickRfl) rfl rfl rfl))))).trans CFSG.KD.Fi24Cp.Pc.f77

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a964_2 : Nat := CFSG.KD.Fi24Cp.KV7 66
theorem CFSG.KD.Fi24Cp.Pc.q964_2 : Nat.beq (powTop AR.mul (getV AR SD 964 [] (SD.na.getD 964 0)) (SD.nk.getD 964 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a964_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v964 : Nat := CFSG.KD.Fi24Cp.KV7 67
theorem CFSG.KD.Fi24Cp.Pc.r964 : Nat.beq (powR AR.mul AR.one (getV AR SD 964 [] (SD.na.getD 964 0)) (SD.nk.getD 964 1) 2 CFSG.KD.Fi24Cp.Pc.a964_2 true) CFSG.KD.Fi24Cp.Pc.v964 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l965 : List Nat := [CFSG.KD.Fi24Cp.Pc.v964]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a965_1 : Nat := CFSG.KD.Fi24Cp.KV7 68
theorem CFSG.KD.Fi24Cp.Pc.q965_1 : Nat.beq (powTop AR.mul (getV AR SD 964 CFSG.KD.Fi24Cp.Pc.l965 (SD.na.getD 965 0)) (SD.nk.getD 965 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a965_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v965 : Nat := CFSG.KD.Fi24Cp.KV7 69
theorem CFSG.KD.Fi24Cp.Pc.r965 : Nat.beq (powR AR.mul AR.one (getV AR SD 964 CFSG.KD.Fi24Cp.Pc.l965 (SD.na.getD 965 0)) (SD.nk.getD 965 1) 1 CFSG.KD.Fi24Cp.Pc.a965_1 true) CFSG.KD.Fi24Cp.Pc.v965 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l966 : List Nat := [CFSG.KD.Fi24Cp.Pc.v964, CFSG.KD.Fi24Cp.Pc.v965]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a966_1 : Nat := CFSG.KD.Fi24Cp.KV7 70
theorem CFSG.KD.Fi24Cp.Pc.q966_1 : Nat.beq (powTop AR.mul (getV AR SD 964 CFSG.KD.Fi24Cp.Pc.l966 (SD.na.getD 966 0)) (SD.nk.getD 966 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a966_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v966 : Nat := CFSG.KD.Fi24Cp.KV7 71
theorem CFSG.KD.Fi24Cp.Pc.r966 : Nat.beq (powR AR.mul AR.one (getV AR SD 964 CFSG.KD.Fi24Cp.Pc.l966 (SD.na.getD 966 0)) (SD.nk.getD 966 1) 1 CFSG.KD.Fi24Cp.Pc.a966_1 true) CFSG.KD.Fi24Cp.Pc.v966 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v967 : Nat := CFSG.KD.Fi24Cp.KV7 72
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l967 : List Nat := [CFSG.KD.Fi24Cp.Pc.v964, CFSG.KD.Fi24Cp.Pc.v965, CFSG.KD.Fi24Cp.Pc.v966]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l968 : List Nat := [CFSG.KD.Fi24Cp.Pc.v964, CFSG.KD.Fi24Cp.Pc.v965, CFSG.KD.Fi24Cp.Pc.v966, CFSG.KD.Fi24Cp.Pc.v967]
theorem CFSG.KD.Fi24Cp.Pc.p967 : Nat.beq (runC AR SD 964 (ckL CFSG.KD.Fi24Cp.Pc.l968) 1 967 CFSG.KD.Fi24Cp.Pc.l967) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v968 : Nat := CFSG.KD.Fi24Cp.KV7 73
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l969 : List Nat := [CFSG.KD.Fi24Cp.Pc.v964, CFSG.KD.Fi24Cp.Pc.v965, CFSG.KD.Fi24Cp.Pc.v966, CFSG.KD.Fi24Cp.Pc.v967, CFSG.KD.Fi24Cp.Pc.v968]
theorem CFSG.KD.Fi24Cp.Pc.p968 : Nat.beq (runC AR SD 964 (ckL CFSG.KD.Fi24Cp.Pc.l969) 1 968 CFSG.KD.Fi24Cp.Pc.l968) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v969 : Nat := CFSG.KD.Fi24Cp.KV7 74
theorem CFSG.KD.Fi24Cp.Pc.f78 : Nat.beq (runC AR SD 964 (finC AR SD (nat_lit 78) 964 970) 1 969 CFSG.KD.Fi24Cp.Pc.l969) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk78 : chk (nat_lit 78) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 78) (lo := 964) (hi := 970) (m := 6) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 6) (m2 := 5) (j2 := 965) (Lr := CFSG.KD.Fi24Cp.Pc.l965) ((nodeV_pow (R := AR) (D := SD) (lo := 964) (L := []) (j := 964) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 964 [] (SD.na.getD 964 0)) (SD.nk.getD 964 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q964_2 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r964)))) (by quickRfl) rfl rfl rfl).trans ((runC_node (m := 5) (m2 := 4) (j2 := 966) (Lr := CFSG.KD.Fi24Cp.Pc.l966) ((nodeV_pow (R := AR) (D := SD) (lo := 964) (L := CFSG.KD.Fi24Cp.Pc.l965) (j := 965) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 964 CFSG.KD.Fi24Cp.Pc.l965 (SD.na.getD 965 0)) (SD.nk.getD 965 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q965_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r965)))) (by quickRfl) rfl rfl rfl).trans ((runC_node (m := 4) (m2 := 3) (j2 := 967) (Lr := CFSG.KD.Fi24Cp.Pc.l967) ((nodeV_pow (R := AR) (D := SD) (lo := 964) (L := CFSG.KD.Fi24Cp.Pc.l966) (j := 966) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 964 CFSG.KD.Fi24Cp.Pc.l966 (SD.na.getD 966 0)) (SD.nk.getD 966 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q966_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r966)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 3) (m2 := 2) (j2 := 968) CFSG.KD.Fi24Cp.Pc.p967 rfl rfl).trans (runC_seq (m := 2) (m2 := 1) (j2 := 969) CFSG.KD.Fi24Cp.Pc.p968 rfl rfl))))))).trans CFSG.KD.Fi24Cp.Pc.f78

end
