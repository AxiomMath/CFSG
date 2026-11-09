module

public import Certificates.Kernel.Sporadic.Fi24Alpha.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Alpha KV8 "Certificates/Kernel/Sporadic/Fi24Alpha/data/v8.bin" 152491 4 23331123 1349001883134379827

public section

open CFSG.KD.Fi24Alpha CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1146 : Nat := CFSG.KD.Fi24Alpha.KV8 0
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1147 : Nat := CFSG.KD.Fi24Alpha.KV8 1
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1148 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1146, CFSG.KD.Fi24Alpha.Pc.v1147]
theorem CFSG.KD.Fi24Alpha.Pc.p1146 : Nat.beq (runC AR SD 1146 (ckL CFSG.KD.Fi24Alpha.Pc.l1148) 2 1146 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1148 : Nat := CFSG.KD.Fi24Alpha.KV8 2
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1149 : Nat := CFSG.KD.Fi24Alpha.KV8 3
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1150 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1146, CFSG.KD.Fi24Alpha.Pc.v1147, CFSG.KD.Fi24Alpha.Pc.v1148, CFSG.KD.Fi24Alpha.Pc.v1149]
theorem CFSG.KD.Fi24Alpha.Pc.p1148 : Nat.beq (runC AR SD 1146 (ckL CFSG.KD.Fi24Alpha.Pc.l1150) 2 1148 CFSG.KD.Fi24Alpha.Pc.l1148) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1150 : Nat := CFSG.KD.Fi24Alpha.KV8 4
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1151 : Nat := CFSG.KD.Fi24Alpha.KV8 5
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1152 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1146, CFSG.KD.Fi24Alpha.Pc.v1147, CFSG.KD.Fi24Alpha.Pc.v1148, CFSG.KD.Fi24Alpha.Pc.v1149, CFSG.KD.Fi24Alpha.Pc.v1150, CFSG.KD.Fi24Alpha.Pc.v1151]
theorem CFSG.KD.Fi24Alpha.Pc.p1150 : Nat.beq (runC AR SD 1146 (ckL CFSG.KD.Fi24Alpha.Pc.l1152) 2 1150 CFSG.KD.Fi24Alpha.Pc.l1150) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1152 : Nat := CFSG.KD.Fi24Alpha.KV8 6
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1153 : Nat := CFSG.KD.Fi24Alpha.KV8 7
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1154 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1146, CFSG.KD.Fi24Alpha.Pc.v1147, CFSG.KD.Fi24Alpha.Pc.v1148, CFSG.KD.Fi24Alpha.Pc.v1149, CFSG.KD.Fi24Alpha.Pc.v1150, CFSG.KD.Fi24Alpha.Pc.v1151, CFSG.KD.Fi24Alpha.Pc.v1152, CFSG.KD.Fi24Alpha.Pc.v1153]
theorem CFSG.KD.Fi24Alpha.Pc.p1152 : Nat.beq (runC AR SD 1146 (ckL CFSG.KD.Fi24Alpha.Pc.l1154) 2 1152 CFSG.KD.Fi24Alpha.Pc.l1152) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1154 : Nat := CFSG.KD.Fi24Alpha.KV8 8
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1155 : Nat := CFSG.KD.Fi24Alpha.KV8 9
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1156 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1146, CFSG.KD.Fi24Alpha.Pc.v1147, CFSG.KD.Fi24Alpha.Pc.v1148, CFSG.KD.Fi24Alpha.Pc.v1149, CFSG.KD.Fi24Alpha.Pc.v1150, CFSG.KD.Fi24Alpha.Pc.v1151, CFSG.KD.Fi24Alpha.Pc.v1152, CFSG.KD.Fi24Alpha.Pc.v1153, CFSG.KD.Fi24Alpha.Pc.v1154, CFSG.KD.Fi24Alpha.Pc.v1155]
theorem CFSG.KD.Fi24Alpha.Pc.p1154 : Nat.beq (runC AR SD 1146 (ckL CFSG.KD.Fi24Alpha.Pc.l1156) 2 1154 CFSG.KD.Fi24Alpha.Pc.l1154) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1156 : Nat := CFSG.KD.Fi24Alpha.KV8 10
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1157 : Nat := CFSG.KD.Fi24Alpha.KV8 11
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1158 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1146, CFSG.KD.Fi24Alpha.Pc.v1147, CFSG.KD.Fi24Alpha.Pc.v1148, CFSG.KD.Fi24Alpha.Pc.v1149, CFSG.KD.Fi24Alpha.Pc.v1150, CFSG.KD.Fi24Alpha.Pc.v1151, CFSG.KD.Fi24Alpha.Pc.v1152, CFSG.KD.Fi24Alpha.Pc.v1153, CFSG.KD.Fi24Alpha.Pc.v1154, CFSG.KD.Fi24Alpha.Pc.v1155, CFSG.KD.Fi24Alpha.Pc.v1156, CFSG.KD.Fi24Alpha.Pc.v1157]
theorem CFSG.KD.Fi24Alpha.Pc.p1156 : Nat.beq (runC AR SD 1146 (ckL CFSG.KD.Fi24Alpha.Pc.l1158) 2 1156 CFSG.KD.Fi24Alpha.Pc.l1156) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1158 : Nat := CFSG.KD.Fi24Alpha.KV8 12
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1159 : Nat := CFSG.KD.Fi24Alpha.KV8 13
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1160 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1146, CFSG.KD.Fi24Alpha.Pc.v1147, CFSG.KD.Fi24Alpha.Pc.v1148, CFSG.KD.Fi24Alpha.Pc.v1149, CFSG.KD.Fi24Alpha.Pc.v1150, CFSG.KD.Fi24Alpha.Pc.v1151, CFSG.KD.Fi24Alpha.Pc.v1152, CFSG.KD.Fi24Alpha.Pc.v1153, CFSG.KD.Fi24Alpha.Pc.v1154, CFSG.KD.Fi24Alpha.Pc.v1155, CFSG.KD.Fi24Alpha.Pc.v1156, CFSG.KD.Fi24Alpha.Pc.v1157, CFSG.KD.Fi24Alpha.Pc.v1158, CFSG.KD.Fi24Alpha.Pc.v1159]
theorem CFSG.KD.Fi24Alpha.Pc.p1158 : Nat.beq (runC AR SD 1146 (ckL CFSG.KD.Fi24Alpha.Pc.l1160) 2 1158 CFSG.KD.Fi24Alpha.Pc.l1158) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1160 : Nat := CFSG.KD.Fi24Alpha.KV8 14
theorem CFSG.KD.Fi24Alpha.Pc.f80 : Nat.beq (runC AR SD 1146 (finC AR SD (nat_lit 80) 1146 1161) 1 1160 CFSG.KD.Fi24Alpha.Pc.l1160) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk80 : chk (nat_lit 80) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 80) (lo := 1146) (hi := 1161) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 1148) CFSG.KD.Fi24Alpha.Pc.p1146 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 1150) CFSG.KD.Fi24Alpha.Pc.p1148 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 1152) CFSG.KD.Fi24Alpha.Pc.p1150 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 1154) CFSG.KD.Fi24Alpha.Pc.p1152 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 1156) CFSG.KD.Fi24Alpha.Pc.p1154 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 1158) CFSG.KD.Fi24Alpha.Pc.p1156 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 1160) CFSG.KD.Fi24Alpha.Pc.p1158 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f80

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1161 : Nat := CFSG.KD.Fi24Alpha.KV8 15
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1162 : Nat := CFSG.KD.Fi24Alpha.KV8 16
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1163 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1161, CFSG.KD.Fi24Alpha.Pc.v1162]
theorem CFSG.KD.Fi24Alpha.Pc.p1161 : Nat.beq (runC AR SD 1161 (ckL CFSG.KD.Fi24Alpha.Pc.l1163) 2 1161 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1163 : Nat := CFSG.KD.Fi24Alpha.KV8 17
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1164 : Nat := CFSG.KD.Fi24Alpha.KV8 18
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1165 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1161, CFSG.KD.Fi24Alpha.Pc.v1162, CFSG.KD.Fi24Alpha.Pc.v1163, CFSG.KD.Fi24Alpha.Pc.v1164]
theorem CFSG.KD.Fi24Alpha.Pc.p1163 : Nat.beq (runC AR SD 1161 (ckL CFSG.KD.Fi24Alpha.Pc.l1165) 2 1163 CFSG.KD.Fi24Alpha.Pc.l1163) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1165 : Nat := CFSG.KD.Fi24Alpha.KV8 19
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1166 : Nat := CFSG.KD.Fi24Alpha.KV8 20
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1167 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1161, CFSG.KD.Fi24Alpha.Pc.v1162, CFSG.KD.Fi24Alpha.Pc.v1163, CFSG.KD.Fi24Alpha.Pc.v1164, CFSG.KD.Fi24Alpha.Pc.v1165, CFSG.KD.Fi24Alpha.Pc.v1166]
theorem CFSG.KD.Fi24Alpha.Pc.p1165 : Nat.beq (runC AR SD 1161 (ckL CFSG.KD.Fi24Alpha.Pc.l1167) 2 1165 CFSG.KD.Fi24Alpha.Pc.l1165) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1167 : Nat := CFSG.KD.Fi24Alpha.KV8 21
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1168 : Nat := CFSG.KD.Fi24Alpha.KV8 22
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1169 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1161, CFSG.KD.Fi24Alpha.Pc.v1162, CFSG.KD.Fi24Alpha.Pc.v1163, CFSG.KD.Fi24Alpha.Pc.v1164, CFSG.KD.Fi24Alpha.Pc.v1165, CFSG.KD.Fi24Alpha.Pc.v1166, CFSG.KD.Fi24Alpha.Pc.v1167, CFSG.KD.Fi24Alpha.Pc.v1168]
theorem CFSG.KD.Fi24Alpha.Pc.p1167 : Nat.beq (runC AR SD 1161 (ckL CFSG.KD.Fi24Alpha.Pc.l1169) 2 1167 CFSG.KD.Fi24Alpha.Pc.l1167) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1169 : Nat := CFSG.KD.Fi24Alpha.KV8 23
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1170 : Nat := CFSG.KD.Fi24Alpha.KV8 24
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1171 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1161, CFSG.KD.Fi24Alpha.Pc.v1162, CFSG.KD.Fi24Alpha.Pc.v1163, CFSG.KD.Fi24Alpha.Pc.v1164, CFSG.KD.Fi24Alpha.Pc.v1165, CFSG.KD.Fi24Alpha.Pc.v1166, CFSG.KD.Fi24Alpha.Pc.v1167, CFSG.KD.Fi24Alpha.Pc.v1168, CFSG.KD.Fi24Alpha.Pc.v1169, CFSG.KD.Fi24Alpha.Pc.v1170]
theorem CFSG.KD.Fi24Alpha.Pc.p1169 : Nat.beq (runC AR SD 1161 (ckL CFSG.KD.Fi24Alpha.Pc.l1171) 2 1169 CFSG.KD.Fi24Alpha.Pc.l1169) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1171 : Nat := CFSG.KD.Fi24Alpha.KV8 25
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1172 : Nat := CFSG.KD.Fi24Alpha.KV8 26
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1173 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1161, CFSG.KD.Fi24Alpha.Pc.v1162, CFSG.KD.Fi24Alpha.Pc.v1163, CFSG.KD.Fi24Alpha.Pc.v1164, CFSG.KD.Fi24Alpha.Pc.v1165, CFSG.KD.Fi24Alpha.Pc.v1166, CFSG.KD.Fi24Alpha.Pc.v1167, CFSG.KD.Fi24Alpha.Pc.v1168, CFSG.KD.Fi24Alpha.Pc.v1169, CFSG.KD.Fi24Alpha.Pc.v1170, CFSG.KD.Fi24Alpha.Pc.v1171, CFSG.KD.Fi24Alpha.Pc.v1172]
theorem CFSG.KD.Fi24Alpha.Pc.p1171 : Nat.beq (runC AR SD 1161 (ckL CFSG.KD.Fi24Alpha.Pc.l1173) 2 1171 CFSG.KD.Fi24Alpha.Pc.l1171) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1173 : Nat := CFSG.KD.Fi24Alpha.KV8 27
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1174 : Nat := CFSG.KD.Fi24Alpha.KV8 28
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1175 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1161, CFSG.KD.Fi24Alpha.Pc.v1162, CFSG.KD.Fi24Alpha.Pc.v1163, CFSG.KD.Fi24Alpha.Pc.v1164, CFSG.KD.Fi24Alpha.Pc.v1165, CFSG.KD.Fi24Alpha.Pc.v1166, CFSG.KD.Fi24Alpha.Pc.v1167, CFSG.KD.Fi24Alpha.Pc.v1168, CFSG.KD.Fi24Alpha.Pc.v1169, CFSG.KD.Fi24Alpha.Pc.v1170, CFSG.KD.Fi24Alpha.Pc.v1171, CFSG.KD.Fi24Alpha.Pc.v1172, CFSG.KD.Fi24Alpha.Pc.v1173, CFSG.KD.Fi24Alpha.Pc.v1174]
theorem CFSG.KD.Fi24Alpha.Pc.p1173 : Nat.beq (runC AR SD 1161 (ckL CFSG.KD.Fi24Alpha.Pc.l1175) 2 1173 CFSG.KD.Fi24Alpha.Pc.l1173) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1175 : Nat := CFSG.KD.Fi24Alpha.KV8 29
theorem CFSG.KD.Fi24Alpha.Pc.f81 : Nat.beq (runC AR SD 1161 (finC AR SD (nat_lit 81) 1161 1176) 1 1175 CFSG.KD.Fi24Alpha.Pc.l1175) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk81 : chk (nat_lit 81) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 81) (lo := 1161) (hi := 1176) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 1163) CFSG.KD.Fi24Alpha.Pc.p1161 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 1165) CFSG.KD.Fi24Alpha.Pc.p1163 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 1167) CFSG.KD.Fi24Alpha.Pc.p1165 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 1169) CFSG.KD.Fi24Alpha.Pc.p1167 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 1171) CFSG.KD.Fi24Alpha.Pc.p1169 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 1173) CFSG.KD.Fi24Alpha.Pc.p1171 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 1175) CFSG.KD.Fi24Alpha.Pc.p1173 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f81

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a1176_2 : Nat := CFSG.KD.Fi24Alpha.KV8 30
theorem CFSG.KD.Fi24Alpha.Pc.q1176_2 : Nat.beq (powTop AR.mul (getV AR SD 1176 [] (SD.na.getD 1176 0)) (SD.nk.getD 1176 1) 2 (ckP CFSG.KD.Fi24Alpha.Pc.a1176_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a1176_1 : Nat := CFSG.KD.Fi24Alpha.KV8 31
theorem CFSG.KD.Fi24Alpha.Pc.q1176_1 : Nat.beq (powTop AR.mul (getV AR SD 1176 [] (SD.na.getD 1176 0)) (SD.nk.getD 1176 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a1176_1) 1 CFSG.KD.Fi24Alpha.Pc.a1176_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1176 : Nat := CFSG.KD.Fi24Alpha.KV8 32
theorem CFSG.KD.Fi24Alpha.Pc.r1176 : Nat.beq (powR AR.mul AR.one (getV AR SD 1176 [] (SD.na.getD 1176 0)) (SD.nk.getD 1176 1) 1 CFSG.KD.Fi24Alpha.Pc.a1176_1 true) CFSG.KD.Fi24Alpha.Pc.v1176 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1177 : Nat := CFSG.KD.Fi24Alpha.KV8 33
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1178 : Nat := CFSG.KD.Fi24Alpha.KV8 34
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1177 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1176]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1179 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1176, CFSG.KD.Fi24Alpha.Pc.v1177, CFSG.KD.Fi24Alpha.Pc.v1178]
theorem CFSG.KD.Fi24Alpha.Pc.p1177 : Nat.beq (runC AR SD 1176 (ckL CFSG.KD.Fi24Alpha.Pc.l1179) 2 1177 CFSG.KD.Fi24Alpha.Pc.l1177) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1179 : Nat := CFSG.KD.Fi24Alpha.KV8 35
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1180 : Nat := CFSG.KD.Fi24Alpha.KV8 36
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1181 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1176, CFSG.KD.Fi24Alpha.Pc.v1177, CFSG.KD.Fi24Alpha.Pc.v1178, CFSG.KD.Fi24Alpha.Pc.v1179, CFSG.KD.Fi24Alpha.Pc.v1180]
theorem CFSG.KD.Fi24Alpha.Pc.p1179 : Nat.beq (runC AR SD 1176 (ckL CFSG.KD.Fi24Alpha.Pc.l1181) 2 1179 CFSG.KD.Fi24Alpha.Pc.l1179) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1181 : Nat := CFSG.KD.Fi24Alpha.KV8 37
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1182 : Nat := CFSG.KD.Fi24Alpha.KV8 38
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1183 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1176, CFSG.KD.Fi24Alpha.Pc.v1177, CFSG.KD.Fi24Alpha.Pc.v1178, CFSG.KD.Fi24Alpha.Pc.v1179, CFSG.KD.Fi24Alpha.Pc.v1180, CFSG.KD.Fi24Alpha.Pc.v1181, CFSG.KD.Fi24Alpha.Pc.v1182]
theorem CFSG.KD.Fi24Alpha.Pc.p1181 : Nat.beq (runC AR SD 1176 (ckL CFSG.KD.Fi24Alpha.Pc.l1183) 2 1181 CFSG.KD.Fi24Alpha.Pc.l1181) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1183 : Nat := CFSG.KD.Fi24Alpha.KV8 39
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1184 : Nat := CFSG.KD.Fi24Alpha.KV8 40
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1185 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1176, CFSG.KD.Fi24Alpha.Pc.v1177, CFSG.KD.Fi24Alpha.Pc.v1178, CFSG.KD.Fi24Alpha.Pc.v1179, CFSG.KD.Fi24Alpha.Pc.v1180, CFSG.KD.Fi24Alpha.Pc.v1181, CFSG.KD.Fi24Alpha.Pc.v1182, CFSG.KD.Fi24Alpha.Pc.v1183, CFSG.KD.Fi24Alpha.Pc.v1184]
theorem CFSG.KD.Fi24Alpha.Pc.p1183 : Nat.beq (runC AR SD 1176 (ckL CFSG.KD.Fi24Alpha.Pc.l1185) 2 1183 CFSG.KD.Fi24Alpha.Pc.l1183) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1185 : Nat := CFSG.KD.Fi24Alpha.KV8 41
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1186 : Nat := CFSG.KD.Fi24Alpha.KV8 42
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1187 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1176, CFSG.KD.Fi24Alpha.Pc.v1177, CFSG.KD.Fi24Alpha.Pc.v1178, CFSG.KD.Fi24Alpha.Pc.v1179, CFSG.KD.Fi24Alpha.Pc.v1180, CFSG.KD.Fi24Alpha.Pc.v1181, CFSG.KD.Fi24Alpha.Pc.v1182, CFSG.KD.Fi24Alpha.Pc.v1183, CFSG.KD.Fi24Alpha.Pc.v1184, CFSG.KD.Fi24Alpha.Pc.v1185, CFSG.KD.Fi24Alpha.Pc.v1186]
theorem CFSG.KD.Fi24Alpha.Pc.p1185 : Nat.beq (runC AR SD 1176 (ckL CFSG.KD.Fi24Alpha.Pc.l1187) 2 1185 CFSG.KD.Fi24Alpha.Pc.l1185) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1187 : Nat := CFSG.KD.Fi24Alpha.KV8 43
theorem CFSG.KD.Fi24Alpha.Pc.f82 : Nat.beq (runC AR SD 1176 (finC AR SD (nat_lit 82) 1176 1188) 1 1187 CFSG.KD.Fi24Alpha.Pc.l1187) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk82 : chk (nat_lit 82) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 82) (lo := 1176) (hi := 1188) (m := 12) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 12) (m2 := 11) (j2 := 1177) (Lr := CFSG.KD.Fi24Alpha.Pc.l1177) ((nodeV_pow (R := AR) (D := SD) (lo := 1176) (L := []) (j := 1176) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1176 [] (SD.na.getD 1176 0)) (SD.nk.getD 1176 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q1176_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Alpha.Pc.q1176_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r1176))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 1179) CFSG.KD.Fi24Alpha.Pc.p1177 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 1181) CFSG.KD.Fi24Alpha.Pc.p1179 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 1183) CFSG.KD.Fi24Alpha.Pc.p1181 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 1185) CFSG.KD.Fi24Alpha.Pc.p1183 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 1187) CFSG.KD.Fi24Alpha.Pc.p1185 rfl rfl)))))))).trans CFSG.KD.Fi24Alpha.Pc.f82

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1188 : Nat := CFSG.KD.Fi24Alpha.KV8 44
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1189 : Nat := CFSG.KD.Fi24Alpha.KV8 45
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1190 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1188, CFSG.KD.Fi24Alpha.Pc.v1189]
theorem CFSG.KD.Fi24Alpha.Pc.p1188 : Nat.beq (runC AR SD 1188 (ckL CFSG.KD.Fi24Alpha.Pc.l1190) 2 1188 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1190 : Nat := CFSG.KD.Fi24Alpha.KV8 46
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1191 : Nat := CFSG.KD.Fi24Alpha.KV8 47
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1192 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1188, CFSG.KD.Fi24Alpha.Pc.v1189, CFSG.KD.Fi24Alpha.Pc.v1190, CFSG.KD.Fi24Alpha.Pc.v1191]
theorem CFSG.KD.Fi24Alpha.Pc.p1190 : Nat.beq (runC AR SD 1188 (ckL CFSG.KD.Fi24Alpha.Pc.l1192) 2 1190 CFSG.KD.Fi24Alpha.Pc.l1190) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1192 : Nat := CFSG.KD.Fi24Alpha.KV8 48
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1193 : Nat := CFSG.KD.Fi24Alpha.KV8 49
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1194 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1188, CFSG.KD.Fi24Alpha.Pc.v1189, CFSG.KD.Fi24Alpha.Pc.v1190, CFSG.KD.Fi24Alpha.Pc.v1191, CFSG.KD.Fi24Alpha.Pc.v1192, CFSG.KD.Fi24Alpha.Pc.v1193]
theorem CFSG.KD.Fi24Alpha.Pc.p1192 : Nat.beq (runC AR SD 1188 (ckL CFSG.KD.Fi24Alpha.Pc.l1194) 2 1192 CFSG.KD.Fi24Alpha.Pc.l1192) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1194 : Nat := CFSG.KD.Fi24Alpha.KV8 50
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1195 : Nat := CFSG.KD.Fi24Alpha.KV8 51
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1196 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1188, CFSG.KD.Fi24Alpha.Pc.v1189, CFSG.KD.Fi24Alpha.Pc.v1190, CFSG.KD.Fi24Alpha.Pc.v1191, CFSG.KD.Fi24Alpha.Pc.v1192, CFSG.KD.Fi24Alpha.Pc.v1193, CFSG.KD.Fi24Alpha.Pc.v1194, CFSG.KD.Fi24Alpha.Pc.v1195]
theorem CFSG.KD.Fi24Alpha.Pc.p1194 : Nat.beq (runC AR SD 1188 (ckL CFSG.KD.Fi24Alpha.Pc.l1196) 2 1194 CFSG.KD.Fi24Alpha.Pc.l1194) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1196 : Nat := CFSG.KD.Fi24Alpha.KV8 52
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1197 : Nat := CFSG.KD.Fi24Alpha.KV8 53
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1198 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1188, CFSG.KD.Fi24Alpha.Pc.v1189, CFSG.KD.Fi24Alpha.Pc.v1190, CFSG.KD.Fi24Alpha.Pc.v1191, CFSG.KD.Fi24Alpha.Pc.v1192, CFSG.KD.Fi24Alpha.Pc.v1193, CFSG.KD.Fi24Alpha.Pc.v1194, CFSG.KD.Fi24Alpha.Pc.v1195, CFSG.KD.Fi24Alpha.Pc.v1196, CFSG.KD.Fi24Alpha.Pc.v1197]
theorem CFSG.KD.Fi24Alpha.Pc.p1196 : Nat.beq (runC AR SD 1188 (ckL CFSG.KD.Fi24Alpha.Pc.l1198) 2 1196 CFSG.KD.Fi24Alpha.Pc.l1196) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1198 : Nat := CFSG.KD.Fi24Alpha.KV8 54
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1199 : Nat := CFSG.KD.Fi24Alpha.KV8 55
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1200 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1188, CFSG.KD.Fi24Alpha.Pc.v1189, CFSG.KD.Fi24Alpha.Pc.v1190, CFSG.KD.Fi24Alpha.Pc.v1191, CFSG.KD.Fi24Alpha.Pc.v1192, CFSG.KD.Fi24Alpha.Pc.v1193, CFSG.KD.Fi24Alpha.Pc.v1194, CFSG.KD.Fi24Alpha.Pc.v1195, CFSG.KD.Fi24Alpha.Pc.v1196, CFSG.KD.Fi24Alpha.Pc.v1197, CFSG.KD.Fi24Alpha.Pc.v1198, CFSG.KD.Fi24Alpha.Pc.v1199]
theorem CFSG.KD.Fi24Alpha.Pc.p1198 : Nat.beq (runC AR SD 1188 (ckL CFSG.KD.Fi24Alpha.Pc.l1200) 2 1198 CFSG.KD.Fi24Alpha.Pc.l1198) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1200 : Nat := CFSG.KD.Fi24Alpha.KV8 56
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1201 : Nat := CFSG.KD.Fi24Alpha.KV8 57
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1202 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1188, CFSG.KD.Fi24Alpha.Pc.v1189, CFSG.KD.Fi24Alpha.Pc.v1190, CFSG.KD.Fi24Alpha.Pc.v1191, CFSG.KD.Fi24Alpha.Pc.v1192, CFSG.KD.Fi24Alpha.Pc.v1193, CFSG.KD.Fi24Alpha.Pc.v1194, CFSG.KD.Fi24Alpha.Pc.v1195, CFSG.KD.Fi24Alpha.Pc.v1196, CFSG.KD.Fi24Alpha.Pc.v1197, CFSG.KD.Fi24Alpha.Pc.v1198, CFSG.KD.Fi24Alpha.Pc.v1199, CFSG.KD.Fi24Alpha.Pc.v1200, CFSG.KD.Fi24Alpha.Pc.v1201]
theorem CFSG.KD.Fi24Alpha.Pc.p1200 : Nat.beq (runC AR SD 1188 (ckL CFSG.KD.Fi24Alpha.Pc.l1202) 2 1200 CFSG.KD.Fi24Alpha.Pc.l1200) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1202 : Nat := CFSG.KD.Fi24Alpha.KV8 58
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1203 : Nat := CFSG.KD.Fi24Alpha.KV8 59
theorem CFSG.KD.Fi24Alpha.Pc.f83 : Nat.beq (runC AR SD 1188 (finC AR SD (nat_lit 83) 1188 1204) 2 1202 CFSG.KD.Fi24Alpha.Pc.l1202) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk83 : chk (nat_lit 83) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 83) (lo := 1188) (hi := 1204) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1190) CFSG.KD.Fi24Alpha.Pc.p1188 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1192) CFSG.KD.Fi24Alpha.Pc.p1190 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1194) CFSG.KD.Fi24Alpha.Pc.p1192 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1196) CFSG.KD.Fi24Alpha.Pc.p1194 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1198) CFSG.KD.Fi24Alpha.Pc.p1196 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1200) CFSG.KD.Fi24Alpha.Pc.p1198 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1202) CFSG.KD.Fi24Alpha.Pc.p1200 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f83

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1204 : Nat := CFSG.KD.Fi24Alpha.KV8 60
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1205 : Nat := CFSG.KD.Fi24Alpha.KV8 61
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1206 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1204, CFSG.KD.Fi24Alpha.Pc.v1205]
theorem CFSG.KD.Fi24Alpha.Pc.p1204 : Nat.beq (runC AR SD 1204 (ckL CFSG.KD.Fi24Alpha.Pc.l1206) 2 1204 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1206 : Nat := CFSG.KD.Fi24Alpha.KV8 62
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1207 : Nat := CFSG.KD.Fi24Alpha.KV8 63
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1208 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1204, CFSG.KD.Fi24Alpha.Pc.v1205, CFSG.KD.Fi24Alpha.Pc.v1206, CFSG.KD.Fi24Alpha.Pc.v1207]
theorem CFSG.KD.Fi24Alpha.Pc.p1206 : Nat.beq (runC AR SD 1204 (ckL CFSG.KD.Fi24Alpha.Pc.l1208) 2 1206 CFSG.KD.Fi24Alpha.Pc.l1206) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1208 : Nat := CFSG.KD.Fi24Alpha.KV8 64
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1209 : Nat := CFSG.KD.Fi24Alpha.KV8 65
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1210 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1204, CFSG.KD.Fi24Alpha.Pc.v1205, CFSG.KD.Fi24Alpha.Pc.v1206, CFSG.KD.Fi24Alpha.Pc.v1207, CFSG.KD.Fi24Alpha.Pc.v1208, CFSG.KD.Fi24Alpha.Pc.v1209]
theorem CFSG.KD.Fi24Alpha.Pc.p1208 : Nat.beq (runC AR SD 1204 (ckL CFSG.KD.Fi24Alpha.Pc.l1210) 2 1208 CFSG.KD.Fi24Alpha.Pc.l1208) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1210 : Nat := CFSG.KD.Fi24Alpha.KV8 66
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1211 : Nat := CFSG.KD.Fi24Alpha.KV8 67
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1212 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1204, CFSG.KD.Fi24Alpha.Pc.v1205, CFSG.KD.Fi24Alpha.Pc.v1206, CFSG.KD.Fi24Alpha.Pc.v1207, CFSG.KD.Fi24Alpha.Pc.v1208, CFSG.KD.Fi24Alpha.Pc.v1209, CFSG.KD.Fi24Alpha.Pc.v1210, CFSG.KD.Fi24Alpha.Pc.v1211]
theorem CFSG.KD.Fi24Alpha.Pc.p1210 : Nat.beq (runC AR SD 1204 (ckL CFSG.KD.Fi24Alpha.Pc.l1212) 2 1210 CFSG.KD.Fi24Alpha.Pc.l1210) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1212 : Nat := CFSG.KD.Fi24Alpha.KV8 68
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1213 : Nat := CFSG.KD.Fi24Alpha.KV8 69
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1214 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1204, CFSG.KD.Fi24Alpha.Pc.v1205, CFSG.KD.Fi24Alpha.Pc.v1206, CFSG.KD.Fi24Alpha.Pc.v1207, CFSG.KD.Fi24Alpha.Pc.v1208, CFSG.KD.Fi24Alpha.Pc.v1209, CFSG.KD.Fi24Alpha.Pc.v1210, CFSG.KD.Fi24Alpha.Pc.v1211, CFSG.KD.Fi24Alpha.Pc.v1212, CFSG.KD.Fi24Alpha.Pc.v1213]
theorem CFSG.KD.Fi24Alpha.Pc.p1212 : Nat.beq (runC AR SD 1204 (ckL CFSG.KD.Fi24Alpha.Pc.l1214) 2 1212 CFSG.KD.Fi24Alpha.Pc.l1212) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1214 : Nat := CFSG.KD.Fi24Alpha.KV8 70
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1215 : Nat := CFSG.KD.Fi24Alpha.KV8 71
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1216 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1204, CFSG.KD.Fi24Alpha.Pc.v1205, CFSG.KD.Fi24Alpha.Pc.v1206, CFSG.KD.Fi24Alpha.Pc.v1207, CFSG.KD.Fi24Alpha.Pc.v1208, CFSG.KD.Fi24Alpha.Pc.v1209, CFSG.KD.Fi24Alpha.Pc.v1210, CFSG.KD.Fi24Alpha.Pc.v1211, CFSG.KD.Fi24Alpha.Pc.v1212, CFSG.KD.Fi24Alpha.Pc.v1213, CFSG.KD.Fi24Alpha.Pc.v1214, CFSG.KD.Fi24Alpha.Pc.v1215]
theorem CFSG.KD.Fi24Alpha.Pc.p1214 : Nat.beq (runC AR SD 1204 (ckL CFSG.KD.Fi24Alpha.Pc.l1216) 2 1214 CFSG.KD.Fi24Alpha.Pc.l1214) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1216 : Nat := CFSG.KD.Fi24Alpha.KV8 72
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1217 : Nat := CFSG.KD.Fi24Alpha.KV8 73
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1218 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1204, CFSG.KD.Fi24Alpha.Pc.v1205, CFSG.KD.Fi24Alpha.Pc.v1206, CFSG.KD.Fi24Alpha.Pc.v1207, CFSG.KD.Fi24Alpha.Pc.v1208, CFSG.KD.Fi24Alpha.Pc.v1209, CFSG.KD.Fi24Alpha.Pc.v1210, CFSG.KD.Fi24Alpha.Pc.v1211, CFSG.KD.Fi24Alpha.Pc.v1212, CFSG.KD.Fi24Alpha.Pc.v1213, CFSG.KD.Fi24Alpha.Pc.v1214, CFSG.KD.Fi24Alpha.Pc.v1215, CFSG.KD.Fi24Alpha.Pc.v1216, CFSG.KD.Fi24Alpha.Pc.v1217]
theorem CFSG.KD.Fi24Alpha.Pc.p1216 : Nat.beq (runC AR SD 1204 (ckL CFSG.KD.Fi24Alpha.Pc.l1218) 2 1216 CFSG.KD.Fi24Alpha.Pc.l1216) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1218 : Nat := CFSG.KD.Fi24Alpha.KV8 74
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1219 : Nat := CFSG.KD.Fi24Alpha.KV8 75
theorem CFSG.KD.Fi24Alpha.Pc.f84 : Nat.beq (runC AR SD 1204 (finC AR SD (nat_lit 84) 1204 1220) 2 1218 CFSG.KD.Fi24Alpha.Pc.l1218) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk84 : chk (nat_lit 84) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 84) (lo := 1204) (hi := 1220) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1206) CFSG.KD.Fi24Alpha.Pc.p1204 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1208) CFSG.KD.Fi24Alpha.Pc.p1206 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1210) CFSG.KD.Fi24Alpha.Pc.p1208 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1212) CFSG.KD.Fi24Alpha.Pc.p1210 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1214) CFSG.KD.Fi24Alpha.Pc.p1212 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1216) CFSG.KD.Fi24Alpha.Pc.p1214 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1218) CFSG.KD.Fi24Alpha.Pc.p1216 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f84

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1220 : Nat := CFSG.KD.Fi24Alpha.KV8 76
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1221 : Nat := CFSG.KD.Fi24Alpha.KV8 77
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1222 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1220, CFSG.KD.Fi24Alpha.Pc.v1221]
theorem CFSG.KD.Fi24Alpha.Pc.p1220 : Nat.beq (runC AR SD 1220 (ckL CFSG.KD.Fi24Alpha.Pc.l1222) 2 1220 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1222 : Nat := CFSG.KD.Fi24Alpha.KV8 78
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1223 : Nat := CFSG.KD.Fi24Alpha.KV8 79
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1224 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1220, CFSG.KD.Fi24Alpha.Pc.v1221, CFSG.KD.Fi24Alpha.Pc.v1222, CFSG.KD.Fi24Alpha.Pc.v1223]
theorem CFSG.KD.Fi24Alpha.Pc.p1222 : Nat.beq (runC AR SD 1220 (ckL CFSG.KD.Fi24Alpha.Pc.l1224) 2 1222 CFSG.KD.Fi24Alpha.Pc.l1222) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1224 : Nat := CFSG.KD.Fi24Alpha.KV8 80
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1225 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1220, CFSG.KD.Fi24Alpha.Pc.v1221, CFSG.KD.Fi24Alpha.Pc.v1222, CFSG.KD.Fi24Alpha.Pc.v1223, CFSG.KD.Fi24Alpha.Pc.v1224]
theorem CFSG.KD.Fi24Alpha.Pc.p1224 : Nat.beq (runC AR SD 1220 (ckL CFSG.KD.Fi24Alpha.Pc.l1225) 1 1224 CFSG.KD.Fi24Alpha.Pc.l1224) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a1225_4 : Nat := CFSG.KD.Fi24Alpha.KV8 81
theorem CFSG.KD.Fi24Alpha.Pc.q1225_4 : Nat.beq (powTop AR.mul (getV AR SD 1220 CFSG.KD.Fi24Alpha.Pc.l1225 (SD.na.getD 1225 0)) (SD.nk.getD 1225 1) 4 (ckP CFSG.KD.Fi24Alpha.Pc.a1225_4) 12 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a1225_3 : Nat := CFSG.KD.Fi24Alpha.KV8 82
theorem CFSG.KD.Fi24Alpha.Pc.q1225_3 : Nat.beq (powTop AR.mul (getV AR SD 1220 CFSG.KD.Fi24Alpha.Pc.l1225 (SD.na.getD 1225 0)) (SD.nk.getD 1225 1) 3 (ckP CFSG.KD.Fi24Alpha.Pc.a1225_3) 1 CFSG.KD.Fi24Alpha.Pc.a1225_4 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a1225_2 : Nat := CFSG.KD.Fi24Alpha.KV8 83
theorem CFSG.KD.Fi24Alpha.Pc.q1225_2 : Nat.beq (powTop AR.mul (getV AR SD 1220 CFSG.KD.Fi24Alpha.Pc.l1225 (SD.na.getD 1225 0)) (SD.nk.getD 1225 1) 2 (ckP CFSG.KD.Fi24Alpha.Pc.a1225_2) 1 CFSG.KD.Fi24Alpha.Pc.a1225_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a1225_1 : Nat := CFSG.KD.Fi24Alpha.KV8 84
theorem CFSG.KD.Fi24Alpha.Pc.q1225_1 : Nat.beq (powTop AR.mul (getV AR SD 1220 CFSG.KD.Fi24Alpha.Pc.l1225 (SD.na.getD 1225 0)) (SD.nk.getD 1225 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a1225_1) 1 CFSG.KD.Fi24Alpha.Pc.a1225_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1225 : Nat := CFSG.KD.Fi24Alpha.KV8 85
theorem CFSG.KD.Fi24Alpha.Pc.r1225 : Nat.beq (powR AR.mul AR.one (getV AR SD 1220 CFSG.KD.Fi24Alpha.Pc.l1225 (SD.na.getD 1225 0)) (SD.nk.getD 1225 1) 1 CFSG.KD.Fi24Alpha.Pc.a1225_1 true) CFSG.KD.Fi24Alpha.Pc.v1225 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1226 : Nat := CFSG.KD.Fi24Alpha.KV8 86
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1227 : Nat := CFSG.KD.Fi24Alpha.KV8 87
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1226 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1220, CFSG.KD.Fi24Alpha.Pc.v1221, CFSG.KD.Fi24Alpha.Pc.v1222, CFSG.KD.Fi24Alpha.Pc.v1223, CFSG.KD.Fi24Alpha.Pc.v1224, CFSG.KD.Fi24Alpha.Pc.v1225]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1228 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1220, CFSG.KD.Fi24Alpha.Pc.v1221, CFSG.KD.Fi24Alpha.Pc.v1222, CFSG.KD.Fi24Alpha.Pc.v1223, CFSG.KD.Fi24Alpha.Pc.v1224, CFSG.KD.Fi24Alpha.Pc.v1225, CFSG.KD.Fi24Alpha.Pc.v1226, CFSG.KD.Fi24Alpha.Pc.v1227]
theorem CFSG.KD.Fi24Alpha.Pc.p1226 : Nat.beq (runC AR SD 1220 (ckL CFSG.KD.Fi24Alpha.Pc.l1228) 2 1226 CFSG.KD.Fi24Alpha.Pc.l1226) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1228 : Nat := CFSG.KD.Fi24Alpha.KV8 88
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1229 : Nat := CFSG.KD.Fi24Alpha.KV8 89
theorem CFSG.KD.Fi24Alpha.Pc.f85 : Nat.beq (runC AR SD 1220 (finC AR SD (nat_lit 85) 1220 1230) 2 1228 CFSG.KD.Fi24Alpha.Pc.l1228) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk85 : chk (nat_lit 85) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 85) (lo := 1220) (hi := 1230) (m := 10) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 10) (m2 := 8) (j2 := 1222) CFSG.KD.Fi24Alpha.Pc.p1220 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1224) CFSG.KD.Fi24Alpha.Pc.p1222 rfl rfl).trans ((runC_seq (m := 6) (m2 := 5) (j2 := 1225) CFSG.KD.Fi24Alpha.Pc.p1224 rfl rfl).trans ((runC_node (m := 5) (m2 := 4) (j2 := 1226) (Lr := CFSG.KD.Fi24Alpha.Pc.l1226) ((nodeV_pow (R := AR) (D := SD) (lo := 1220) (L := CFSG.KD.Fi24Alpha.Pc.l1225) (j := 1225) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1220 CFSG.KD.Fi24Alpha.Pc.l1225 (SD.na.getD 1225 0)) (SD.nk.getD 1225 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q1225_4 rfl).trans ((powR_seq (n := 4) CFSG.KD.Fi24Alpha.Pc.q1225_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Alpha.Pc.q1225_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Alpha.Pc.q1225_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r1225))))))) (by quickRfl) rfl rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1228) CFSG.KD.Fi24Alpha.Pc.p1226 rfl rfl))))))).trans CFSG.KD.Fi24Alpha.Pc.f85

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1230 : Nat := CFSG.KD.Fi24Alpha.KV8 90
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1231 : Nat := CFSG.KD.Fi24Alpha.KV8 91
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1232 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1230, CFSG.KD.Fi24Alpha.Pc.v1231]
theorem CFSG.KD.Fi24Alpha.Pc.p1230 : Nat.beq (runC AR SD 1230 (ckL CFSG.KD.Fi24Alpha.Pc.l1232) 2 1230 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1232 : Nat := CFSG.KD.Fi24Alpha.KV8 92
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1233 : Nat := CFSG.KD.Fi24Alpha.KV8 93
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1234 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1230, CFSG.KD.Fi24Alpha.Pc.v1231, CFSG.KD.Fi24Alpha.Pc.v1232, CFSG.KD.Fi24Alpha.Pc.v1233]
theorem CFSG.KD.Fi24Alpha.Pc.p1232 : Nat.beq (runC AR SD 1230 (ckL CFSG.KD.Fi24Alpha.Pc.l1234) 2 1232 CFSG.KD.Fi24Alpha.Pc.l1232) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1234 : Nat := CFSG.KD.Fi24Alpha.KV8 94
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1235 : Nat := CFSG.KD.Fi24Alpha.KV8 95
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1236 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1230, CFSG.KD.Fi24Alpha.Pc.v1231, CFSG.KD.Fi24Alpha.Pc.v1232, CFSG.KD.Fi24Alpha.Pc.v1233, CFSG.KD.Fi24Alpha.Pc.v1234, CFSG.KD.Fi24Alpha.Pc.v1235]
theorem CFSG.KD.Fi24Alpha.Pc.p1234 : Nat.beq (runC AR SD 1230 (ckL CFSG.KD.Fi24Alpha.Pc.l1236) 2 1234 CFSG.KD.Fi24Alpha.Pc.l1234) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1236 : Nat := CFSG.KD.Fi24Alpha.KV8 96
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1237 : Nat := CFSG.KD.Fi24Alpha.KV8 97
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1238 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1230, CFSG.KD.Fi24Alpha.Pc.v1231, CFSG.KD.Fi24Alpha.Pc.v1232, CFSG.KD.Fi24Alpha.Pc.v1233, CFSG.KD.Fi24Alpha.Pc.v1234, CFSG.KD.Fi24Alpha.Pc.v1235, CFSG.KD.Fi24Alpha.Pc.v1236, CFSG.KD.Fi24Alpha.Pc.v1237]
theorem CFSG.KD.Fi24Alpha.Pc.p1236 : Nat.beq (runC AR SD 1230 (ckL CFSG.KD.Fi24Alpha.Pc.l1238) 2 1236 CFSG.KD.Fi24Alpha.Pc.l1236) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1238 : Nat := CFSG.KD.Fi24Alpha.KV8 98
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1239 : Nat := CFSG.KD.Fi24Alpha.KV8 99
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1240 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1230, CFSG.KD.Fi24Alpha.Pc.v1231, CFSG.KD.Fi24Alpha.Pc.v1232, CFSG.KD.Fi24Alpha.Pc.v1233, CFSG.KD.Fi24Alpha.Pc.v1234, CFSG.KD.Fi24Alpha.Pc.v1235, CFSG.KD.Fi24Alpha.Pc.v1236, CFSG.KD.Fi24Alpha.Pc.v1237, CFSG.KD.Fi24Alpha.Pc.v1238, CFSG.KD.Fi24Alpha.Pc.v1239]
theorem CFSG.KD.Fi24Alpha.Pc.p1238 : Nat.beq (runC AR SD 1230 (ckL CFSG.KD.Fi24Alpha.Pc.l1240) 2 1238 CFSG.KD.Fi24Alpha.Pc.l1238) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1240 : Nat := CFSG.KD.Fi24Alpha.KV8 100
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1241 : Nat := CFSG.KD.Fi24Alpha.KV8 101
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1242 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1230, CFSG.KD.Fi24Alpha.Pc.v1231, CFSG.KD.Fi24Alpha.Pc.v1232, CFSG.KD.Fi24Alpha.Pc.v1233, CFSG.KD.Fi24Alpha.Pc.v1234, CFSG.KD.Fi24Alpha.Pc.v1235, CFSG.KD.Fi24Alpha.Pc.v1236, CFSG.KD.Fi24Alpha.Pc.v1237, CFSG.KD.Fi24Alpha.Pc.v1238, CFSG.KD.Fi24Alpha.Pc.v1239, CFSG.KD.Fi24Alpha.Pc.v1240, CFSG.KD.Fi24Alpha.Pc.v1241]
theorem CFSG.KD.Fi24Alpha.Pc.p1240 : Nat.beq (runC AR SD 1230 (ckL CFSG.KD.Fi24Alpha.Pc.l1242) 2 1240 CFSG.KD.Fi24Alpha.Pc.l1240) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1242 : Nat := CFSG.KD.Fi24Alpha.KV8 102
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1243 : Nat := CFSG.KD.Fi24Alpha.KV8 103
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1244 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1230, CFSG.KD.Fi24Alpha.Pc.v1231, CFSG.KD.Fi24Alpha.Pc.v1232, CFSG.KD.Fi24Alpha.Pc.v1233, CFSG.KD.Fi24Alpha.Pc.v1234, CFSG.KD.Fi24Alpha.Pc.v1235, CFSG.KD.Fi24Alpha.Pc.v1236, CFSG.KD.Fi24Alpha.Pc.v1237, CFSG.KD.Fi24Alpha.Pc.v1238, CFSG.KD.Fi24Alpha.Pc.v1239, CFSG.KD.Fi24Alpha.Pc.v1240, CFSG.KD.Fi24Alpha.Pc.v1241, CFSG.KD.Fi24Alpha.Pc.v1242, CFSG.KD.Fi24Alpha.Pc.v1243]
theorem CFSG.KD.Fi24Alpha.Pc.p1242 : Nat.beq (runC AR SD 1230 (ckL CFSG.KD.Fi24Alpha.Pc.l1244) 2 1242 CFSG.KD.Fi24Alpha.Pc.l1242) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1244 : Nat := CFSG.KD.Fi24Alpha.KV8 104
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1245 : Nat := CFSG.KD.Fi24Alpha.KV8 105
theorem CFSG.KD.Fi24Alpha.Pc.f86 : Nat.beq (runC AR SD 1230 (finC AR SD (nat_lit 86) 1230 1246) 2 1244 CFSG.KD.Fi24Alpha.Pc.l1244) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk86 : chk (nat_lit 86) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 86) (lo := 1230) (hi := 1246) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1232) CFSG.KD.Fi24Alpha.Pc.p1230 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1234) CFSG.KD.Fi24Alpha.Pc.p1232 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1236) CFSG.KD.Fi24Alpha.Pc.p1234 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1238) CFSG.KD.Fi24Alpha.Pc.p1236 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1240) CFSG.KD.Fi24Alpha.Pc.p1238 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1242) CFSG.KD.Fi24Alpha.Pc.p1240 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1244) CFSG.KD.Fi24Alpha.Pc.p1242 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f86

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1246 : Nat := CFSG.KD.Fi24Alpha.KV8 106
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1247 : Nat := CFSG.KD.Fi24Alpha.KV8 107
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1248 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1246, CFSG.KD.Fi24Alpha.Pc.v1247]
theorem CFSG.KD.Fi24Alpha.Pc.p1246 : Nat.beq (runC AR SD 1246 (ckL CFSG.KD.Fi24Alpha.Pc.l1248) 2 1246 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1248 : Nat := CFSG.KD.Fi24Alpha.KV8 108
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1249 : Nat := CFSG.KD.Fi24Alpha.KV8 109
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1250 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1246, CFSG.KD.Fi24Alpha.Pc.v1247, CFSG.KD.Fi24Alpha.Pc.v1248, CFSG.KD.Fi24Alpha.Pc.v1249]
theorem CFSG.KD.Fi24Alpha.Pc.p1248 : Nat.beq (runC AR SD 1246 (ckL CFSG.KD.Fi24Alpha.Pc.l1250) 2 1248 CFSG.KD.Fi24Alpha.Pc.l1248) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1250 : Nat := CFSG.KD.Fi24Alpha.KV8 110
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1251 : Nat := CFSG.KD.Fi24Alpha.KV8 111
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1252 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1246, CFSG.KD.Fi24Alpha.Pc.v1247, CFSG.KD.Fi24Alpha.Pc.v1248, CFSG.KD.Fi24Alpha.Pc.v1249, CFSG.KD.Fi24Alpha.Pc.v1250, CFSG.KD.Fi24Alpha.Pc.v1251]
theorem CFSG.KD.Fi24Alpha.Pc.p1250 : Nat.beq (runC AR SD 1246 (ckL CFSG.KD.Fi24Alpha.Pc.l1252) 2 1250 CFSG.KD.Fi24Alpha.Pc.l1250) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1252 : Nat := CFSG.KD.Fi24Alpha.KV8 112
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1253 : Nat := CFSG.KD.Fi24Alpha.KV8 113
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1254 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1246, CFSG.KD.Fi24Alpha.Pc.v1247, CFSG.KD.Fi24Alpha.Pc.v1248, CFSG.KD.Fi24Alpha.Pc.v1249, CFSG.KD.Fi24Alpha.Pc.v1250, CFSG.KD.Fi24Alpha.Pc.v1251, CFSG.KD.Fi24Alpha.Pc.v1252, CFSG.KD.Fi24Alpha.Pc.v1253]
theorem CFSG.KD.Fi24Alpha.Pc.p1252 : Nat.beq (runC AR SD 1246 (ckL CFSG.KD.Fi24Alpha.Pc.l1254) 2 1252 CFSG.KD.Fi24Alpha.Pc.l1252) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1254 : Nat := CFSG.KD.Fi24Alpha.KV8 114
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1255 : Nat := CFSG.KD.Fi24Alpha.KV8 115
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1256 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1246, CFSG.KD.Fi24Alpha.Pc.v1247, CFSG.KD.Fi24Alpha.Pc.v1248, CFSG.KD.Fi24Alpha.Pc.v1249, CFSG.KD.Fi24Alpha.Pc.v1250, CFSG.KD.Fi24Alpha.Pc.v1251, CFSG.KD.Fi24Alpha.Pc.v1252, CFSG.KD.Fi24Alpha.Pc.v1253, CFSG.KD.Fi24Alpha.Pc.v1254, CFSG.KD.Fi24Alpha.Pc.v1255]
theorem CFSG.KD.Fi24Alpha.Pc.p1254 : Nat.beq (runC AR SD 1246 (ckL CFSG.KD.Fi24Alpha.Pc.l1256) 2 1254 CFSG.KD.Fi24Alpha.Pc.l1254) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1256 : Nat := CFSG.KD.Fi24Alpha.KV8 116
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1257 : Nat := CFSG.KD.Fi24Alpha.KV8 117
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1258 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1246, CFSG.KD.Fi24Alpha.Pc.v1247, CFSG.KD.Fi24Alpha.Pc.v1248, CFSG.KD.Fi24Alpha.Pc.v1249, CFSG.KD.Fi24Alpha.Pc.v1250, CFSG.KD.Fi24Alpha.Pc.v1251, CFSG.KD.Fi24Alpha.Pc.v1252, CFSG.KD.Fi24Alpha.Pc.v1253, CFSG.KD.Fi24Alpha.Pc.v1254, CFSG.KD.Fi24Alpha.Pc.v1255, CFSG.KD.Fi24Alpha.Pc.v1256, CFSG.KD.Fi24Alpha.Pc.v1257]
theorem CFSG.KD.Fi24Alpha.Pc.p1256 : Nat.beq (runC AR SD 1246 (ckL CFSG.KD.Fi24Alpha.Pc.l1258) 2 1256 CFSG.KD.Fi24Alpha.Pc.l1256) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1258 : Nat := CFSG.KD.Fi24Alpha.KV8 118
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1259 : Nat := CFSG.KD.Fi24Alpha.KV8 119
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1260 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1246, CFSG.KD.Fi24Alpha.Pc.v1247, CFSG.KD.Fi24Alpha.Pc.v1248, CFSG.KD.Fi24Alpha.Pc.v1249, CFSG.KD.Fi24Alpha.Pc.v1250, CFSG.KD.Fi24Alpha.Pc.v1251, CFSG.KD.Fi24Alpha.Pc.v1252, CFSG.KD.Fi24Alpha.Pc.v1253, CFSG.KD.Fi24Alpha.Pc.v1254, CFSG.KD.Fi24Alpha.Pc.v1255, CFSG.KD.Fi24Alpha.Pc.v1256, CFSG.KD.Fi24Alpha.Pc.v1257, CFSG.KD.Fi24Alpha.Pc.v1258, CFSG.KD.Fi24Alpha.Pc.v1259]
theorem CFSG.KD.Fi24Alpha.Pc.p1258 : Nat.beq (runC AR SD 1246 (ckL CFSG.KD.Fi24Alpha.Pc.l1260) 2 1258 CFSG.KD.Fi24Alpha.Pc.l1258) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1260 : Nat := CFSG.KD.Fi24Alpha.KV8 120
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1261 : Nat := CFSG.KD.Fi24Alpha.KV8 121
theorem CFSG.KD.Fi24Alpha.Pc.f87 : Nat.beq (runC AR SD 1246 (finC AR SD (nat_lit 87) 1246 1262) 2 1260 CFSG.KD.Fi24Alpha.Pc.l1260) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk87 : chk (nat_lit 87) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 87) (lo := 1246) (hi := 1262) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1248) CFSG.KD.Fi24Alpha.Pc.p1246 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1250) CFSG.KD.Fi24Alpha.Pc.p1248 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1252) CFSG.KD.Fi24Alpha.Pc.p1250 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1254) CFSG.KD.Fi24Alpha.Pc.p1252 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1256) CFSG.KD.Fi24Alpha.Pc.p1254 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1258) CFSG.KD.Fi24Alpha.Pc.p1256 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1260) CFSG.KD.Fi24Alpha.Pc.p1258 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f87

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1262 : Nat := CFSG.KD.Fi24Alpha.KV8 122
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1263 : Nat := CFSG.KD.Fi24Alpha.KV8 123
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1264 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1262, CFSG.KD.Fi24Alpha.Pc.v1263]
theorem CFSG.KD.Fi24Alpha.Pc.p1262 : Nat.beq (runC AR SD 1262 (ckL CFSG.KD.Fi24Alpha.Pc.l1264) 2 1262 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1264 : Nat := CFSG.KD.Fi24Alpha.KV8 124
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1265 : Nat := CFSG.KD.Fi24Alpha.KV8 125
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1266 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1262, CFSG.KD.Fi24Alpha.Pc.v1263, CFSG.KD.Fi24Alpha.Pc.v1264, CFSG.KD.Fi24Alpha.Pc.v1265]
theorem CFSG.KD.Fi24Alpha.Pc.p1264 : Nat.beq (runC AR SD 1262 (ckL CFSG.KD.Fi24Alpha.Pc.l1266) 2 1264 CFSG.KD.Fi24Alpha.Pc.l1264) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1266 : Nat := CFSG.KD.Fi24Alpha.KV8 126
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1267 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1262, CFSG.KD.Fi24Alpha.Pc.v1263, CFSG.KD.Fi24Alpha.Pc.v1264, CFSG.KD.Fi24Alpha.Pc.v1265, CFSG.KD.Fi24Alpha.Pc.v1266]
theorem CFSG.KD.Fi24Alpha.Pc.p1266 : Nat.beq (runC AR SD 1262 (ckL CFSG.KD.Fi24Alpha.Pc.l1267) 1 1266 CFSG.KD.Fi24Alpha.Pc.l1266) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1267 : Nat := CFSG.KD.Fi24Alpha.KV8 127
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1268 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1262, CFSG.KD.Fi24Alpha.Pc.v1263, CFSG.KD.Fi24Alpha.Pc.v1264, CFSG.KD.Fi24Alpha.Pc.v1265, CFSG.KD.Fi24Alpha.Pc.v1266, CFSG.KD.Fi24Alpha.Pc.v1267]
theorem CFSG.KD.Fi24Alpha.Pc.p1267 : Nat.beq (runC AR SD 1262 (ckL CFSG.KD.Fi24Alpha.Pc.l1268) 1 1267 CFSG.KD.Fi24Alpha.Pc.l1267) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1268 : Nat := CFSG.KD.Fi24Alpha.KV8 128
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1269 : Nat := CFSG.KD.Fi24Alpha.KV8 129
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1270 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1262, CFSG.KD.Fi24Alpha.Pc.v1263, CFSG.KD.Fi24Alpha.Pc.v1264, CFSG.KD.Fi24Alpha.Pc.v1265, CFSG.KD.Fi24Alpha.Pc.v1266, CFSG.KD.Fi24Alpha.Pc.v1267, CFSG.KD.Fi24Alpha.Pc.v1268, CFSG.KD.Fi24Alpha.Pc.v1269]
theorem CFSG.KD.Fi24Alpha.Pc.p1268 : Nat.beq (runC AR SD 1262 (ckL CFSG.KD.Fi24Alpha.Pc.l1270) 2 1268 CFSG.KD.Fi24Alpha.Pc.l1268) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1270 : Nat := CFSG.KD.Fi24Alpha.KV8 130
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1271 : Nat := CFSG.KD.Fi24Alpha.KV8 131
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1272 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1262, CFSG.KD.Fi24Alpha.Pc.v1263, CFSG.KD.Fi24Alpha.Pc.v1264, CFSG.KD.Fi24Alpha.Pc.v1265, CFSG.KD.Fi24Alpha.Pc.v1266, CFSG.KD.Fi24Alpha.Pc.v1267, CFSG.KD.Fi24Alpha.Pc.v1268, CFSG.KD.Fi24Alpha.Pc.v1269, CFSG.KD.Fi24Alpha.Pc.v1270, CFSG.KD.Fi24Alpha.Pc.v1271]
theorem CFSG.KD.Fi24Alpha.Pc.p1270 : Nat.beq (runC AR SD 1262 (ckL CFSG.KD.Fi24Alpha.Pc.l1272) 2 1270 CFSG.KD.Fi24Alpha.Pc.l1270) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1272 : Nat := CFSG.KD.Fi24Alpha.KV8 132
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1273 : Nat := CFSG.KD.Fi24Alpha.KV8 133
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1274 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1262, CFSG.KD.Fi24Alpha.Pc.v1263, CFSG.KD.Fi24Alpha.Pc.v1264, CFSG.KD.Fi24Alpha.Pc.v1265, CFSG.KD.Fi24Alpha.Pc.v1266, CFSG.KD.Fi24Alpha.Pc.v1267, CFSG.KD.Fi24Alpha.Pc.v1268, CFSG.KD.Fi24Alpha.Pc.v1269, CFSG.KD.Fi24Alpha.Pc.v1270, CFSG.KD.Fi24Alpha.Pc.v1271, CFSG.KD.Fi24Alpha.Pc.v1272, CFSG.KD.Fi24Alpha.Pc.v1273]
theorem CFSG.KD.Fi24Alpha.Pc.p1272 : Nat.beq (runC AR SD 1262 (ckL CFSG.KD.Fi24Alpha.Pc.l1274) 2 1272 CFSG.KD.Fi24Alpha.Pc.l1272) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1274 : Nat := CFSG.KD.Fi24Alpha.KV8 134
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1275 : Nat := CFSG.KD.Fi24Alpha.KV8 135
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1276 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1262, CFSG.KD.Fi24Alpha.Pc.v1263, CFSG.KD.Fi24Alpha.Pc.v1264, CFSG.KD.Fi24Alpha.Pc.v1265, CFSG.KD.Fi24Alpha.Pc.v1266, CFSG.KD.Fi24Alpha.Pc.v1267, CFSG.KD.Fi24Alpha.Pc.v1268, CFSG.KD.Fi24Alpha.Pc.v1269, CFSG.KD.Fi24Alpha.Pc.v1270, CFSG.KD.Fi24Alpha.Pc.v1271, CFSG.KD.Fi24Alpha.Pc.v1272, CFSG.KD.Fi24Alpha.Pc.v1273, CFSG.KD.Fi24Alpha.Pc.v1274, CFSG.KD.Fi24Alpha.Pc.v1275]
theorem CFSG.KD.Fi24Alpha.Pc.p1274 : Nat.beq (runC AR SD 1262 (ckL CFSG.KD.Fi24Alpha.Pc.l1276) 2 1274 CFSG.KD.Fi24Alpha.Pc.l1274) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1276 : Nat := CFSG.KD.Fi24Alpha.KV8 136
theorem CFSG.KD.Fi24Alpha.Pc.f88 : Nat.beq (runC AR SD 1262 (finC AR SD (nat_lit 88) 1262 1277) 1 1276 CFSG.KD.Fi24Alpha.Pc.l1276) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk88 : chk (nat_lit 88) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 88) (lo := 1262) (hi := 1277) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 1264) CFSG.KD.Fi24Alpha.Pc.p1262 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 1266) CFSG.KD.Fi24Alpha.Pc.p1264 rfl rfl).trans ((runC_seq (m := 11) (m2 := 10) (j2 := 1267) CFSG.KD.Fi24Alpha.Pc.p1266 rfl rfl).trans ((runC_seq (m := 10) (m2 := 9) (j2 := 1268) CFSG.KD.Fi24Alpha.Pc.p1267 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 1270) CFSG.KD.Fi24Alpha.Pc.p1268 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 1272) CFSG.KD.Fi24Alpha.Pc.p1270 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 1274) CFSG.KD.Fi24Alpha.Pc.p1272 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 1276) CFSG.KD.Fi24Alpha.Pc.p1274 rfl rfl)))))))))).trans CFSG.KD.Fi24Alpha.Pc.f88

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1277 : Nat := CFSG.KD.Fi24Alpha.KV8 137
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1278 : Nat := CFSG.KD.Fi24Alpha.KV8 138
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1279 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1277, CFSG.KD.Fi24Alpha.Pc.v1278]
theorem CFSG.KD.Fi24Alpha.Pc.p1277 : Nat.beq (runC AR SD 1277 (ckL CFSG.KD.Fi24Alpha.Pc.l1279) 2 1277 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1279 : Nat := CFSG.KD.Fi24Alpha.KV8 139
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1280 : Nat := CFSG.KD.Fi24Alpha.KV8 140
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1281 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1277, CFSG.KD.Fi24Alpha.Pc.v1278, CFSG.KD.Fi24Alpha.Pc.v1279, CFSG.KD.Fi24Alpha.Pc.v1280]
theorem CFSG.KD.Fi24Alpha.Pc.p1279 : Nat.beq (runC AR SD 1277 (ckL CFSG.KD.Fi24Alpha.Pc.l1281) 2 1279 CFSG.KD.Fi24Alpha.Pc.l1279) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1281 : Nat := CFSG.KD.Fi24Alpha.KV8 141
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1282 : Nat := CFSG.KD.Fi24Alpha.KV8 142
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1283 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1277, CFSG.KD.Fi24Alpha.Pc.v1278, CFSG.KD.Fi24Alpha.Pc.v1279, CFSG.KD.Fi24Alpha.Pc.v1280, CFSG.KD.Fi24Alpha.Pc.v1281, CFSG.KD.Fi24Alpha.Pc.v1282]
theorem CFSG.KD.Fi24Alpha.Pc.p1281 : Nat.beq (runC AR SD 1277 (ckL CFSG.KD.Fi24Alpha.Pc.l1283) 2 1281 CFSG.KD.Fi24Alpha.Pc.l1281) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1283 : Nat := CFSG.KD.Fi24Alpha.KV8 143
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1284 : Nat := CFSG.KD.Fi24Alpha.KV8 144
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1285 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1277, CFSG.KD.Fi24Alpha.Pc.v1278, CFSG.KD.Fi24Alpha.Pc.v1279, CFSG.KD.Fi24Alpha.Pc.v1280, CFSG.KD.Fi24Alpha.Pc.v1281, CFSG.KD.Fi24Alpha.Pc.v1282, CFSG.KD.Fi24Alpha.Pc.v1283, CFSG.KD.Fi24Alpha.Pc.v1284]
theorem CFSG.KD.Fi24Alpha.Pc.p1283 : Nat.beq (runC AR SD 1277 (ckL CFSG.KD.Fi24Alpha.Pc.l1285) 2 1283 CFSG.KD.Fi24Alpha.Pc.l1283) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1285 : Nat := CFSG.KD.Fi24Alpha.KV8 145
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1286 : Nat := CFSG.KD.Fi24Alpha.KV8 146
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1287 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1277, CFSG.KD.Fi24Alpha.Pc.v1278, CFSG.KD.Fi24Alpha.Pc.v1279, CFSG.KD.Fi24Alpha.Pc.v1280, CFSG.KD.Fi24Alpha.Pc.v1281, CFSG.KD.Fi24Alpha.Pc.v1282, CFSG.KD.Fi24Alpha.Pc.v1283, CFSG.KD.Fi24Alpha.Pc.v1284, CFSG.KD.Fi24Alpha.Pc.v1285, CFSG.KD.Fi24Alpha.Pc.v1286]
theorem CFSG.KD.Fi24Alpha.Pc.p1285 : Nat.beq (runC AR SD 1277 (ckL CFSG.KD.Fi24Alpha.Pc.l1287) 2 1285 CFSG.KD.Fi24Alpha.Pc.l1285) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1287 : Nat := CFSG.KD.Fi24Alpha.KV8 147
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1288 : Nat := CFSG.KD.Fi24Alpha.KV8 148
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1289 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1277, CFSG.KD.Fi24Alpha.Pc.v1278, CFSG.KD.Fi24Alpha.Pc.v1279, CFSG.KD.Fi24Alpha.Pc.v1280, CFSG.KD.Fi24Alpha.Pc.v1281, CFSG.KD.Fi24Alpha.Pc.v1282, CFSG.KD.Fi24Alpha.Pc.v1283, CFSG.KD.Fi24Alpha.Pc.v1284, CFSG.KD.Fi24Alpha.Pc.v1285, CFSG.KD.Fi24Alpha.Pc.v1286, CFSG.KD.Fi24Alpha.Pc.v1287, CFSG.KD.Fi24Alpha.Pc.v1288]
theorem CFSG.KD.Fi24Alpha.Pc.p1287 : Nat.beq (runC AR SD 1277 (ckL CFSG.KD.Fi24Alpha.Pc.l1289) 2 1287 CFSG.KD.Fi24Alpha.Pc.l1287) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1289 : Nat := CFSG.KD.Fi24Alpha.KV8 149
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1290 : Nat := CFSG.KD.Fi24Alpha.KV8 150
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1291 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1277, CFSG.KD.Fi24Alpha.Pc.v1278, CFSG.KD.Fi24Alpha.Pc.v1279, CFSG.KD.Fi24Alpha.Pc.v1280, CFSG.KD.Fi24Alpha.Pc.v1281, CFSG.KD.Fi24Alpha.Pc.v1282, CFSG.KD.Fi24Alpha.Pc.v1283, CFSG.KD.Fi24Alpha.Pc.v1284, CFSG.KD.Fi24Alpha.Pc.v1285, CFSG.KD.Fi24Alpha.Pc.v1286, CFSG.KD.Fi24Alpha.Pc.v1287, CFSG.KD.Fi24Alpha.Pc.v1288, CFSG.KD.Fi24Alpha.Pc.v1289, CFSG.KD.Fi24Alpha.Pc.v1290]
theorem CFSG.KD.Fi24Alpha.Pc.p1289 : Nat.beq (runC AR SD 1277 (ckL CFSG.KD.Fi24Alpha.Pc.l1291) 2 1289 CFSG.KD.Fi24Alpha.Pc.l1289) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1291 : Nat := CFSG.KD.Fi24Alpha.KV8 151
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1292 : Nat := CFSG.KD.Fi24Alpha.KV8 152
theorem CFSG.KD.Fi24Alpha.Pc.f89 : Nat.beq (runC AR SD 1277 (finC AR SD (nat_lit 89) 1277 1293) 2 1291 CFSG.KD.Fi24Alpha.Pc.l1291) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk89 : chk (nat_lit 89) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 89) (lo := 1277) (hi := 1293) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1279) CFSG.KD.Fi24Alpha.Pc.p1277 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1281) CFSG.KD.Fi24Alpha.Pc.p1279 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1283) CFSG.KD.Fi24Alpha.Pc.p1281 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1285) CFSG.KD.Fi24Alpha.Pc.p1283 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1287) CFSG.KD.Fi24Alpha.Pc.p1285 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1289) CFSG.KD.Fi24Alpha.Pc.p1287 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1291) CFSG.KD.Fi24Alpha.Pc.p1289 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f89

end
