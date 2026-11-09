module

public import Certificates.Kernel.Sporadic.Fi24Tc.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Tc KV9 "Certificates/Kernel/Sporadic/Fi24Tc/data/v9.bin" 152491 4 16926501 15356161068199893741

public section

open CFSG.KD.Fi24Tc CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1250 : Nat := CFSG.KD.Fi24Tc.KV9 0
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1251 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1250]
theorem CFSG.KD.Fi24Tc.Pc.p1250 : Nat.beq (runC AR SD 1250 (ckL CFSG.KD.Fi24Tc.Pc.l1251) 1 1250 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1251 : Nat := CFSG.KD.Fi24Tc.KV9 1
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1252 : Nat := CFSG.KD.Fi24Tc.KV9 2
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1253 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1250, CFSG.KD.Fi24Tc.Pc.v1251, CFSG.KD.Fi24Tc.Pc.v1252]
theorem CFSG.KD.Fi24Tc.Pc.p1251 : Nat.beq (runC AR SD 1250 (ckL CFSG.KD.Fi24Tc.Pc.l1253) 2 1251 CFSG.KD.Fi24Tc.Pc.l1251) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1253 : Nat := CFSG.KD.Fi24Tc.KV9 3
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1254 : Nat := CFSG.KD.Fi24Tc.KV9 4
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1255 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1250, CFSG.KD.Fi24Tc.Pc.v1251, CFSG.KD.Fi24Tc.Pc.v1252, CFSG.KD.Fi24Tc.Pc.v1253, CFSG.KD.Fi24Tc.Pc.v1254]
theorem CFSG.KD.Fi24Tc.Pc.p1253 : Nat.beq (runC AR SD 1250 (ckL CFSG.KD.Fi24Tc.Pc.l1255) 2 1253 CFSG.KD.Fi24Tc.Pc.l1253) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f180 : Nat.beq (runC AR SD 1250 (finC AR SD (nat_lit 180) 1250 1256) 1 1255 CFSG.KD.Fi24Tc.Pc.l1255) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk180 : chk (nat_lit 180) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 180) (lo := 1250) (hi := 1256) (m := 6) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 6) (m2 := 5) (j2 := 1251) CFSG.KD.Fi24Tc.Pc.p1250 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 1253) CFSG.KD.Fi24Tc.Pc.p1251 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 1255) CFSG.KD.Fi24Tc.Pc.p1253 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f180

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1256 : Nat := CFSG.KD.Fi24Tc.KV9 5
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1257 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1256]
theorem CFSG.KD.Fi24Tc.Pc.p1256 : Nat.beq (runC AR SD 1256 (ckL CFSG.KD.Fi24Tc.Pc.l1257) 1 1256 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1257 : Nat := CFSG.KD.Fi24Tc.KV9 6
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1258 : Nat := CFSG.KD.Fi24Tc.KV9 7
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1259 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1256, CFSG.KD.Fi24Tc.Pc.v1257, CFSG.KD.Fi24Tc.Pc.v1258]
theorem CFSG.KD.Fi24Tc.Pc.p1257 : Nat.beq (runC AR SD 1256 (ckL CFSG.KD.Fi24Tc.Pc.l1259) 2 1257 CFSG.KD.Fi24Tc.Pc.l1257) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1259 : Nat := CFSG.KD.Fi24Tc.KV9 8
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1260 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1256, CFSG.KD.Fi24Tc.Pc.v1257, CFSG.KD.Fi24Tc.Pc.v1258, CFSG.KD.Fi24Tc.Pc.v1259]
theorem CFSG.KD.Fi24Tc.Pc.p1259 : Nat.beq (runC AR SD 1256 (ckL CFSG.KD.Fi24Tc.Pc.l1260) 1 1259 CFSG.KD.Fi24Tc.Pc.l1259) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1260 : Nat := CFSG.KD.Fi24Tc.KV9 9
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1261 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1256, CFSG.KD.Fi24Tc.Pc.v1257, CFSG.KD.Fi24Tc.Pc.v1258, CFSG.KD.Fi24Tc.Pc.v1259, CFSG.KD.Fi24Tc.Pc.v1260]
theorem CFSG.KD.Fi24Tc.Pc.p1260 : Nat.beq (runC AR SD 1256 (ckL CFSG.KD.Fi24Tc.Pc.l1261) 1 1260 CFSG.KD.Fi24Tc.Pc.l1260) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f181 : Nat.beq (runC AR SD 1256 (finC AR SD (nat_lit 181) 1256 1262) 1 1261 CFSG.KD.Fi24Tc.Pc.l1261) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk181 : chk (nat_lit 181) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 181) (lo := 1256) (hi := 1262) (m := 6) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 6) (m2 := 5) (j2 := 1257) CFSG.KD.Fi24Tc.Pc.p1256 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 1259) CFSG.KD.Fi24Tc.Pc.p1257 rfl rfl).trans ((runC_seq (m := 3) (m2 := 2) (j2 := 1260) CFSG.KD.Fi24Tc.Pc.p1259 rfl rfl).trans (runC_seq (m := 2) (m2 := 1) (j2 := 1261) CFSG.KD.Fi24Tc.Pc.p1260 rfl rfl)))))).trans CFSG.KD.Fi24Tc.Pc.f181

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1262 : Nat := CFSG.KD.Fi24Tc.KV9 10
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1263 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1262]
theorem CFSG.KD.Fi24Tc.Pc.p1262 : Nat.beq (runC AR SD 1262 (ckL CFSG.KD.Fi24Tc.Pc.l1263) 1 1262 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1263 : Nat := CFSG.KD.Fi24Tc.KV9 11
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1264 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1262, CFSG.KD.Fi24Tc.Pc.v1263]
theorem CFSG.KD.Fi24Tc.Pc.p1263 : Nat.beq (runC AR SD 1262 (ckL CFSG.KD.Fi24Tc.Pc.l1264) 1 1263 CFSG.KD.Fi24Tc.Pc.l1263) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1264 : Nat := CFSG.KD.Fi24Tc.KV9 12
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1265 : Nat := CFSG.KD.Fi24Tc.KV9 13
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1266 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1262, CFSG.KD.Fi24Tc.Pc.v1263, CFSG.KD.Fi24Tc.Pc.v1264, CFSG.KD.Fi24Tc.Pc.v1265]
theorem CFSG.KD.Fi24Tc.Pc.p1264 : Nat.beq (runC AR SD 1262 (ckL CFSG.KD.Fi24Tc.Pc.l1266) 2 1264 CFSG.KD.Fi24Tc.Pc.l1264) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f182 : Nat.beq (runC AR SD 1262 (finC AR SD (nat_lit 182) 1262 1268) 2 1266 CFSG.KD.Fi24Tc.Pc.l1266) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk182 : chk (nat_lit 182) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 182) (lo := 1262) (hi := 1268) (m := 6) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 6) (m2 := 5) (j2 := 1263) CFSG.KD.Fi24Tc.Pc.p1262 rfl rfl).trans ((runC_seq (m := 5) (m2 := 4) (j2 := 1264) CFSG.KD.Fi24Tc.Pc.p1263 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1266) CFSG.KD.Fi24Tc.Pc.p1264 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f182

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1268 : Nat := CFSG.KD.Fi24Tc.KV9 14
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1269 : Nat := CFSG.KD.Fi24Tc.KV9 15
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1270 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1268, CFSG.KD.Fi24Tc.Pc.v1269]
theorem CFSG.KD.Fi24Tc.Pc.p1268 : Nat.beq (runC AR SD 1268 (ckL CFSG.KD.Fi24Tc.Pc.l1270) 2 1268 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1270 : Nat := CFSG.KD.Fi24Tc.KV9 16
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1271 : Nat := CFSG.KD.Fi24Tc.KV9 17
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1272 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1268, CFSG.KD.Fi24Tc.Pc.v1269, CFSG.KD.Fi24Tc.Pc.v1270, CFSG.KD.Fi24Tc.Pc.v1271]
theorem CFSG.KD.Fi24Tc.Pc.p1270 : Nat.beq (runC AR SD 1268 (ckL CFSG.KD.Fi24Tc.Pc.l1272) 2 1270 CFSG.KD.Fi24Tc.Pc.l1270) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1272 : Nat := CFSG.KD.Fi24Tc.KV9 18
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1273 : Nat := CFSG.KD.Fi24Tc.KV9 19
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1274 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1268, CFSG.KD.Fi24Tc.Pc.v1269, CFSG.KD.Fi24Tc.Pc.v1270, CFSG.KD.Fi24Tc.Pc.v1271, CFSG.KD.Fi24Tc.Pc.v1272, CFSG.KD.Fi24Tc.Pc.v1273]
theorem CFSG.KD.Fi24Tc.Pc.p1272 : Nat.beq (runC AR SD 1268 (ckL CFSG.KD.Fi24Tc.Pc.l1274) 2 1272 CFSG.KD.Fi24Tc.Pc.l1272) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f183 : Nat.beq (runC AR SD 1268 (finC AR SD (nat_lit 183) 1268 1276) 2 1274 CFSG.KD.Fi24Tc.Pc.l1274) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk183 : chk (nat_lit 183) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 183) (lo := 1268) (hi := 1276) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1270) CFSG.KD.Fi24Tc.Pc.p1268 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1272) CFSG.KD.Fi24Tc.Pc.p1270 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1274) CFSG.KD.Fi24Tc.Pc.p1272 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f183

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1276 : Nat := CFSG.KD.Fi24Tc.KV9 95
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1277 : Nat := CFSG.KD.Fi24Tc.KV9 96
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1278 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1276, CFSG.KD.Fi24Tc.Pc.v1277]
theorem CFSG.KD.Fi24Tc.Pc.p1276 : Nat.beq (runC AR SD 1276 (ckL CFSG.KD.Fi24Tc.Pc.l1278) 2 1276 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1278 : Nat := CFSG.KD.Fi24Tc.KV9 97
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1279 : Nat := CFSG.KD.Fi24Tc.KV9 98
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1280 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1276, CFSG.KD.Fi24Tc.Pc.v1277, CFSG.KD.Fi24Tc.Pc.v1278, CFSG.KD.Fi24Tc.Pc.v1279]
theorem CFSG.KD.Fi24Tc.Pc.p1278 : Nat.beq (runC AR SD 1276 (ckL CFSG.KD.Fi24Tc.Pc.l1280) 2 1278 CFSG.KD.Fi24Tc.Pc.l1278) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1280 : Nat := CFSG.KD.Fi24Tc.KV9 99
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1281 : Nat := CFSG.KD.Fi24Tc.KV9 100
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1282 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1276, CFSG.KD.Fi24Tc.Pc.v1277, CFSG.KD.Fi24Tc.Pc.v1278, CFSG.KD.Fi24Tc.Pc.v1279, CFSG.KD.Fi24Tc.Pc.v1280, CFSG.KD.Fi24Tc.Pc.v1281]
theorem CFSG.KD.Fi24Tc.Pc.p1280 : Nat.beq (runC AR SD 1276 (ckL CFSG.KD.Fi24Tc.Pc.l1282) 2 1280 CFSG.KD.Fi24Tc.Pc.l1280) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f184 : Nat.beq (runC AR SD 1276 (finC AR SD (nat_lit 184) 1276 1284) 2 1282 CFSG.KD.Fi24Tc.Pc.l1282) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk184 : chk (nat_lit 184) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 184) (lo := 1276) (hi := 1284) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1278) CFSG.KD.Fi24Tc.Pc.p1276 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1280) CFSG.KD.Fi24Tc.Pc.p1278 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1282) CFSG.KD.Fi24Tc.Pc.p1280 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f184

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1284 : Nat := CFSG.KD.Fi24Tc.KV9 101
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1285 : Nat := CFSG.KD.Fi24Tc.KV9 102
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1286 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1284, CFSG.KD.Fi24Tc.Pc.v1285]
theorem CFSG.KD.Fi24Tc.Pc.p1284 : Nat.beq (runC AR SD 1284 (ckL CFSG.KD.Fi24Tc.Pc.l1286) 2 1284 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1286 : Nat := CFSG.KD.Fi24Tc.KV9 103
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1287 : Nat := CFSG.KD.Fi24Tc.KV9 104
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1288 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1284, CFSG.KD.Fi24Tc.Pc.v1285, CFSG.KD.Fi24Tc.Pc.v1286, CFSG.KD.Fi24Tc.Pc.v1287]
theorem CFSG.KD.Fi24Tc.Pc.p1286 : Nat.beq (runC AR SD 1284 (ckL CFSG.KD.Fi24Tc.Pc.l1288) 2 1286 CFSG.KD.Fi24Tc.Pc.l1286) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1288 : Nat := CFSG.KD.Fi24Tc.KV9 105
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1289 : Nat := CFSG.KD.Fi24Tc.KV9 106
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1290 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1284, CFSG.KD.Fi24Tc.Pc.v1285, CFSG.KD.Fi24Tc.Pc.v1286, CFSG.KD.Fi24Tc.Pc.v1287, CFSG.KD.Fi24Tc.Pc.v1288, CFSG.KD.Fi24Tc.Pc.v1289]
theorem CFSG.KD.Fi24Tc.Pc.p1288 : Nat.beq (runC AR SD 1284 (ckL CFSG.KD.Fi24Tc.Pc.l1290) 2 1288 CFSG.KD.Fi24Tc.Pc.l1288) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f185 : Nat.beq (runC AR SD 1284 (finC AR SD (nat_lit 185) 1284 1292) 2 1290 CFSG.KD.Fi24Tc.Pc.l1290) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk185 : chk (nat_lit 185) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 185) (lo := 1284) (hi := 1292) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1286) CFSG.KD.Fi24Tc.Pc.p1284 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1288) CFSG.KD.Fi24Tc.Pc.p1286 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1290) CFSG.KD.Fi24Tc.Pc.p1288 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f185

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1292 : Nat := CFSG.KD.Fi24Tc.KV9 20
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1293 : Nat := CFSG.KD.Fi24Tc.KV9 21
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1294 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1292, CFSG.KD.Fi24Tc.Pc.v1293]
theorem CFSG.KD.Fi24Tc.Pc.p1292 : Nat.beq (runC AR SD 1292 (ckL CFSG.KD.Fi24Tc.Pc.l1294) 2 1292 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1294 : Nat := CFSG.KD.Fi24Tc.KV9 22
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1295 : Nat := CFSG.KD.Fi24Tc.KV9 23
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1296 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1292, CFSG.KD.Fi24Tc.Pc.v1293, CFSG.KD.Fi24Tc.Pc.v1294, CFSG.KD.Fi24Tc.Pc.v1295]
theorem CFSG.KD.Fi24Tc.Pc.p1294 : Nat.beq (runC AR SD 1292 (ckL CFSG.KD.Fi24Tc.Pc.l1296) 2 1294 CFSG.KD.Fi24Tc.Pc.l1294) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1296 : Nat := CFSG.KD.Fi24Tc.KV9 24
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1297 : Nat := CFSG.KD.Fi24Tc.KV9 25
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1298 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1292, CFSG.KD.Fi24Tc.Pc.v1293, CFSG.KD.Fi24Tc.Pc.v1294, CFSG.KD.Fi24Tc.Pc.v1295, CFSG.KD.Fi24Tc.Pc.v1296, CFSG.KD.Fi24Tc.Pc.v1297]
theorem CFSG.KD.Fi24Tc.Pc.p1296 : Nat.beq (runC AR SD 1292 (ckL CFSG.KD.Fi24Tc.Pc.l1298) 2 1296 CFSG.KD.Fi24Tc.Pc.l1296) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f186 : Nat.beq (runC AR SD 1292 (finC AR SD (nat_lit 186) 1292 1300) 2 1298 CFSG.KD.Fi24Tc.Pc.l1298) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk186 : chk (nat_lit 186) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 186) (lo := 1292) (hi := 1300) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1294) CFSG.KD.Fi24Tc.Pc.p1292 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1296) CFSG.KD.Fi24Tc.Pc.p1294 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1298) CFSG.KD.Fi24Tc.Pc.p1296 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f186

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1300 : Nat := CFSG.KD.Fi24Tc.KV9 26
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1301 : Nat := CFSG.KD.Fi24Tc.KV9 27
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1302 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1300, CFSG.KD.Fi24Tc.Pc.v1301]
theorem CFSG.KD.Fi24Tc.Pc.p1300 : Nat.beq (runC AR SD 1300 (ckL CFSG.KD.Fi24Tc.Pc.l1302) 2 1300 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1302 : Nat := CFSG.KD.Fi24Tc.KV9 28
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1303 : Nat := CFSG.KD.Fi24Tc.KV9 29
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1304 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1300, CFSG.KD.Fi24Tc.Pc.v1301, CFSG.KD.Fi24Tc.Pc.v1302, CFSG.KD.Fi24Tc.Pc.v1303]
theorem CFSG.KD.Fi24Tc.Pc.p1302 : Nat.beq (runC AR SD 1300 (ckL CFSG.KD.Fi24Tc.Pc.l1304) 2 1302 CFSG.KD.Fi24Tc.Pc.l1302) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1304 : Nat := CFSG.KD.Fi24Tc.KV9 30
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1305 : Nat := CFSG.KD.Fi24Tc.KV9 31
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1306 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1300, CFSG.KD.Fi24Tc.Pc.v1301, CFSG.KD.Fi24Tc.Pc.v1302, CFSG.KD.Fi24Tc.Pc.v1303, CFSG.KD.Fi24Tc.Pc.v1304, CFSG.KD.Fi24Tc.Pc.v1305]
theorem CFSG.KD.Fi24Tc.Pc.p1304 : Nat.beq (runC AR SD 1300 (ckL CFSG.KD.Fi24Tc.Pc.l1306) 2 1304 CFSG.KD.Fi24Tc.Pc.l1304) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f187 : Nat.beq (runC AR SD 1300 (finC AR SD (nat_lit 187) 1300 1308) 2 1306 CFSG.KD.Fi24Tc.Pc.l1306) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk187 : chk (nat_lit 187) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 187) (lo := 1300) (hi := 1308) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1302) CFSG.KD.Fi24Tc.Pc.p1300 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1304) CFSG.KD.Fi24Tc.Pc.p1302 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1306) CFSG.KD.Fi24Tc.Pc.p1304 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f187

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1308 : Nat := CFSG.KD.Fi24Tc.KV9 107
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1309 : Nat := CFSG.KD.Fi24Tc.KV9 108
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1310 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1308, CFSG.KD.Fi24Tc.Pc.v1309]
theorem CFSG.KD.Fi24Tc.Pc.p1308 : Nat.beq (runC AR SD 1308 (ckL CFSG.KD.Fi24Tc.Pc.l1310) 2 1308 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1310 : Nat := CFSG.KD.Fi24Tc.KV9 109
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1311 : Nat := CFSG.KD.Fi24Tc.KV9 110
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1312 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1308, CFSG.KD.Fi24Tc.Pc.v1309, CFSG.KD.Fi24Tc.Pc.v1310, CFSG.KD.Fi24Tc.Pc.v1311]
theorem CFSG.KD.Fi24Tc.Pc.p1310 : Nat.beq (runC AR SD 1308 (ckL CFSG.KD.Fi24Tc.Pc.l1312) 2 1310 CFSG.KD.Fi24Tc.Pc.l1310) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f188 : Nat.beq (runC AR SD 1308 (finC AR SD (nat_lit 188) 1308 1313) 1 1312 CFSG.KD.Fi24Tc.Pc.l1312) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk188 : chk (nat_lit 188) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 188) (lo := 1308) (hi := 1313) (m := 5) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 5) (m2 := 3) (j2 := 1310) CFSG.KD.Fi24Tc.Pc.p1308 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 1312) CFSG.KD.Fi24Tc.Pc.p1310 rfl rfl)))).trans CFSG.KD.Fi24Tc.Pc.f188

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1313_3 : Nat := CFSG.KD.Fi24Tc.KV9 32
theorem CFSG.KD.Fi24Tc.Pc.q1313_3 : Nat.beq (powTop AR.mul (getV AR SD 1313 [] (SD.na.getD 1313 0)) (SD.nk.getD 1313 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a1313_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a1313_2 : Nat := CFSG.KD.Fi24Tc.KV9 33
theorem CFSG.KD.Fi24Tc.Pc.q1313_2 : Nat.beq (powTop AR.mul (getV AR SD 1313 [] (SD.na.getD 1313 0)) (SD.nk.getD 1313 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a1313_2) 1 CFSG.KD.Fi24Tc.Pc.a1313_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1313 : Nat := CFSG.KD.Fi24Tc.KV9 34
theorem CFSG.KD.Fi24Tc.Pc.r1313 : Nat.beq (powR AR.mul AR.one (getV AR SD 1313 [] (SD.na.getD 1313 0)) (SD.nk.getD 1313 1) 2 CFSG.KD.Fi24Tc.Pc.a1313_2 true) CFSG.KD.Fi24Tc.Pc.v1313 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1314 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1313]
theorem CFSG.KD.Fi24Tc.Pc.f189 : Nat.beq (runC AR SD 1313 (finC AR SD (nat_lit 189) 1313 1316) 2 1314 CFSG.KD.Fi24Tc.Pc.l1314) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk189 : chk (nat_lit 189) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 189) (lo := 1313) (hi := 1316) (m := 3) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 3) (m2 := 2) (j2 := 1314) (Lr := CFSG.KD.Fi24Tc.Pc.l1314) ((nodeV_pow (R := AR) (D := SD) (lo := 1313) (L := []) (j := 1313) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 1313 [] (SD.na.getD 1313 0)) (SD.nk.getD 1313 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q1313_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q1313_2 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r1313))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f189

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1316 : Nat := CFSG.KD.Fi24Tc.KV9 35
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1317 : Nat := CFSG.KD.Fi24Tc.KV9 36
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1318 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1316, CFSG.KD.Fi24Tc.Pc.v1317]
theorem CFSG.KD.Fi24Tc.Pc.p1316 : Nat.beq (runC AR SD 1316 (ckL CFSG.KD.Fi24Tc.Pc.l1318) 2 1316 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1318 : Nat := CFSG.KD.Fi24Tc.KV9 37
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1319 : Nat := CFSG.KD.Fi24Tc.KV9 38
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1320 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1316, CFSG.KD.Fi24Tc.Pc.v1317, CFSG.KD.Fi24Tc.Pc.v1318, CFSG.KD.Fi24Tc.Pc.v1319]
theorem CFSG.KD.Fi24Tc.Pc.p1318 : Nat.beq (runC AR SD 1316 (ckL CFSG.KD.Fi24Tc.Pc.l1320) 2 1318 CFSG.KD.Fi24Tc.Pc.l1318) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1320 : Nat := CFSG.KD.Fi24Tc.KV9 39
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1321 : Nat := CFSG.KD.Fi24Tc.KV9 40
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1322 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1316, CFSG.KD.Fi24Tc.Pc.v1317, CFSG.KD.Fi24Tc.Pc.v1318, CFSG.KD.Fi24Tc.Pc.v1319, CFSG.KD.Fi24Tc.Pc.v1320, CFSG.KD.Fi24Tc.Pc.v1321]
theorem CFSG.KD.Fi24Tc.Pc.p1320 : Nat.beq (runC AR SD 1316 (ckL CFSG.KD.Fi24Tc.Pc.l1322) 2 1320 CFSG.KD.Fi24Tc.Pc.l1320) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f190 : Nat.beq (runC AR SD 1316 (finC AR SD (nat_lit 190) 1316 1324) 2 1322 CFSG.KD.Fi24Tc.Pc.l1322) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk190 : chk (nat_lit 190) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 190) (lo := 1316) (hi := 1324) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1318) CFSG.KD.Fi24Tc.Pc.p1316 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1320) CFSG.KD.Fi24Tc.Pc.p1318 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1322) CFSG.KD.Fi24Tc.Pc.p1320 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f190

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1324 : Nat := CFSG.KD.Fi24Tc.KV9 41
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1325 : Nat := CFSG.KD.Fi24Tc.KV9 42
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1326 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1324, CFSG.KD.Fi24Tc.Pc.v1325]
theorem CFSG.KD.Fi24Tc.Pc.p1324 : Nat.beq (runC AR SD 1324 (ckL CFSG.KD.Fi24Tc.Pc.l1326) 2 1324 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1326 : Nat := CFSG.KD.Fi24Tc.KV9 43
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1327 : Nat := CFSG.KD.Fi24Tc.KV9 44
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1328 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1324, CFSG.KD.Fi24Tc.Pc.v1325, CFSG.KD.Fi24Tc.Pc.v1326, CFSG.KD.Fi24Tc.Pc.v1327]
theorem CFSG.KD.Fi24Tc.Pc.p1326 : Nat.beq (runC AR SD 1324 (ckL CFSG.KD.Fi24Tc.Pc.l1328) 2 1326 CFSG.KD.Fi24Tc.Pc.l1326) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1328 : Nat := CFSG.KD.Fi24Tc.KV9 45
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1329 : Nat := CFSG.KD.Fi24Tc.KV9 46
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1330 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1324, CFSG.KD.Fi24Tc.Pc.v1325, CFSG.KD.Fi24Tc.Pc.v1326, CFSG.KD.Fi24Tc.Pc.v1327, CFSG.KD.Fi24Tc.Pc.v1328, CFSG.KD.Fi24Tc.Pc.v1329]
theorem CFSG.KD.Fi24Tc.Pc.p1328 : Nat.beq (runC AR SD 1324 (ckL CFSG.KD.Fi24Tc.Pc.l1330) 2 1328 CFSG.KD.Fi24Tc.Pc.l1328) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f191 : Nat.beq (runC AR SD 1324 (finC AR SD (nat_lit 191) 1324 1332) 2 1330 CFSG.KD.Fi24Tc.Pc.l1330) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk191 : chk (nat_lit 191) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 191) (lo := 1324) (hi := 1332) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1326) CFSG.KD.Fi24Tc.Pc.p1324 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1328) CFSG.KD.Fi24Tc.Pc.p1326 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1330) CFSG.KD.Fi24Tc.Pc.p1328 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f191

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1332 : Nat := CFSG.KD.Fi24Tc.KV9 47
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1333 : Nat := CFSG.KD.Fi24Tc.KV9 48
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1334 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1332, CFSG.KD.Fi24Tc.Pc.v1333]
theorem CFSG.KD.Fi24Tc.Pc.p1332 : Nat.beq (runC AR SD 1332 (ckL CFSG.KD.Fi24Tc.Pc.l1334) 2 1332 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1334 : Nat := CFSG.KD.Fi24Tc.KV9 49
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1335 : Nat := CFSG.KD.Fi24Tc.KV9 50
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1336 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1332, CFSG.KD.Fi24Tc.Pc.v1333, CFSG.KD.Fi24Tc.Pc.v1334, CFSG.KD.Fi24Tc.Pc.v1335]
theorem CFSG.KD.Fi24Tc.Pc.p1334 : Nat.beq (runC AR SD 1332 (ckL CFSG.KD.Fi24Tc.Pc.l1336) 2 1334 CFSG.KD.Fi24Tc.Pc.l1334) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1336 : Nat := CFSG.KD.Fi24Tc.KV9 51
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1337 : Nat := CFSG.KD.Fi24Tc.KV9 52
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1338 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1332, CFSG.KD.Fi24Tc.Pc.v1333, CFSG.KD.Fi24Tc.Pc.v1334, CFSG.KD.Fi24Tc.Pc.v1335, CFSG.KD.Fi24Tc.Pc.v1336, CFSG.KD.Fi24Tc.Pc.v1337]
theorem CFSG.KD.Fi24Tc.Pc.p1336 : Nat.beq (runC AR SD 1332 (ckL CFSG.KD.Fi24Tc.Pc.l1338) 2 1336 CFSG.KD.Fi24Tc.Pc.l1336) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f192 : Nat.beq (runC AR SD 1332 (finC AR SD (nat_lit 192) 1332 1340) 2 1338 CFSG.KD.Fi24Tc.Pc.l1338) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk192 : chk (nat_lit 192) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 192) (lo := 1332) (hi := 1340) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1334) CFSG.KD.Fi24Tc.Pc.p1332 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1336) CFSG.KD.Fi24Tc.Pc.p1334 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1338) CFSG.KD.Fi24Tc.Pc.p1336 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f192

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1340 : Nat := CFSG.KD.Fi24Tc.KV9 53
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1341 : Nat := CFSG.KD.Fi24Tc.KV9 54
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1342 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1340, CFSG.KD.Fi24Tc.Pc.v1341]
theorem CFSG.KD.Fi24Tc.Pc.p1340 : Nat.beq (runC AR SD 1340 (ckL CFSG.KD.Fi24Tc.Pc.l1342) 2 1340 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1342 : Nat := CFSG.KD.Fi24Tc.KV9 55
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1343 : Nat := CFSG.KD.Fi24Tc.KV9 56
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1344 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1340, CFSG.KD.Fi24Tc.Pc.v1341, CFSG.KD.Fi24Tc.Pc.v1342, CFSG.KD.Fi24Tc.Pc.v1343]
theorem CFSG.KD.Fi24Tc.Pc.p1342 : Nat.beq (runC AR SD 1340 (ckL CFSG.KD.Fi24Tc.Pc.l1344) 2 1342 CFSG.KD.Fi24Tc.Pc.l1342) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1344 : Nat := CFSG.KD.Fi24Tc.KV9 57
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1345 : Nat := CFSG.KD.Fi24Tc.KV9 58
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1346 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1340, CFSG.KD.Fi24Tc.Pc.v1341, CFSG.KD.Fi24Tc.Pc.v1342, CFSG.KD.Fi24Tc.Pc.v1343, CFSG.KD.Fi24Tc.Pc.v1344, CFSG.KD.Fi24Tc.Pc.v1345]
theorem CFSG.KD.Fi24Tc.Pc.p1344 : Nat.beq (runC AR SD 1340 (ckL CFSG.KD.Fi24Tc.Pc.l1346) 2 1344 CFSG.KD.Fi24Tc.Pc.l1344) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f193 : Nat.beq (runC AR SD 1340 (finC AR SD (nat_lit 193) 1340 1348) 2 1346 CFSG.KD.Fi24Tc.Pc.l1346) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk193 : chk (nat_lit 193) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 193) (lo := 1340) (hi := 1348) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1342) CFSG.KD.Fi24Tc.Pc.p1340 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1344) CFSG.KD.Fi24Tc.Pc.p1342 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1346) CFSG.KD.Fi24Tc.Pc.p1344 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f193

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1348 : Nat := CFSG.KD.Fi24Tc.KV9 59
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1349 : Nat := CFSG.KD.Fi24Tc.KV9 60
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1350 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1348, CFSG.KD.Fi24Tc.Pc.v1349]
theorem CFSG.KD.Fi24Tc.Pc.p1348 : Nat.beq (runC AR SD 1348 (ckL CFSG.KD.Fi24Tc.Pc.l1350) 2 1348 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1350 : Nat := CFSG.KD.Fi24Tc.KV9 61
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1351 : Nat := CFSG.KD.Fi24Tc.KV9 62
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1352 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1348, CFSG.KD.Fi24Tc.Pc.v1349, CFSG.KD.Fi24Tc.Pc.v1350, CFSG.KD.Fi24Tc.Pc.v1351]
theorem CFSG.KD.Fi24Tc.Pc.p1350 : Nat.beq (runC AR SD 1348 (ckL CFSG.KD.Fi24Tc.Pc.l1352) 2 1350 CFSG.KD.Fi24Tc.Pc.l1350) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1352 : Nat := CFSG.KD.Fi24Tc.KV9 63
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1353 : Nat := CFSG.KD.Fi24Tc.KV9 64
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1354 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1348, CFSG.KD.Fi24Tc.Pc.v1349, CFSG.KD.Fi24Tc.Pc.v1350, CFSG.KD.Fi24Tc.Pc.v1351, CFSG.KD.Fi24Tc.Pc.v1352, CFSG.KD.Fi24Tc.Pc.v1353]
theorem CFSG.KD.Fi24Tc.Pc.p1352 : Nat.beq (runC AR SD 1348 (ckL CFSG.KD.Fi24Tc.Pc.l1354) 2 1352 CFSG.KD.Fi24Tc.Pc.l1352) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f194 : Nat.beq (runC AR SD 1348 (finC AR SD (nat_lit 194) 1348 1356) 2 1354 CFSG.KD.Fi24Tc.Pc.l1354) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk194 : chk (nat_lit 194) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 194) (lo := 1348) (hi := 1356) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1350) CFSG.KD.Fi24Tc.Pc.p1348 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1352) CFSG.KD.Fi24Tc.Pc.p1350 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1354) CFSG.KD.Fi24Tc.Pc.p1352 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f194

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1356 : Nat := CFSG.KD.Fi24Tc.KV9 65
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1357 : Nat := CFSG.KD.Fi24Tc.KV9 66
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1358 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1356, CFSG.KD.Fi24Tc.Pc.v1357]
theorem CFSG.KD.Fi24Tc.Pc.p1356 : Nat.beq (runC AR SD 1356 (ckL CFSG.KD.Fi24Tc.Pc.l1358) 2 1356 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1358 : Nat := CFSG.KD.Fi24Tc.KV9 67
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1359 : Nat := CFSG.KD.Fi24Tc.KV9 68
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1360 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1356, CFSG.KD.Fi24Tc.Pc.v1357, CFSG.KD.Fi24Tc.Pc.v1358, CFSG.KD.Fi24Tc.Pc.v1359]
theorem CFSG.KD.Fi24Tc.Pc.p1358 : Nat.beq (runC AR SD 1356 (ckL CFSG.KD.Fi24Tc.Pc.l1360) 2 1358 CFSG.KD.Fi24Tc.Pc.l1358) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1360 : Nat := CFSG.KD.Fi24Tc.KV9 69
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1361 : Nat := CFSG.KD.Fi24Tc.KV9 70
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1362 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1356, CFSG.KD.Fi24Tc.Pc.v1357, CFSG.KD.Fi24Tc.Pc.v1358, CFSG.KD.Fi24Tc.Pc.v1359, CFSG.KD.Fi24Tc.Pc.v1360, CFSG.KD.Fi24Tc.Pc.v1361]
theorem CFSG.KD.Fi24Tc.Pc.p1360 : Nat.beq (runC AR SD 1356 (ckL CFSG.KD.Fi24Tc.Pc.l1362) 2 1360 CFSG.KD.Fi24Tc.Pc.l1360) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f195 : Nat.beq (runC AR SD 1356 (finC AR SD (nat_lit 195) 1356 1364) 2 1362 CFSG.KD.Fi24Tc.Pc.l1362) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk195 : chk (nat_lit 195) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 195) (lo := 1356) (hi := 1364) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1358) CFSG.KD.Fi24Tc.Pc.p1356 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1360) CFSG.KD.Fi24Tc.Pc.p1358 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1362) CFSG.KD.Fi24Tc.Pc.p1360 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f195

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1364 : Nat := CFSG.KD.Fi24Tc.KV9 71
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1365 : Nat := CFSG.KD.Fi24Tc.KV9 72
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1366 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1364, CFSG.KD.Fi24Tc.Pc.v1365]
theorem CFSG.KD.Fi24Tc.Pc.p1364 : Nat.beq (runC AR SD 1364 (ckL CFSG.KD.Fi24Tc.Pc.l1366) 2 1364 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1366 : Nat := CFSG.KD.Fi24Tc.KV9 73
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1367 : Nat := CFSG.KD.Fi24Tc.KV9 74
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1368 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1364, CFSG.KD.Fi24Tc.Pc.v1365, CFSG.KD.Fi24Tc.Pc.v1366, CFSG.KD.Fi24Tc.Pc.v1367]
theorem CFSG.KD.Fi24Tc.Pc.p1366 : Nat.beq (runC AR SD 1364 (ckL CFSG.KD.Fi24Tc.Pc.l1368) 2 1366 CFSG.KD.Fi24Tc.Pc.l1366) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1368 : Nat := CFSG.KD.Fi24Tc.KV9 75
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1369 : Nat := CFSG.KD.Fi24Tc.KV9 76
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1370 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1364, CFSG.KD.Fi24Tc.Pc.v1365, CFSG.KD.Fi24Tc.Pc.v1366, CFSG.KD.Fi24Tc.Pc.v1367, CFSG.KD.Fi24Tc.Pc.v1368, CFSG.KD.Fi24Tc.Pc.v1369]
theorem CFSG.KD.Fi24Tc.Pc.p1368 : Nat.beq (runC AR SD 1364 (ckL CFSG.KD.Fi24Tc.Pc.l1370) 2 1368 CFSG.KD.Fi24Tc.Pc.l1368) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f196 : Nat.beq (runC AR SD 1364 (finC AR SD (nat_lit 196) 1364 1372) 2 1370 CFSG.KD.Fi24Tc.Pc.l1370) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk196 : chk (nat_lit 196) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 196) (lo := 1364) (hi := 1372) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1366) CFSG.KD.Fi24Tc.Pc.p1364 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1368) CFSG.KD.Fi24Tc.Pc.p1366 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1370) CFSG.KD.Fi24Tc.Pc.p1368 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f196

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1372 : Nat := CFSG.KD.Fi24Tc.KV9 77
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1373 : Nat := CFSG.KD.Fi24Tc.KV9 78
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1374 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1372, CFSG.KD.Fi24Tc.Pc.v1373]
theorem CFSG.KD.Fi24Tc.Pc.p1372 : Nat.beq (runC AR SD 1372 (ckL CFSG.KD.Fi24Tc.Pc.l1374) 2 1372 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1374 : Nat := CFSG.KD.Fi24Tc.KV9 79
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1375 : Nat := CFSG.KD.Fi24Tc.KV9 80
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1376 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1372, CFSG.KD.Fi24Tc.Pc.v1373, CFSG.KD.Fi24Tc.Pc.v1374, CFSG.KD.Fi24Tc.Pc.v1375]
theorem CFSG.KD.Fi24Tc.Pc.p1374 : Nat.beq (runC AR SD 1372 (ckL CFSG.KD.Fi24Tc.Pc.l1376) 2 1374 CFSG.KD.Fi24Tc.Pc.l1374) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1376 : Nat := CFSG.KD.Fi24Tc.KV9 81
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1377 : Nat := CFSG.KD.Fi24Tc.KV9 82
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1378 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1372, CFSG.KD.Fi24Tc.Pc.v1373, CFSG.KD.Fi24Tc.Pc.v1374, CFSG.KD.Fi24Tc.Pc.v1375, CFSG.KD.Fi24Tc.Pc.v1376, CFSG.KD.Fi24Tc.Pc.v1377]
theorem CFSG.KD.Fi24Tc.Pc.p1376 : Nat.beq (runC AR SD 1372 (ckL CFSG.KD.Fi24Tc.Pc.l1378) 2 1376 CFSG.KD.Fi24Tc.Pc.l1376) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f197 : Nat.beq (runC AR SD 1372 (finC AR SD (nat_lit 197) 1372 1380) 2 1378 CFSG.KD.Fi24Tc.Pc.l1378) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk197 : chk (nat_lit 197) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 197) (lo := 1372) (hi := 1380) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1374) CFSG.KD.Fi24Tc.Pc.p1372 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1376) CFSG.KD.Fi24Tc.Pc.p1374 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1378) CFSG.KD.Fi24Tc.Pc.p1376 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f197

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1380 : Nat := CFSG.KD.Fi24Tc.KV9 83
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1381 : Nat := CFSG.KD.Fi24Tc.KV9 84
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1382 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1380, CFSG.KD.Fi24Tc.Pc.v1381]
theorem CFSG.KD.Fi24Tc.Pc.p1380 : Nat.beq (runC AR SD 1380 (ckL CFSG.KD.Fi24Tc.Pc.l1382) 2 1380 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1382 : Nat := CFSG.KD.Fi24Tc.KV9 85
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1383 : Nat := CFSG.KD.Fi24Tc.KV9 86
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1384 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1380, CFSG.KD.Fi24Tc.Pc.v1381, CFSG.KD.Fi24Tc.Pc.v1382, CFSG.KD.Fi24Tc.Pc.v1383]
theorem CFSG.KD.Fi24Tc.Pc.p1382 : Nat.beq (runC AR SD 1380 (ckL CFSG.KD.Fi24Tc.Pc.l1384) 2 1382 CFSG.KD.Fi24Tc.Pc.l1382) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1384 : Nat := CFSG.KD.Fi24Tc.KV9 87
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1385 : Nat := CFSG.KD.Fi24Tc.KV9 88
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1386 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1380, CFSG.KD.Fi24Tc.Pc.v1381, CFSG.KD.Fi24Tc.Pc.v1382, CFSG.KD.Fi24Tc.Pc.v1383, CFSG.KD.Fi24Tc.Pc.v1384, CFSG.KD.Fi24Tc.Pc.v1385]
theorem CFSG.KD.Fi24Tc.Pc.p1384 : Nat.beq (runC AR SD 1380 (ckL CFSG.KD.Fi24Tc.Pc.l1386) 2 1384 CFSG.KD.Fi24Tc.Pc.l1384) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f198 : Nat.beq (runC AR SD 1380 (finC AR SD (nat_lit 198) 1380 1388) 2 1386 CFSG.KD.Fi24Tc.Pc.l1386) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk198 : chk (nat_lit 198) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 198) (lo := 1380) (hi := 1388) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1382) CFSG.KD.Fi24Tc.Pc.p1380 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1384) CFSG.KD.Fi24Tc.Pc.p1382 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1386) CFSG.KD.Fi24Tc.Pc.p1384 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f198

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1388 : Nat := CFSG.KD.Fi24Tc.KV9 89
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1389 : Nat := CFSG.KD.Fi24Tc.KV9 90
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1390 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1388, CFSG.KD.Fi24Tc.Pc.v1389]
theorem CFSG.KD.Fi24Tc.Pc.p1388 : Nat.beq (runC AR SD 1388 (ckL CFSG.KD.Fi24Tc.Pc.l1390) 2 1388 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1390 : Nat := CFSG.KD.Fi24Tc.KV9 91
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1391 : Nat := CFSG.KD.Fi24Tc.KV9 92
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1392 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1388, CFSG.KD.Fi24Tc.Pc.v1389, CFSG.KD.Fi24Tc.Pc.v1390, CFSG.KD.Fi24Tc.Pc.v1391]
theorem CFSG.KD.Fi24Tc.Pc.p1390 : Nat.beq (runC AR SD 1388 (ckL CFSG.KD.Fi24Tc.Pc.l1392) 2 1390 CFSG.KD.Fi24Tc.Pc.l1390) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1392 : Nat := CFSG.KD.Fi24Tc.KV9 93
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1393 : Nat := CFSG.KD.Fi24Tc.KV9 94
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1394 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1388, CFSG.KD.Fi24Tc.Pc.v1389, CFSG.KD.Fi24Tc.Pc.v1390, CFSG.KD.Fi24Tc.Pc.v1391, CFSG.KD.Fi24Tc.Pc.v1392, CFSG.KD.Fi24Tc.Pc.v1393]
theorem CFSG.KD.Fi24Tc.Pc.p1392 : Nat.beq (runC AR SD 1388 (ckL CFSG.KD.Fi24Tc.Pc.l1394) 2 1392 CFSG.KD.Fi24Tc.Pc.l1392) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f199 : Nat.beq (runC AR SD 1388 (finC AR SD (nat_lit 199) 1388 1396) 2 1394 CFSG.KD.Fi24Tc.Pc.l1394) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk199 : chk (nat_lit 199) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 199) (lo := 1388) (hi := 1396) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1390) CFSG.KD.Fi24Tc.Pc.p1388 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1392) CFSG.KD.Fi24Tc.Pc.p1390 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1394) CFSG.KD.Fi24Tc.Pc.p1392 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f199

end
