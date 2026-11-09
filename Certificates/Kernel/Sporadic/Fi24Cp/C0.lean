module

public import Certificates.Kernel.Sporadic.Fi24Cp.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Cp KV0 "Certificates/Kernel/Sporadic/Fi24Cp/data/v0.bin" 152491 4 21043758 12635983272815600161

public section

open CFSG.KD.Fi24Cp CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v0 : Nat := CFSG.KD.Fi24Cp.KV0 0
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v1 : Nat := CFSG.KD.Fi24Cp.KV0 1
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l2 : List Nat := [CFSG.KD.Fi24Cp.Pc.v0, CFSG.KD.Fi24Cp.Pc.v1]
theorem CFSG.KD.Fi24Cp.Pc.p0 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Cp.Pc.l2) 2 0 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v2 : Nat := CFSG.KD.Fi24Cp.KV0 2
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v3 : Nat := CFSG.KD.Fi24Cp.KV0 3
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l4 : List Nat := [CFSG.KD.Fi24Cp.Pc.v0, CFSG.KD.Fi24Cp.Pc.v1, CFSG.KD.Fi24Cp.Pc.v2, CFSG.KD.Fi24Cp.Pc.v3]
theorem CFSG.KD.Fi24Cp.Pc.p2 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Cp.Pc.l4) 2 2 CFSG.KD.Fi24Cp.Pc.l2) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v4 : Nat := CFSG.KD.Fi24Cp.KV0 4
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v5 : Nat := CFSG.KD.Fi24Cp.KV0 5
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l6 : List Nat := [CFSG.KD.Fi24Cp.Pc.v0, CFSG.KD.Fi24Cp.Pc.v1, CFSG.KD.Fi24Cp.Pc.v2, CFSG.KD.Fi24Cp.Pc.v3, CFSG.KD.Fi24Cp.Pc.v4, CFSG.KD.Fi24Cp.Pc.v5]
theorem CFSG.KD.Fi24Cp.Pc.p4 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Cp.Pc.l6) 2 4 CFSG.KD.Fi24Cp.Pc.l4) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v6 : Nat := CFSG.KD.Fi24Cp.KV0 6
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v7 : Nat := CFSG.KD.Fi24Cp.KV0 7
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l8 : List Nat := [CFSG.KD.Fi24Cp.Pc.v0, CFSG.KD.Fi24Cp.Pc.v1, CFSG.KD.Fi24Cp.Pc.v2, CFSG.KD.Fi24Cp.Pc.v3, CFSG.KD.Fi24Cp.Pc.v4, CFSG.KD.Fi24Cp.Pc.v5, CFSG.KD.Fi24Cp.Pc.v6, CFSG.KD.Fi24Cp.Pc.v7]
theorem CFSG.KD.Fi24Cp.Pc.p6 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Cp.Pc.l8) 2 6 CFSG.KD.Fi24Cp.Pc.l6) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v8 : Nat := CFSG.KD.Fi24Cp.KV0 8
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v9 : Nat := CFSG.KD.Fi24Cp.KV0 9
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l10 : List Nat := [CFSG.KD.Fi24Cp.Pc.v0, CFSG.KD.Fi24Cp.Pc.v1, CFSG.KD.Fi24Cp.Pc.v2, CFSG.KD.Fi24Cp.Pc.v3, CFSG.KD.Fi24Cp.Pc.v4, CFSG.KD.Fi24Cp.Pc.v5, CFSG.KD.Fi24Cp.Pc.v6, CFSG.KD.Fi24Cp.Pc.v7, CFSG.KD.Fi24Cp.Pc.v8, CFSG.KD.Fi24Cp.Pc.v9]
theorem CFSG.KD.Fi24Cp.Pc.p8 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Cp.Pc.l10) 2 8 CFSG.KD.Fi24Cp.Pc.l8) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v10 : Nat := CFSG.KD.Fi24Cp.KV0 10
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v11 : Nat := CFSG.KD.Fi24Cp.KV0 11
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l12 : List Nat := [CFSG.KD.Fi24Cp.Pc.v0, CFSG.KD.Fi24Cp.Pc.v1, CFSG.KD.Fi24Cp.Pc.v2, CFSG.KD.Fi24Cp.Pc.v3, CFSG.KD.Fi24Cp.Pc.v4, CFSG.KD.Fi24Cp.Pc.v5, CFSG.KD.Fi24Cp.Pc.v6, CFSG.KD.Fi24Cp.Pc.v7, CFSG.KD.Fi24Cp.Pc.v8, CFSG.KD.Fi24Cp.Pc.v9, CFSG.KD.Fi24Cp.Pc.v10, CFSG.KD.Fi24Cp.Pc.v11]
theorem CFSG.KD.Fi24Cp.Pc.p10 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Cp.Pc.l12) 2 10 CFSG.KD.Fi24Cp.Pc.l10) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v12 : Nat := CFSG.KD.Fi24Cp.KV0 12
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v13 : Nat := CFSG.KD.Fi24Cp.KV0 13
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l14 : List Nat := [CFSG.KD.Fi24Cp.Pc.v0, CFSG.KD.Fi24Cp.Pc.v1, CFSG.KD.Fi24Cp.Pc.v2, CFSG.KD.Fi24Cp.Pc.v3, CFSG.KD.Fi24Cp.Pc.v4, CFSG.KD.Fi24Cp.Pc.v5, CFSG.KD.Fi24Cp.Pc.v6, CFSG.KD.Fi24Cp.Pc.v7, CFSG.KD.Fi24Cp.Pc.v8, CFSG.KD.Fi24Cp.Pc.v9, CFSG.KD.Fi24Cp.Pc.v10, CFSG.KD.Fi24Cp.Pc.v11, CFSG.KD.Fi24Cp.Pc.v12, CFSG.KD.Fi24Cp.Pc.v13]
theorem CFSG.KD.Fi24Cp.Pc.p12 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Cp.Pc.l14) 2 12 CFSG.KD.Fi24Cp.Pc.l12) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v14 : Nat := CFSG.KD.Fi24Cp.KV0 14
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v15 : Nat := CFSG.KD.Fi24Cp.KV0 15
theorem CFSG.KD.Fi24Cp.Pc.f0 : Nat.beq (runC AR SD 0 (finC AR SD (nat_lit 0) 0 16) 2 14 CFSG.KD.Fi24Cp.Pc.l14) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk0 : chk (nat_lit 0) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 0) (lo := 0) (hi := 16) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 2) CFSG.KD.Fi24Cp.Pc.p0 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 4) CFSG.KD.Fi24Cp.Pc.p2 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 6) CFSG.KD.Fi24Cp.Pc.p4 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 8) CFSG.KD.Fi24Cp.Pc.p6 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 10) CFSG.KD.Fi24Cp.Pc.p8 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 12) CFSG.KD.Fi24Cp.Pc.p10 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 14) CFSG.KD.Fi24Cp.Pc.p12 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f0

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v16 : Nat := CFSG.KD.Fi24Cp.KV0 16
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v17 : Nat := CFSG.KD.Fi24Cp.KV0 17
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l18 : List Nat := [CFSG.KD.Fi24Cp.Pc.v16, CFSG.KD.Fi24Cp.Pc.v17]
theorem CFSG.KD.Fi24Cp.Pc.p16 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Cp.Pc.l18) 2 16 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v18 : Nat := CFSG.KD.Fi24Cp.KV0 18
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v19 : Nat := CFSG.KD.Fi24Cp.KV0 19
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l20 : List Nat := [CFSG.KD.Fi24Cp.Pc.v16, CFSG.KD.Fi24Cp.Pc.v17, CFSG.KD.Fi24Cp.Pc.v18, CFSG.KD.Fi24Cp.Pc.v19]
theorem CFSG.KD.Fi24Cp.Pc.p18 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Cp.Pc.l20) 2 18 CFSG.KD.Fi24Cp.Pc.l18) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v20 : Nat := CFSG.KD.Fi24Cp.KV0 20
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v21 : Nat := CFSG.KD.Fi24Cp.KV0 21
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l22 : List Nat := [CFSG.KD.Fi24Cp.Pc.v16, CFSG.KD.Fi24Cp.Pc.v17, CFSG.KD.Fi24Cp.Pc.v18, CFSG.KD.Fi24Cp.Pc.v19, CFSG.KD.Fi24Cp.Pc.v20, CFSG.KD.Fi24Cp.Pc.v21]
theorem CFSG.KD.Fi24Cp.Pc.p20 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Cp.Pc.l22) 2 20 CFSG.KD.Fi24Cp.Pc.l20) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v22 : Nat := CFSG.KD.Fi24Cp.KV0 22
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v23 : Nat := CFSG.KD.Fi24Cp.KV0 23
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l24 : List Nat := [CFSG.KD.Fi24Cp.Pc.v16, CFSG.KD.Fi24Cp.Pc.v17, CFSG.KD.Fi24Cp.Pc.v18, CFSG.KD.Fi24Cp.Pc.v19, CFSG.KD.Fi24Cp.Pc.v20, CFSG.KD.Fi24Cp.Pc.v21, CFSG.KD.Fi24Cp.Pc.v22, CFSG.KD.Fi24Cp.Pc.v23]
theorem CFSG.KD.Fi24Cp.Pc.p22 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Cp.Pc.l24) 2 22 CFSG.KD.Fi24Cp.Pc.l22) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v24 : Nat := CFSG.KD.Fi24Cp.KV0 24
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v25 : Nat := CFSG.KD.Fi24Cp.KV0 25
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l26 : List Nat := [CFSG.KD.Fi24Cp.Pc.v16, CFSG.KD.Fi24Cp.Pc.v17, CFSG.KD.Fi24Cp.Pc.v18, CFSG.KD.Fi24Cp.Pc.v19, CFSG.KD.Fi24Cp.Pc.v20, CFSG.KD.Fi24Cp.Pc.v21, CFSG.KD.Fi24Cp.Pc.v22, CFSG.KD.Fi24Cp.Pc.v23, CFSG.KD.Fi24Cp.Pc.v24, CFSG.KD.Fi24Cp.Pc.v25]
theorem CFSG.KD.Fi24Cp.Pc.p24 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Cp.Pc.l26) 2 24 CFSG.KD.Fi24Cp.Pc.l24) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v26 : Nat := CFSG.KD.Fi24Cp.KV0 26
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v27 : Nat := CFSG.KD.Fi24Cp.KV0 27
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l28 : List Nat := [CFSG.KD.Fi24Cp.Pc.v16, CFSG.KD.Fi24Cp.Pc.v17, CFSG.KD.Fi24Cp.Pc.v18, CFSG.KD.Fi24Cp.Pc.v19, CFSG.KD.Fi24Cp.Pc.v20, CFSG.KD.Fi24Cp.Pc.v21, CFSG.KD.Fi24Cp.Pc.v22, CFSG.KD.Fi24Cp.Pc.v23, CFSG.KD.Fi24Cp.Pc.v24, CFSG.KD.Fi24Cp.Pc.v25, CFSG.KD.Fi24Cp.Pc.v26, CFSG.KD.Fi24Cp.Pc.v27]
theorem CFSG.KD.Fi24Cp.Pc.p26 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Cp.Pc.l28) 2 26 CFSG.KD.Fi24Cp.Pc.l26) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v28 : Nat := CFSG.KD.Fi24Cp.KV0 28
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v29 : Nat := CFSG.KD.Fi24Cp.KV0 29
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l30 : List Nat := [CFSG.KD.Fi24Cp.Pc.v16, CFSG.KD.Fi24Cp.Pc.v17, CFSG.KD.Fi24Cp.Pc.v18, CFSG.KD.Fi24Cp.Pc.v19, CFSG.KD.Fi24Cp.Pc.v20, CFSG.KD.Fi24Cp.Pc.v21, CFSG.KD.Fi24Cp.Pc.v22, CFSG.KD.Fi24Cp.Pc.v23, CFSG.KD.Fi24Cp.Pc.v24, CFSG.KD.Fi24Cp.Pc.v25, CFSG.KD.Fi24Cp.Pc.v26, CFSG.KD.Fi24Cp.Pc.v27, CFSG.KD.Fi24Cp.Pc.v28, CFSG.KD.Fi24Cp.Pc.v29]
theorem CFSG.KD.Fi24Cp.Pc.p28 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Cp.Pc.l30) 2 28 CFSG.KD.Fi24Cp.Pc.l28) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v30 : Nat := CFSG.KD.Fi24Cp.KV0 30
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v31 : Nat := CFSG.KD.Fi24Cp.KV0 31
theorem CFSG.KD.Fi24Cp.Pc.f1 : Nat.beq (runC AR SD 16 (finC AR SD (nat_lit 1) 16 32) 2 30 CFSG.KD.Fi24Cp.Pc.l30) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk1 : chk (nat_lit 1) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 1) (lo := 16) (hi := 32) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 18) CFSG.KD.Fi24Cp.Pc.p16 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 20) CFSG.KD.Fi24Cp.Pc.p18 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 22) CFSG.KD.Fi24Cp.Pc.p20 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 24) CFSG.KD.Fi24Cp.Pc.p22 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 26) CFSG.KD.Fi24Cp.Pc.p24 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 28) CFSG.KD.Fi24Cp.Pc.p26 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 30) CFSG.KD.Fi24Cp.Pc.p28 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f1

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v32 : Nat := CFSG.KD.Fi24Cp.KV0 32
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v33 : Nat := CFSG.KD.Fi24Cp.KV0 33
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l34 : List Nat := [CFSG.KD.Fi24Cp.Pc.v32, CFSG.KD.Fi24Cp.Pc.v33]
theorem CFSG.KD.Fi24Cp.Pc.p32 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Cp.Pc.l34) 2 32 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v34 : Nat := CFSG.KD.Fi24Cp.KV0 34
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v35 : Nat := CFSG.KD.Fi24Cp.KV0 35
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l36 : List Nat := [CFSG.KD.Fi24Cp.Pc.v32, CFSG.KD.Fi24Cp.Pc.v33, CFSG.KD.Fi24Cp.Pc.v34, CFSG.KD.Fi24Cp.Pc.v35]
theorem CFSG.KD.Fi24Cp.Pc.p34 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Cp.Pc.l36) 2 34 CFSG.KD.Fi24Cp.Pc.l34) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v36 : Nat := CFSG.KD.Fi24Cp.KV0 36
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v37 : Nat := CFSG.KD.Fi24Cp.KV0 37
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l38 : List Nat := [CFSG.KD.Fi24Cp.Pc.v32, CFSG.KD.Fi24Cp.Pc.v33, CFSG.KD.Fi24Cp.Pc.v34, CFSG.KD.Fi24Cp.Pc.v35, CFSG.KD.Fi24Cp.Pc.v36, CFSG.KD.Fi24Cp.Pc.v37]
theorem CFSG.KD.Fi24Cp.Pc.p36 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Cp.Pc.l38) 2 36 CFSG.KD.Fi24Cp.Pc.l36) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v38 : Nat := CFSG.KD.Fi24Cp.KV0 38
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v39 : Nat := CFSG.KD.Fi24Cp.KV0 39
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l40 : List Nat := [CFSG.KD.Fi24Cp.Pc.v32, CFSG.KD.Fi24Cp.Pc.v33, CFSG.KD.Fi24Cp.Pc.v34, CFSG.KD.Fi24Cp.Pc.v35, CFSG.KD.Fi24Cp.Pc.v36, CFSG.KD.Fi24Cp.Pc.v37, CFSG.KD.Fi24Cp.Pc.v38, CFSG.KD.Fi24Cp.Pc.v39]
theorem CFSG.KD.Fi24Cp.Pc.p38 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Cp.Pc.l40) 2 38 CFSG.KD.Fi24Cp.Pc.l38) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v40 : Nat := CFSG.KD.Fi24Cp.KV0 40
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v41 : Nat := CFSG.KD.Fi24Cp.KV0 41
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l42 : List Nat := [CFSG.KD.Fi24Cp.Pc.v32, CFSG.KD.Fi24Cp.Pc.v33, CFSG.KD.Fi24Cp.Pc.v34, CFSG.KD.Fi24Cp.Pc.v35, CFSG.KD.Fi24Cp.Pc.v36, CFSG.KD.Fi24Cp.Pc.v37, CFSG.KD.Fi24Cp.Pc.v38, CFSG.KD.Fi24Cp.Pc.v39, CFSG.KD.Fi24Cp.Pc.v40, CFSG.KD.Fi24Cp.Pc.v41]
theorem CFSG.KD.Fi24Cp.Pc.p40 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Cp.Pc.l42) 2 40 CFSG.KD.Fi24Cp.Pc.l40) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v42 : Nat := CFSG.KD.Fi24Cp.KV0 42
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v43 : Nat := CFSG.KD.Fi24Cp.KV0 43
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l44 : List Nat := [CFSG.KD.Fi24Cp.Pc.v32, CFSG.KD.Fi24Cp.Pc.v33, CFSG.KD.Fi24Cp.Pc.v34, CFSG.KD.Fi24Cp.Pc.v35, CFSG.KD.Fi24Cp.Pc.v36, CFSG.KD.Fi24Cp.Pc.v37, CFSG.KD.Fi24Cp.Pc.v38, CFSG.KD.Fi24Cp.Pc.v39, CFSG.KD.Fi24Cp.Pc.v40, CFSG.KD.Fi24Cp.Pc.v41, CFSG.KD.Fi24Cp.Pc.v42, CFSG.KD.Fi24Cp.Pc.v43]
theorem CFSG.KD.Fi24Cp.Pc.p42 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Cp.Pc.l44) 2 42 CFSG.KD.Fi24Cp.Pc.l42) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v44 : Nat := CFSG.KD.Fi24Cp.KV0 44
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v45 : Nat := CFSG.KD.Fi24Cp.KV0 45
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l46 : List Nat := [CFSG.KD.Fi24Cp.Pc.v32, CFSG.KD.Fi24Cp.Pc.v33, CFSG.KD.Fi24Cp.Pc.v34, CFSG.KD.Fi24Cp.Pc.v35, CFSG.KD.Fi24Cp.Pc.v36, CFSG.KD.Fi24Cp.Pc.v37, CFSG.KD.Fi24Cp.Pc.v38, CFSG.KD.Fi24Cp.Pc.v39, CFSG.KD.Fi24Cp.Pc.v40, CFSG.KD.Fi24Cp.Pc.v41, CFSG.KD.Fi24Cp.Pc.v42, CFSG.KD.Fi24Cp.Pc.v43, CFSG.KD.Fi24Cp.Pc.v44, CFSG.KD.Fi24Cp.Pc.v45]
theorem CFSG.KD.Fi24Cp.Pc.p44 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Cp.Pc.l46) 2 44 CFSG.KD.Fi24Cp.Pc.l44) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v46 : Nat := CFSG.KD.Fi24Cp.KV0 46
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v47 : Nat := CFSG.KD.Fi24Cp.KV0 47
theorem CFSG.KD.Fi24Cp.Pc.f2 : Nat.beq (runC AR SD 32 (finC AR SD (nat_lit 2) 32 48) 2 46 CFSG.KD.Fi24Cp.Pc.l46) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk2 : chk (nat_lit 2) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 2) (lo := 32) (hi := 48) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 34) CFSG.KD.Fi24Cp.Pc.p32 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 36) CFSG.KD.Fi24Cp.Pc.p34 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 38) CFSG.KD.Fi24Cp.Pc.p36 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 40) CFSG.KD.Fi24Cp.Pc.p38 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 42) CFSG.KD.Fi24Cp.Pc.p40 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 44) CFSG.KD.Fi24Cp.Pc.p42 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 46) CFSG.KD.Fi24Cp.Pc.p44 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f2

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v48 : Nat := CFSG.KD.Fi24Cp.KV0 48
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v49 : Nat := CFSG.KD.Fi24Cp.KV0 49
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l50 : List Nat := [CFSG.KD.Fi24Cp.Pc.v48, CFSG.KD.Fi24Cp.Pc.v49]
theorem CFSG.KD.Fi24Cp.Pc.p48 : Nat.beq (runC AR SD 48 (ckL CFSG.KD.Fi24Cp.Pc.l50) 2 48 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v50 : Nat := CFSG.KD.Fi24Cp.KV0 50
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v51 : Nat := CFSG.KD.Fi24Cp.KV0 51
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l52 : List Nat := [CFSG.KD.Fi24Cp.Pc.v48, CFSG.KD.Fi24Cp.Pc.v49, CFSG.KD.Fi24Cp.Pc.v50, CFSG.KD.Fi24Cp.Pc.v51]
theorem CFSG.KD.Fi24Cp.Pc.p50 : Nat.beq (runC AR SD 48 (ckL CFSG.KD.Fi24Cp.Pc.l52) 2 50 CFSG.KD.Fi24Cp.Pc.l50) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v52 : Nat := CFSG.KD.Fi24Cp.KV0 52
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l53 : List Nat := [CFSG.KD.Fi24Cp.Pc.v48, CFSG.KD.Fi24Cp.Pc.v49, CFSG.KD.Fi24Cp.Pc.v50, CFSG.KD.Fi24Cp.Pc.v51, CFSG.KD.Fi24Cp.Pc.v52]
theorem CFSG.KD.Fi24Cp.Pc.p52 : Nat.beq (runC AR SD 48 (ckL CFSG.KD.Fi24Cp.Pc.l53) 1 52 CFSG.KD.Fi24Cp.Pc.l52) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a53_1 : Nat := CFSG.KD.Fi24Cp.KV0 53
theorem CFSG.KD.Fi24Cp.Pc.q53_1 : Nat.beq (powTop AR.mul (getV AR SD 48 CFSG.KD.Fi24Cp.Pc.l53 (SD.na.getD 53 0)) (SD.nk.getD 53 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a53_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v53 : Nat := CFSG.KD.Fi24Cp.KV0 54
theorem CFSG.KD.Fi24Cp.Pc.r53 : Nat.beq (powR AR.mul AR.one (getV AR SD 48 CFSG.KD.Fi24Cp.Pc.l53 (SD.na.getD 53 0)) (SD.nk.getD 53 1) 1 CFSG.KD.Fi24Cp.Pc.a53_1 true) CFSG.KD.Fi24Cp.Pc.v53 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v54 : Nat := CFSG.KD.Fi24Cp.KV0 55
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v55 : Nat := CFSG.KD.Fi24Cp.KV0 56
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l54 : List Nat := [CFSG.KD.Fi24Cp.Pc.v48, CFSG.KD.Fi24Cp.Pc.v49, CFSG.KD.Fi24Cp.Pc.v50, CFSG.KD.Fi24Cp.Pc.v51, CFSG.KD.Fi24Cp.Pc.v52, CFSG.KD.Fi24Cp.Pc.v53]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l56 : List Nat := [CFSG.KD.Fi24Cp.Pc.v48, CFSG.KD.Fi24Cp.Pc.v49, CFSG.KD.Fi24Cp.Pc.v50, CFSG.KD.Fi24Cp.Pc.v51, CFSG.KD.Fi24Cp.Pc.v52, CFSG.KD.Fi24Cp.Pc.v53, CFSG.KD.Fi24Cp.Pc.v54, CFSG.KD.Fi24Cp.Pc.v55]
theorem CFSG.KD.Fi24Cp.Pc.p54 : Nat.beq (runC AR SD 48 (ckL CFSG.KD.Fi24Cp.Pc.l56) 2 54 CFSG.KD.Fi24Cp.Pc.l54) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v56 : Nat := CFSG.KD.Fi24Cp.KV0 57
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v57 : Nat := CFSG.KD.Fi24Cp.KV0 58
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l58 : List Nat := [CFSG.KD.Fi24Cp.Pc.v48, CFSG.KD.Fi24Cp.Pc.v49, CFSG.KD.Fi24Cp.Pc.v50, CFSG.KD.Fi24Cp.Pc.v51, CFSG.KD.Fi24Cp.Pc.v52, CFSG.KD.Fi24Cp.Pc.v53, CFSG.KD.Fi24Cp.Pc.v54, CFSG.KD.Fi24Cp.Pc.v55, CFSG.KD.Fi24Cp.Pc.v56, CFSG.KD.Fi24Cp.Pc.v57]
theorem CFSG.KD.Fi24Cp.Pc.p56 : Nat.beq (runC AR SD 48 (ckL CFSG.KD.Fi24Cp.Pc.l58) 2 56 CFSG.KD.Fi24Cp.Pc.l56) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v58 : Nat := CFSG.KD.Fi24Cp.KV0 59
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v59 : Nat := CFSG.KD.Fi24Cp.KV0 60
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l60 : List Nat := [CFSG.KD.Fi24Cp.Pc.v48, CFSG.KD.Fi24Cp.Pc.v49, CFSG.KD.Fi24Cp.Pc.v50, CFSG.KD.Fi24Cp.Pc.v51, CFSG.KD.Fi24Cp.Pc.v52, CFSG.KD.Fi24Cp.Pc.v53, CFSG.KD.Fi24Cp.Pc.v54, CFSG.KD.Fi24Cp.Pc.v55, CFSG.KD.Fi24Cp.Pc.v56, CFSG.KD.Fi24Cp.Pc.v57, CFSG.KD.Fi24Cp.Pc.v58, CFSG.KD.Fi24Cp.Pc.v59]
theorem CFSG.KD.Fi24Cp.Pc.p58 : Nat.beq (runC AR SD 48 (ckL CFSG.KD.Fi24Cp.Pc.l60) 2 58 CFSG.KD.Fi24Cp.Pc.l58) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v60 : Nat := CFSG.KD.Fi24Cp.KV0 61
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v61 : Nat := CFSG.KD.Fi24Cp.KV0 62
theorem CFSG.KD.Fi24Cp.Pc.f3 : Nat.beq (runC AR SD 48 (finC AR SD (nat_lit 3) 48 62) 2 60 CFSG.KD.Fi24Cp.Pc.l60) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk3 : chk (nat_lit 3) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 3) (lo := 48) (hi := 62) (m := 14) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 14) (m2 := 12) (j2 := 50) CFSG.KD.Fi24Cp.Pc.p48 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 52) CFSG.KD.Fi24Cp.Pc.p50 rfl rfl).trans ((runC_seq (m := 10) (m2 := 9) (j2 := 53) CFSG.KD.Fi24Cp.Pc.p52 rfl rfl).trans ((runC_node (m := 9) (m2 := 8) (j2 := 54) (Lr := CFSG.KD.Fi24Cp.Pc.l54) ((nodeV_pow (R := AR) (D := SD) (lo := 48) (L := CFSG.KD.Fi24Cp.Pc.l53) (j := 53) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 48 CFSG.KD.Fi24Cp.Pc.l53 (SD.na.getD 53 0)) (SD.nk.getD 53 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q53_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r53)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 56) CFSG.KD.Fi24Cp.Pc.p54 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 58) CFSG.KD.Fi24Cp.Pc.p56 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 60) CFSG.KD.Fi24Cp.Pc.p58 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f3

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v62 : Nat := CFSG.KD.Fi24Cp.KV0 63
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v63 : Nat := CFSG.KD.Fi24Cp.KV0 64
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l64 : List Nat := [CFSG.KD.Fi24Cp.Pc.v62, CFSG.KD.Fi24Cp.Pc.v63]
theorem CFSG.KD.Fi24Cp.Pc.p62 : Nat.beq (runC AR SD 62 (ckL CFSG.KD.Fi24Cp.Pc.l64) 2 62 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v64 : Nat := CFSG.KD.Fi24Cp.KV0 65
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v65 : Nat := CFSG.KD.Fi24Cp.KV0 66
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l66 : List Nat := [CFSG.KD.Fi24Cp.Pc.v62, CFSG.KD.Fi24Cp.Pc.v63, CFSG.KD.Fi24Cp.Pc.v64, CFSG.KD.Fi24Cp.Pc.v65]
theorem CFSG.KD.Fi24Cp.Pc.p64 : Nat.beq (runC AR SD 62 (ckL CFSG.KD.Fi24Cp.Pc.l66) 2 64 CFSG.KD.Fi24Cp.Pc.l64) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a66_1 : Nat := CFSG.KD.Fi24Cp.KV0 67
theorem CFSG.KD.Fi24Cp.Pc.q66_1 : Nat.beq (powTop AR.mul (getV AR SD 62 CFSG.KD.Fi24Cp.Pc.l66 (SD.na.getD 66 0)) (SD.nk.getD 66 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a66_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v66 : Nat := CFSG.KD.Fi24Cp.KV0 68
theorem CFSG.KD.Fi24Cp.Pc.r66 : Nat.beq (powR AR.mul AR.one (getV AR SD 62 CFSG.KD.Fi24Cp.Pc.l66 (SD.na.getD 66 0)) (SD.nk.getD 66 1) 1 CFSG.KD.Fi24Cp.Pc.a66_1 true) CFSG.KD.Fi24Cp.Pc.v66 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v67 : Nat := CFSG.KD.Fi24Cp.KV0 69
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v68 : Nat := CFSG.KD.Fi24Cp.KV0 70
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l67 : List Nat := [CFSG.KD.Fi24Cp.Pc.v62, CFSG.KD.Fi24Cp.Pc.v63, CFSG.KD.Fi24Cp.Pc.v64, CFSG.KD.Fi24Cp.Pc.v65, CFSG.KD.Fi24Cp.Pc.v66]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l69 : List Nat := [CFSG.KD.Fi24Cp.Pc.v62, CFSG.KD.Fi24Cp.Pc.v63, CFSG.KD.Fi24Cp.Pc.v64, CFSG.KD.Fi24Cp.Pc.v65, CFSG.KD.Fi24Cp.Pc.v66, CFSG.KD.Fi24Cp.Pc.v67, CFSG.KD.Fi24Cp.Pc.v68]
theorem CFSG.KD.Fi24Cp.Pc.p67 : Nat.beq (runC AR SD 62 (ckL CFSG.KD.Fi24Cp.Pc.l69) 2 67 CFSG.KD.Fi24Cp.Pc.l67) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v69 : Nat := CFSG.KD.Fi24Cp.KV0 71
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v70 : Nat := CFSG.KD.Fi24Cp.KV0 72
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l71 : List Nat := [CFSG.KD.Fi24Cp.Pc.v62, CFSG.KD.Fi24Cp.Pc.v63, CFSG.KD.Fi24Cp.Pc.v64, CFSG.KD.Fi24Cp.Pc.v65, CFSG.KD.Fi24Cp.Pc.v66, CFSG.KD.Fi24Cp.Pc.v67, CFSG.KD.Fi24Cp.Pc.v68, CFSG.KD.Fi24Cp.Pc.v69, CFSG.KD.Fi24Cp.Pc.v70]
theorem CFSG.KD.Fi24Cp.Pc.p69 : Nat.beq (runC AR SD 62 (ckL CFSG.KD.Fi24Cp.Pc.l71) 2 69 CFSG.KD.Fi24Cp.Pc.l69) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v71 : Nat := CFSG.KD.Fi24Cp.KV0 73
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v72 : Nat := CFSG.KD.Fi24Cp.KV0 74
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l73 : List Nat := [CFSG.KD.Fi24Cp.Pc.v62, CFSG.KD.Fi24Cp.Pc.v63, CFSG.KD.Fi24Cp.Pc.v64, CFSG.KD.Fi24Cp.Pc.v65, CFSG.KD.Fi24Cp.Pc.v66, CFSG.KD.Fi24Cp.Pc.v67, CFSG.KD.Fi24Cp.Pc.v68, CFSG.KD.Fi24Cp.Pc.v69, CFSG.KD.Fi24Cp.Pc.v70, CFSG.KD.Fi24Cp.Pc.v71, CFSG.KD.Fi24Cp.Pc.v72]
theorem CFSG.KD.Fi24Cp.Pc.p71 : Nat.beq (runC AR SD 62 (ckL CFSG.KD.Fi24Cp.Pc.l73) 2 71 CFSG.KD.Fi24Cp.Pc.l71) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v73 : Nat := CFSG.KD.Fi24Cp.KV0 75
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v74 : Nat := CFSG.KD.Fi24Cp.KV0 76
theorem CFSG.KD.Fi24Cp.Pc.f4 : Nat.beq (runC AR SD 62 (finC AR SD (nat_lit 4) 62 75) 2 73 CFSG.KD.Fi24Cp.Pc.l73) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk4 : chk (nat_lit 4) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 4) (lo := 62) (hi := 75) (m := 13) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 13) (m2 := 11) (j2 := 64) CFSG.KD.Fi24Cp.Pc.p62 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 66) CFSG.KD.Fi24Cp.Pc.p64 rfl rfl).trans ((runC_node (m := 9) (m2 := 8) (j2 := 67) (Lr := CFSG.KD.Fi24Cp.Pc.l67) ((nodeV_pow (R := AR) (D := SD) (lo := 62) (L := CFSG.KD.Fi24Cp.Pc.l66) (j := 66) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 62 CFSG.KD.Fi24Cp.Pc.l66 (SD.na.getD 66 0)) (SD.nk.getD 66 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q66_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r66)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 69) CFSG.KD.Fi24Cp.Pc.p67 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 71) CFSG.KD.Fi24Cp.Pc.p69 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 73) CFSG.KD.Fi24Cp.Pc.p71 rfl rfl)))))))).trans CFSG.KD.Fi24Cp.Pc.f4

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v75 : Nat := CFSG.KD.Fi24Cp.KV0 77
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v76 : Nat := CFSG.KD.Fi24Cp.KV0 78
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l77 : List Nat := [CFSG.KD.Fi24Cp.Pc.v75, CFSG.KD.Fi24Cp.Pc.v76]
theorem CFSG.KD.Fi24Cp.Pc.p75 : Nat.beq (runC AR SD 75 (ckL CFSG.KD.Fi24Cp.Pc.l77) 2 75 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v77 : Nat := CFSG.KD.Fi24Cp.KV0 79
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v78 : Nat := CFSG.KD.Fi24Cp.KV0 80
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l79 : List Nat := [CFSG.KD.Fi24Cp.Pc.v75, CFSG.KD.Fi24Cp.Pc.v76, CFSG.KD.Fi24Cp.Pc.v77, CFSG.KD.Fi24Cp.Pc.v78]
theorem CFSG.KD.Fi24Cp.Pc.p77 : Nat.beq (runC AR SD 75 (ckL CFSG.KD.Fi24Cp.Pc.l79) 2 77 CFSG.KD.Fi24Cp.Pc.l77) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v79 : Nat := CFSG.KD.Fi24Cp.KV0 81
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v80 : Nat := CFSG.KD.Fi24Cp.KV0 82
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l81 : List Nat := [CFSG.KD.Fi24Cp.Pc.v75, CFSG.KD.Fi24Cp.Pc.v76, CFSG.KD.Fi24Cp.Pc.v77, CFSG.KD.Fi24Cp.Pc.v78, CFSG.KD.Fi24Cp.Pc.v79, CFSG.KD.Fi24Cp.Pc.v80]
theorem CFSG.KD.Fi24Cp.Pc.p79 : Nat.beq (runC AR SD 75 (ckL CFSG.KD.Fi24Cp.Pc.l81) 2 79 CFSG.KD.Fi24Cp.Pc.l79) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v81 : Nat := CFSG.KD.Fi24Cp.KV0 83
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v82 : Nat := CFSG.KD.Fi24Cp.KV0 84
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l83 : List Nat := [CFSG.KD.Fi24Cp.Pc.v75, CFSG.KD.Fi24Cp.Pc.v76, CFSG.KD.Fi24Cp.Pc.v77, CFSG.KD.Fi24Cp.Pc.v78, CFSG.KD.Fi24Cp.Pc.v79, CFSG.KD.Fi24Cp.Pc.v80, CFSG.KD.Fi24Cp.Pc.v81, CFSG.KD.Fi24Cp.Pc.v82]
theorem CFSG.KD.Fi24Cp.Pc.p81 : Nat.beq (runC AR SD 75 (ckL CFSG.KD.Fi24Cp.Pc.l83) 2 81 CFSG.KD.Fi24Cp.Pc.l81) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v83 : Nat := CFSG.KD.Fi24Cp.KV0 85
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v84 : Nat := CFSG.KD.Fi24Cp.KV0 86
theorem CFSG.KD.Fi24Cp.Pc.f5 : Nat.beq (runC AR SD 75 (finC AR SD (nat_lit 5) 75 85) 2 83 CFSG.KD.Fi24Cp.Pc.l83) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk5 : chk (nat_lit 5) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 5) (lo := 75) (hi := 85) (m := 10) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 10) (m2 := 8) (j2 := 77) CFSG.KD.Fi24Cp.Pc.p75 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 79) CFSG.KD.Fi24Cp.Pc.p77 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 81) CFSG.KD.Fi24Cp.Pc.p79 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 83) CFSG.KD.Fi24Cp.Pc.p81 rfl rfl)))))).trans CFSG.KD.Fi24Cp.Pc.f5

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a85_3 : Nat := CFSG.KD.Fi24Cp.KV0 87
theorem CFSG.KD.Fi24Cp.Pc.q85_3 : Nat.beq (powTop AR.mul (getV AR SD 85 [] (SD.na.getD 85 0)) (SD.nk.getD 85 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a85_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a85_2 : Nat := CFSG.KD.Fi24Cp.KV0 88
theorem CFSG.KD.Fi24Cp.Pc.q85_2 : Nat.beq (powTop AR.mul (getV AR SD 85 [] (SD.na.getD 85 0)) (SD.nk.getD 85 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a85_2) 1 CFSG.KD.Fi24Cp.Pc.a85_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a85_1 : Nat := CFSG.KD.Fi24Cp.KV0 89
theorem CFSG.KD.Fi24Cp.Pc.q85_1 : Nat.beq (powTop AR.mul (getV AR SD 85 [] (SD.na.getD 85 0)) (SD.nk.getD 85 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a85_1) 1 CFSG.KD.Fi24Cp.Pc.a85_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v85 : Nat := CFSG.KD.Fi24Cp.KV0 90
theorem CFSG.KD.Fi24Cp.Pc.r85 : Nat.beq (powR AR.mul AR.one (getV AR SD 85 [] (SD.na.getD 85 0)) (SD.nk.getD 85 1) 1 CFSG.KD.Fi24Cp.Pc.a85_1 true) CFSG.KD.Fi24Cp.Pc.v85 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v86 : Nat := CFSG.KD.Fi24Cp.KV0 91
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v87 : Nat := CFSG.KD.Fi24Cp.KV0 92
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l86 : List Nat := [CFSG.KD.Fi24Cp.Pc.v85]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l88 : List Nat := [CFSG.KD.Fi24Cp.Pc.v85, CFSG.KD.Fi24Cp.Pc.v86, CFSG.KD.Fi24Cp.Pc.v87]
theorem CFSG.KD.Fi24Cp.Pc.p86 : Nat.beq (runC AR SD 85 (ckL CFSG.KD.Fi24Cp.Pc.l88) 2 86 CFSG.KD.Fi24Cp.Pc.l86) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v88 : Nat := CFSG.KD.Fi24Cp.KV0 93
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v89 : Nat := CFSG.KD.Fi24Cp.KV0 94
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l90 : List Nat := [CFSG.KD.Fi24Cp.Pc.v85, CFSG.KD.Fi24Cp.Pc.v86, CFSG.KD.Fi24Cp.Pc.v87, CFSG.KD.Fi24Cp.Pc.v88, CFSG.KD.Fi24Cp.Pc.v89]
theorem CFSG.KD.Fi24Cp.Pc.p88 : Nat.beq (runC AR SD 85 (ckL CFSG.KD.Fi24Cp.Pc.l90) 2 88 CFSG.KD.Fi24Cp.Pc.l88) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v90 : Nat := CFSG.KD.Fi24Cp.KV0 95
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v91 : Nat := CFSG.KD.Fi24Cp.KV0 96
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l92 : List Nat := [CFSG.KD.Fi24Cp.Pc.v85, CFSG.KD.Fi24Cp.Pc.v86, CFSG.KD.Fi24Cp.Pc.v87, CFSG.KD.Fi24Cp.Pc.v88, CFSG.KD.Fi24Cp.Pc.v89, CFSG.KD.Fi24Cp.Pc.v90, CFSG.KD.Fi24Cp.Pc.v91]
theorem CFSG.KD.Fi24Cp.Pc.p90 : Nat.beq (runC AR SD 85 (ckL CFSG.KD.Fi24Cp.Pc.l92) 2 90 CFSG.KD.Fi24Cp.Pc.l90) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v92 : Nat := CFSG.KD.Fi24Cp.KV0 97
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v93 : Nat := CFSG.KD.Fi24Cp.KV0 98
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l94 : List Nat := [CFSG.KD.Fi24Cp.Pc.v85, CFSG.KD.Fi24Cp.Pc.v86, CFSG.KD.Fi24Cp.Pc.v87, CFSG.KD.Fi24Cp.Pc.v88, CFSG.KD.Fi24Cp.Pc.v89, CFSG.KD.Fi24Cp.Pc.v90, CFSG.KD.Fi24Cp.Pc.v91, CFSG.KD.Fi24Cp.Pc.v92, CFSG.KD.Fi24Cp.Pc.v93]
theorem CFSG.KD.Fi24Cp.Pc.p92 : Nat.beq (runC AR SD 85 (ckL CFSG.KD.Fi24Cp.Pc.l94) 2 92 CFSG.KD.Fi24Cp.Pc.l92) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v94 : Nat := CFSG.KD.Fi24Cp.KV0 99
theorem CFSG.KD.Fi24Cp.Pc.f6 : Nat.beq (runC AR SD 85 (finC AR SD (nat_lit 6) 85 95) 1 94 CFSG.KD.Fi24Cp.Pc.l94) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk6 : chk (nat_lit 6) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 6) (lo := 85) (hi := 95) (m := 10) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 10) (m2 := 9) (j2 := 86) (Lr := CFSG.KD.Fi24Cp.Pc.l86) ((nodeV_pow (R := AR) (D := SD) (lo := 85) (L := []) (j := 85) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 85 [] (SD.na.getD 85 0)) (SD.nk.getD 85 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q85_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q85_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q85_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r85)))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 88) CFSG.KD.Fi24Cp.Pc.p86 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 90) CFSG.KD.Fi24Cp.Pc.p88 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 92) CFSG.KD.Fi24Cp.Pc.p90 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 94) CFSG.KD.Fi24Cp.Pc.p92 rfl rfl))))))).trans CFSG.KD.Fi24Cp.Pc.f6

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v95 : Nat := CFSG.KD.Fi24Cp.KV0 100
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v96 : Nat := CFSG.KD.Fi24Cp.KV0 101
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l97 : List Nat := [CFSG.KD.Fi24Cp.Pc.v95, CFSG.KD.Fi24Cp.Pc.v96]
theorem CFSG.KD.Fi24Cp.Pc.p95 : Nat.beq (runC AR SD 95 (ckL CFSG.KD.Fi24Cp.Pc.l97) 2 95 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v97 : Nat := CFSG.KD.Fi24Cp.KV0 102
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v98 : Nat := CFSG.KD.Fi24Cp.KV0 103
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l99 : List Nat := [CFSG.KD.Fi24Cp.Pc.v95, CFSG.KD.Fi24Cp.Pc.v96, CFSG.KD.Fi24Cp.Pc.v97, CFSG.KD.Fi24Cp.Pc.v98]
theorem CFSG.KD.Fi24Cp.Pc.p97 : Nat.beq (runC AR SD 95 (ckL CFSG.KD.Fi24Cp.Pc.l99) 2 97 CFSG.KD.Fi24Cp.Pc.l97) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v99 : Nat := CFSG.KD.Fi24Cp.KV0 104
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v100 : Nat := CFSG.KD.Fi24Cp.KV0 105
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l101 : List Nat := [CFSG.KD.Fi24Cp.Pc.v95, CFSG.KD.Fi24Cp.Pc.v96, CFSG.KD.Fi24Cp.Pc.v97, CFSG.KD.Fi24Cp.Pc.v98, CFSG.KD.Fi24Cp.Pc.v99, CFSG.KD.Fi24Cp.Pc.v100]
theorem CFSG.KD.Fi24Cp.Pc.p99 : Nat.beq (runC AR SD 95 (ckL CFSG.KD.Fi24Cp.Pc.l101) 2 99 CFSG.KD.Fi24Cp.Pc.l99) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v101 : Nat := CFSG.KD.Fi24Cp.KV0 106
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v102 : Nat := CFSG.KD.Fi24Cp.KV0 107
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l103 : List Nat := [CFSG.KD.Fi24Cp.Pc.v95, CFSG.KD.Fi24Cp.Pc.v96, CFSG.KD.Fi24Cp.Pc.v97, CFSG.KD.Fi24Cp.Pc.v98, CFSG.KD.Fi24Cp.Pc.v99, CFSG.KD.Fi24Cp.Pc.v100, CFSG.KD.Fi24Cp.Pc.v101, CFSG.KD.Fi24Cp.Pc.v102]
theorem CFSG.KD.Fi24Cp.Pc.p101 : Nat.beq (runC AR SD 95 (ckL CFSG.KD.Fi24Cp.Pc.l103) 2 101 CFSG.KD.Fi24Cp.Pc.l101) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v103 : Nat := CFSG.KD.Fi24Cp.KV0 108
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v104 : Nat := CFSG.KD.Fi24Cp.KV0 109
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l105 : List Nat := [CFSG.KD.Fi24Cp.Pc.v95, CFSG.KD.Fi24Cp.Pc.v96, CFSG.KD.Fi24Cp.Pc.v97, CFSG.KD.Fi24Cp.Pc.v98, CFSG.KD.Fi24Cp.Pc.v99, CFSG.KD.Fi24Cp.Pc.v100, CFSG.KD.Fi24Cp.Pc.v101, CFSG.KD.Fi24Cp.Pc.v102, CFSG.KD.Fi24Cp.Pc.v103, CFSG.KD.Fi24Cp.Pc.v104]
theorem CFSG.KD.Fi24Cp.Pc.p103 : Nat.beq (runC AR SD 95 (ckL CFSG.KD.Fi24Cp.Pc.l105) 2 103 CFSG.KD.Fi24Cp.Pc.l103) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v105 : Nat := CFSG.KD.Fi24Cp.KV0 110
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v106 : Nat := CFSG.KD.Fi24Cp.KV0 111
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l107 : List Nat := [CFSG.KD.Fi24Cp.Pc.v95, CFSG.KD.Fi24Cp.Pc.v96, CFSG.KD.Fi24Cp.Pc.v97, CFSG.KD.Fi24Cp.Pc.v98, CFSG.KD.Fi24Cp.Pc.v99, CFSG.KD.Fi24Cp.Pc.v100, CFSG.KD.Fi24Cp.Pc.v101, CFSG.KD.Fi24Cp.Pc.v102, CFSG.KD.Fi24Cp.Pc.v103, CFSG.KD.Fi24Cp.Pc.v104, CFSG.KD.Fi24Cp.Pc.v105, CFSG.KD.Fi24Cp.Pc.v106]
theorem CFSG.KD.Fi24Cp.Pc.p105 : Nat.beq (runC AR SD 95 (ckL CFSG.KD.Fi24Cp.Pc.l107) 2 105 CFSG.KD.Fi24Cp.Pc.l105) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v107 : Nat := CFSG.KD.Fi24Cp.KV0 112
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v108 : Nat := CFSG.KD.Fi24Cp.KV0 113
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l109 : List Nat := [CFSG.KD.Fi24Cp.Pc.v95, CFSG.KD.Fi24Cp.Pc.v96, CFSG.KD.Fi24Cp.Pc.v97, CFSG.KD.Fi24Cp.Pc.v98, CFSG.KD.Fi24Cp.Pc.v99, CFSG.KD.Fi24Cp.Pc.v100, CFSG.KD.Fi24Cp.Pc.v101, CFSG.KD.Fi24Cp.Pc.v102, CFSG.KD.Fi24Cp.Pc.v103, CFSG.KD.Fi24Cp.Pc.v104, CFSG.KD.Fi24Cp.Pc.v105, CFSG.KD.Fi24Cp.Pc.v106, CFSG.KD.Fi24Cp.Pc.v107, CFSG.KD.Fi24Cp.Pc.v108]
theorem CFSG.KD.Fi24Cp.Pc.p107 : Nat.beq (runC AR SD 95 (ckL CFSG.KD.Fi24Cp.Pc.l109) 2 107 CFSG.KD.Fi24Cp.Pc.l107) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v109 : Nat := CFSG.KD.Fi24Cp.KV0 114
theorem CFSG.KD.Fi24Cp.Pc.f7 : Nat.beq (runC AR SD 95 (finC AR SD (nat_lit 7) 95 110) 1 109 CFSG.KD.Fi24Cp.Pc.l109) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk7 : chk (nat_lit 7) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 7) (lo := 95) (hi := 110) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 97) CFSG.KD.Fi24Cp.Pc.p95 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 99) CFSG.KD.Fi24Cp.Pc.p97 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 101) CFSG.KD.Fi24Cp.Pc.p99 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 103) CFSG.KD.Fi24Cp.Pc.p101 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 105) CFSG.KD.Fi24Cp.Pc.p103 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 107) CFSG.KD.Fi24Cp.Pc.p105 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 109) CFSG.KD.Fi24Cp.Pc.p107 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f7

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a110_1 : Nat := CFSG.KD.Fi24Cp.KV0 115
theorem CFSG.KD.Fi24Cp.Pc.q110_1 : Nat.beq (powTop AR.mul (getV AR SD 110 [] (SD.na.getD 110 0)) (SD.nk.getD 110 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a110_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v110 : Nat := CFSG.KD.Fi24Cp.KV0 116
theorem CFSG.KD.Fi24Cp.Pc.r110 : Nat.beq (powR AR.mul AR.one (getV AR SD 110 [] (SD.na.getD 110 0)) (SD.nk.getD 110 1) 1 CFSG.KD.Fi24Cp.Pc.a110_1 true) CFSG.KD.Fi24Cp.Pc.v110 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v111 : Nat := CFSG.KD.Fi24Cp.KV0 117
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l111 : List Nat := [CFSG.KD.Fi24Cp.Pc.v110]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l112 : List Nat := [CFSG.KD.Fi24Cp.Pc.v110, CFSG.KD.Fi24Cp.Pc.v111]
theorem CFSG.KD.Fi24Cp.Pc.p111 : Nat.beq (runC AR SD 110 (ckL CFSG.KD.Fi24Cp.Pc.l112) 1 111 CFSG.KD.Fi24Cp.Pc.l111) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a112_3 : Nat := CFSG.KD.Fi24Cp.KV0 118
theorem CFSG.KD.Fi24Cp.Pc.q112_3 : Nat.beq (powTop AR.mul (getV AR SD 110 CFSG.KD.Fi24Cp.Pc.l112 (SD.na.getD 112 0)) (SD.nk.getD 112 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a112_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a112_2 : Nat := CFSG.KD.Fi24Cp.KV0 119
theorem CFSG.KD.Fi24Cp.Pc.q112_2 : Nat.beq (powTop AR.mul (getV AR SD 110 CFSG.KD.Fi24Cp.Pc.l112 (SD.na.getD 112 0)) (SD.nk.getD 112 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a112_2) 1 CFSG.KD.Fi24Cp.Pc.a112_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a112_1 : Nat := CFSG.KD.Fi24Cp.KV0 120
theorem CFSG.KD.Fi24Cp.Pc.q112_1 : Nat.beq (powTop AR.mul (getV AR SD 110 CFSG.KD.Fi24Cp.Pc.l112 (SD.na.getD 112 0)) (SD.nk.getD 112 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a112_1) 1 CFSG.KD.Fi24Cp.Pc.a112_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v112 : Nat := CFSG.KD.Fi24Cp.KV0 121
theorem CFSG.KD.Fi24Cp.Pc.r112 : Nat.beq (powR AR.mul AR.one (getV AR SD 110 CFSG.KD.Fi24Cp.Pc.l112 (SD.na.getD 112 0)) (SD.nk.getD 112 1) 1 CFSG.KD.Fi24Cp.Pc.a112_1 true) CFSG.KD.Fi24Cp.Pc.v112 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v113 : Nat := CFSG.KD.Fi24Cp.KV0 122
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v114 : Nat := CFSG.KD.Fi24Cp.KV0 123
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l113 : List Nat := [CFSG.KD.Fi24Cp.Pc.v110, CFSG.KD.Fi24Cp.Pc.v111, CFSG.KD.Fi24Cp.Pc.v112]
theorem CFSG.KD.Fi24Cp.Pc.f8 : Nat.beq (runC AR SD 110 (finC AR SD (nat_lit 8) 110 115) 2 113 CFSG.KD.Fi24Cp.Pc.l113) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk8 : chk (nat_lit 8) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 8) (lo := 110) (hi := 115) (m := 5) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 5) (m2 := 4) (j2 := 111) (Lr := CFSG.KD.Fi24Cp.Pc.l111) ((nodeV_pow (R := AR) (D := SD) (lo := 110) (L := []) (j := 110) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 110 [] (SD.na.getD 110 0)) (SD.nk.getD 110 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q110_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r110)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 4) (m2 := 3) (j2 := 112) CFSG.KD.Fi24Cp.Pc.p111 rfl rfl).trans (runC_node (m := 3) (m2 := 2) (j2 := 113) (Lr := CFSG.KD.Fi24Cp.Pc.l113) ((nodeV_pow (R := AR) (D := SD) (lo := 110) (L := CFSG.KD.Fi24Cp.Pc.l112) (j := 112) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 110 CFSG.KD.Fi24Cp.Pc.l112 (SD.na.getD 112 0)) (SD.nk.getD 112 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q112_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q112_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q112_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r112)))))) (by quickRfl) rfl rfl rfl))))).trans CFSG.KD.Fi24Cp.Pc.f8

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a115_2 : Nat := CFSG.KD.Fi24Cp.KV0 124
theorem CFSG.KD.Fi24Cp.Pc.q115_2 : Nat.beq (powTop AR.mul (getV AR SD 115 [] (SD.na.getD 115 0)) (SD.nk.getD 115 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a115_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v115 : Nat := CFSG.KD.Fi24Cp.KV0 125
theorem CFSG.KD.Fi24Cp.Pc.r115 : Nat.beq (powR AR.mul AR.one (getV AR SD 115 [] (SD.na.getD 115 0)) (SD.nk.getD 115 1) 2 CFSG.KD.Fi24Cp.Pc.a115_2 true) CFSG.KD.Fi24Cp.Pc.v115 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v116 : Nat := CFSG.KD.Fi24Cp.KV0 126
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v117 : Nat := CFSG.KD.Fi24Cp.KV0 127
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l116 : List Nat := [CFSG.KD.Fi24Cp.Pc.v115]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l118 : List Nat := [CFSG.KD.Fi24Cp.Pc.v115, CFSG.KD.Fi24Cp.Pc.v116, CFSG.KD.Fi24Cp.Pc.v117]
theorem CFSG.KD.Fi24Cp.Pc.p116 : Nat.beq (runC AR SD 115 (ckL CFSG.KD.Fi24Cp.Pc.l118) 2 116 CFSG.KD.Fi24Cp.Pc.l116) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v118 : Nat := CFSG.KD.Fi24Cp.KV0 128
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v119 : Nat := CFSG.KD.Fi24Cp.KV0 129
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l120 : List Nat := [CFSG.KD.Fi24Cp.Pc.v115, CFSG.KD.Fi24Cp.Pc.v116, CFSG.KD.Fi24Cp.Pc.v117, CFSG.KD.Fi24Cp.Pc.v118, CFSG.KD.Fi24Cp.Pc.v119]
theorem CFSG.KD.Fi24Cp.Pc.p118 : Nat.beq (runC AR SD 115 (ckL CFSG.KD.Fi24Cp.Pc.l120) 2 118 CFSG.KD.Fi24Cp.Pc.l118) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v120 : Nat := CFSG.KD.Fi24Cp.KV0 130
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v121 : Nat := CFSG.KD.Fi24Cp.KV0 131
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l122 : List Nat := [CFSG.KD.Fi24Cp.Pc.v115, CFSG.KD.Fi24Cp.Pc.v116, CFSG.KD.Fi24Cp.Pc.v117, CFSG.KD.Fi24Cp.Pc.v118, CFSG.KD.Fi24Cp.Pc.v119, CFSG.KD.Fi24Cp.Pc.v120, CFSG.KD.Fi24Cp.Pc.v121]
theorem CFSG.KD.Fi24Cp.Pc.p120 : Nat.beq (runC AR SD 115 (ckL CFSG.KD.Fi24Cp.Pc.l122) 2 120 CFSG.KD.Fi24Cp.Pc.l120) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v122 : Nat := CFSG.KD.Fi24Cp.KV0 132
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v123 : Nat := CFSG.KD.Fi24Cp.KV0 133
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l124 : List Nat := [CFSG.KD.Fi24Cp.Pc.v115, CFSG.KD.Fi24Cp.Pc.v116, CFSG.KD.Fi24Cp.Pc.v117, CFSG.KD.Fi24Cp.Pc.v118, CFSG.KD.Fi24Cp.Pc.v119, CFSG.KD.Fi24Cp.Pc.v120, CFSG.KD.Fi24Cp.Pc.v121, CFSG.KD.Fi24Cp.Pc.v122, CFSG.KD.Fi24Cp.Pc.v123]
theorem CFSG.KD.Fi24Cp.Pc.p122 : Nat.beq (runC AR SD 115 (ckL CFSG.KD.Fi24Cp.Pc.l124) 2 122 CFSG.KD.Fi24Cp.Pc.l122) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v124 : Nat := CFSG.KD.Fi24Cp.KV0 134
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v125 : Nat := CFSG.KD.Fi24Cp.KV0 135
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l126 : List Nat := [CFSG.KD.Fi24Cp.Pc.v115, CFSG.KD.Fi24Cp.Pc.v116, CFSG.KD.Fi24Cp.Pc.v117, CFSG.KD.Fi24Cp.Pc.v118, CFSG.KD.Fi24Cp.Pc.v119, CFSG.KD.Fi24Cp.Pc.v120, CFSG.KD.Fi24Cp.Pc.v121, CFSG.KD.Fi24Cp.Pc.v122, CFSG.KD.Fi24Cp.Pc.v123, CFSG.KD.Fi24Cp.Pc.v124, CFSG.KD.Fi24Cp.Pc.v125]
theorem CFSG.KD.Fi24Cp.Pc.p124 : Nat.beq (runC AR SD 115 (ckL CFSG.KD.Fi24Cp.Pc.l126) 2 124 CFSG.KD.Fi24Cp.Pc.l124) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v126 : Nat := CFSG.KD.Fi24Cp.KV0 136
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v127 : Nat := CFSG.KD.Fi24Cp.KV0 137
theorem CFSG.KD.Fi24Cp.Pc.f9 : Nat.beq (runC AR SD 115 (finC AR SD (nat_lit 9) 115 128) 2 126 CFSG.KD.Fi24Cp.Pc.l126) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk9 : chk (nat_lit 9) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 9) (lo := 115) (hi := 128) (m := 13) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 13) (m2 := 12) (j2 := 116) (Lr := CFSG.KD.Fi24Cp.Pc.l116) ((nodeV_pow (R := AR) (D := SD) (lo := 115) (L := []) (j := 115) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 115 [] (SD.na.getD 115 0)) (SD.nk.getD 115 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q115_2 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r115)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 118) CFSG.KD.Fi24Cp.Pc.p116 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 120) CFSG.KD.Fi24Cp.Pc.p118 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 122) CFSG.KD.Fi24Cp.Pc.p120 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 124) CFSG.KD.Fi24Cp.Pc.p122 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 126) CFSG.KD.Fi24Cp.Pc.p124 rfl rfl)))))))).trans CFSG.KD.Fi24Cp.Pc.f9

end
