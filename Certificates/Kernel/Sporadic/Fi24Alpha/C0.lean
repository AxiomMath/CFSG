module

public import Certificates.Kernel.Sporadic.Fi24Alpha.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Alpha KV0 "Certificates/Kernel/Sporadic/Fi24Alpha/data/v0.bin" 152491 4 21653722 6669388481796455649

public section

open CFSG.KD.Fi24Alpha CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v0 : Nat := CFSG.KD.Fi24Alpha.KV0 0
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1 : Nat := CFSG.KD.Fi24Alpha.KV0 1
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l2 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v0, CFSG.KD.Fi24Alpha.Pc.v1]
theorem CFSG.KD.Fi24Alpha.Pc.p0 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Alpha.Pc.l2) 2 0 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v2 : Nat := CFSG.KD.Fi24Alpha.KV0 2
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v3 : Nat := CFSG.KD.Fi24Alpha.KV0 3
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l4 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v0, CFSG.KD.Fi24Alpha.Pc.v1, CFSG.KD.Fi24Alpha.Pc.v2, CFSG.KD.Fi24Alpha.Pc.v3]
theorem CFSG.KD.Fi24Alpha.Pc.p2 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Alpha.Pc.l4) 2 2 CFSG.KD.Fi24Alpha.Pc.l2) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v4 : Nat := CFSG.KD.Fi24Alpha.KV0 4
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v5 : Nat := CFSG.KD.Fi24Alpha.KV0 5
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l6 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v0, CFSG.KD.Fi24Alpha.Pc.v1, CFSG.KD.Fi24Alpha.Pc.v2, CFSG.KD.Fi24Alpha.Pc.v3, CFSG.KD.Fi24Alpha.Pc.v4, CFSG.KD.Fi24Alpha.Pc.v5]
theorem CFSG.KD.Fi24Alpha.Pc.p4 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Alpha.Pc.l6) 2 4 CFSG.KD.Fi24Alpha.Pc.l4) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v6 : Nat := CFSG.KD.Fi24Alpha.KV0 6
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v7 : Nat := CFSG.KD.Fi24Alpha.KV0 7
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l8 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v0, CFSG.KD.Fi24Alpha.Pc.v1, CFSG.KD.Fi24Alpha.Pc.v2, CFSG.KD.Fi24Alpha.Pc.v3, CFSG.KD.Fi24Alpha.Pc.v4, CFSG.KD.Fi24Alpha.Pc.v5, CFSG.KD.Fi24Alpha.Pc.v6, CFSG.KD.Fi24Alpha.Pc.v7]
theorem CFSG.KD.Fi24Alpha.Pc.p6 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Alpha.Pc.l8) 2 6 CFSG.KD.Fi24Alpha.Pc.l6) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v8 : Nat := CFSG.KD.Fi24Alpha.KV0 8
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v9 : Nat := CFSG.KD.Fi24Alpha.KV0 9
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l10 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v0, CFSG.KD.Fi24Alpha.Pc.v1, CFSG.KD.Fi24Alpha.Pc.v2, CFSG.KD.Fi24Alpha.Pc.v3, CFSG.KD.Fi24Alpha.Pc.v4, CFSG.KD.Fi24Alpha.Pc.v5, CFSG.KD.Fi24Alpha.Pc.v6, CFSG.KD.Fi24Alpha.Pc.v7, CFSG.KD.Fi24Alpha.Pc.v8, CFSG.KD.Fi24Alpha.Pc.v9]
theorem CFSG.KD.Fi24Alpha.Pc.p8 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Alpha.Pc.l10) 2 8 CFSG.KD.Fi24Alpha.Pc.l8) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v10 : Nat := CFSG.KD.Fi24Alpha.KV0 10
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v11 : Nat := CFSG.KD.Fi24Alpha.KV0 11
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l12 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v0, CFSG.KD.Fi24Alpha.Pc.v1, CFSG.KD.Fi24Alpha.Pc.v2, CFSG.KD.Fi24Alpha.Pc.v3, CFSG.KD.Fi24Alpha.Pc.v4, CFSG.KD.Fi24Alpha.Pc.v5, CFSG.KD.Fi24Alpha.Pc.v6, CFSG.KD.Fi24Alpha.Pc.v7, CFSG.KD.Fi24Alpha.Pc.v8, CFSG.KD.Fi24Alpha.Pc.v9, CFSG.KD.Fi24Alpha.Pc.v10, CFSG.KD.Fi24Alpha.Pc.v11]
theorem CFSG.KD.Fi24Alpha.Pc.p10 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Alpha.Pc.l12) 2 10 CFSG.KD.Fi24Alpha.Pc.l10) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v12 : Nat := CFSG.KD.Fi24Alpha.KV0 12
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v13 : Nat := CFSG.KD.Fi24Alpha.KV0 13
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l14 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v0, CFSG.KD.Fi24Alpha.Pc.v1, CFSG.KD.Fi24Alpha.Pc.v2, CFSG.KD.Fi24Alpha.Pc.v3, CFSG.KD.Fi24Alpha.Pc.v4, CFSG.KD.Fi24Alpha.Pc.v5, CFSG.KD.Fi24Alpha.Pc.v6, CFSG.KD.Fi24Alpha.Pc.v7, CFSG.KD.Fi24Alpha.Pc.v8, CFSG.KD.Fi24Alpha.Pc.v9, CFSG.KD.Fi24Alpha.Pc.v10, CFSG.KD.Fi24Alpha.Pc.v11, CFSG.KD.Fi24Alpha.Pc.v12, CFSG.KD.Fi24Alpha.Pc.v13]
theorem CFSG.KD.Fi24Alpha.Pc.p12 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Alpha.Pc.l14) 2 12 CFSG.KD.Fi24Alpha.Pc.l12) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v14 : Nat := CFSG.KD.Fi24Alpha.KV0 14
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v15 : Nat := CFSG.KD.Fi24Alpha.KV0 15
theorem CFSG.KD.Fi24Alpha.Pc.f0 : Nat.beq (runC AR SD 0 (finC AR SD (nat_lit 0) 0 16) 2 14 CFSG.KD.Fi24Alpha.Pc.l14) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk0 : chk (nat_lit 0) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 0) (lo := 0) (hi := 16) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 2) CFSG.KD.Fi24Alpha.Pc.p0 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 4) CFSG.KD.Fi24Alpha.Pc.p2 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 6) CFSG.KD.Fi24Alpha.Pc.p4 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 8) CFSG.KD.Fi24Alpha.Pc.p6 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 10) CFSG.KD.Fi24Alpha.Pc.p8 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 12) CFSG.KD.Fi24Alpha.Pc.p10 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 14) CFSG.KD.Fi24Alpha.Pc.p12 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f0

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v16 : Nat := CFSG.KD.Fi24Alpha.KV0 16
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v17 : Nat := CFSG.KD.Fi24Alpha.KV0 17
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l18 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v16, CFSG.KD.Fi24Alpha.Pc.v17]
theorem CFSG.KD.Fi24Alpha.Pc.p16 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Alpha.Pc.l18) 2 16 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v18 : Nat := CFSG.KD.Fi24Alpha.KV0 18
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v19 : Nat := CFSG.KD.Fi24Alpha.KV0 19
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l20 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v16, CFSG.KD.Fi24Alpha.Pc.v17, CFSG.KD.Fi24Alpha.Pc.v18, CFSG.KD.Fi24Alpha.Pc.v19]
theorem CFSG.KD.Fi24Alpha.Pc.p18 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Alpha.Pc.l20) 2 18 CFSG.KD.Fi24Alpha.Pc.l18) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v20 : Nat := CFSG.KD.Fi24Alpha.KV0 20
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v21 : Nat := CFSG.KD.Fi24Alpha.KV0 21
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l22 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v16, CFSG.KD.Fi24Alpha.Pc.v17, CFSG.KD.Fi24Alpha.Pc.v18, CFSG.KD.Fi24Alpha.Pc.v19, CFSG.KD.Fi24Alpha.Pc.v20, CFSG.KD.Fi24Alpha.Pc.v21]
theorem CFSG.KD.Fi24Alpha.Pc.p20 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Alpha.Pc.l22) 2 20 CFSG.KD.Fi24Alpha.Pc.l20) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v22 : Nat := CFSG.KD.Fi24Alpha.KV0 22
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v23 : Nat := CFSG.KD.Fi24Alpha.KV0 23
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l24 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v16, CFSG.KD.Fi24Alpha.Pc.v17, CFSG.KD.Fi24Alpha.Pc.v18, CFSG.KD.Fi24Alpha.Pc.v19, CFSG.KD.Fi24Alpha.Pc.v20, CFSG.KD.Fi24Alpha.Pc.v21, CFSG.KD.Fi24Alpha.Pc.v22, CFSG.KD.Fi24Alpha.Pc.v23]
theorem CFSG.KD.Fi24Alpha.Pc.p22 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Alpha.Pc.l24) 2 22 CFSG.KD.Fi24Alpha.Pc.l22) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v24 : Nat := CFSG.KD.Fi24Alpha.KV0 24
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v25 : Nat := CFSG.KD.Fi24Alpha.KV0 25
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l26 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v16, CFSG.KD.Fi24Alpha.Pc.v17, CFSG.KD.Fi24Alpha.Pc.v18, CFSG.KD.Fi24Alpha.Pc.v19, CFSG.KD.Fi24Alpha.Pc.v20, CFSG.KD.Fi24Alpha.Pc.v21, CFSG.KD.Fi24Alpha.Pc.v22, CFSG.KD.Fi24Alpha.Pc.v23, CFSG.KD.Fi24Alpha.Pc.v24, CFSG.KD.Fi24Alpha.Pc.v25]
theorem CFSG.KD.Fi24Alpha.Pc.p24 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Alpha.Pc.l26) 2 24 CFSG.KD.Fi24Alpha.Pc.l24) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v26 : Nat := CFSG.KD.Fi24Alpha.KV0 26
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v27 : Nat := CFSG.KD.Fi24Alpha.KV0 27
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l28 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v16, CFSG.KD.Fi24Alpha.Pc.v17, CFSG.KD.Fi24Alpha.Pc.v18, CFSG.KD.Fi24Alpha.Pc.v19, CFSG.KD.Fi24Alpha.Pc.v20, CFSG.KD.Fi24Alpha.Pc.v21, CFSG.KD.Fi24Alpha.Pc.v22, CFSG.KD.Fi24Alpha.Pc.v23, CFSG.KD.Fi24Alpha.Pc.v24, CFSG.KD.Fi24Alpha.Pc.v25, CFSG.KD.Fi24Alpha.Pc.v26, CFSG.KD.Fi24Alpha.Pc.v27]
theorem CFSG.KD.Fi24Alpha.Pc.p26 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Alpha.Pc.l28) 2 26 CFSG.KD.Fi24Alpha.Pc.l26) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v28 : Nat := CFSG.KD.Fi24Alpha.KV0 28
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v29 : Nat := CFSG.KD.Fi24Alpha.KV0 29
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l30 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v16, CFSG.KD.Fi24Alpha.Pc.v17, CFSG.KD.Fi24Alpha.Pc.v18, CFSG.KD.Fi24Alpha.Pc.v19, CFSG.KD.Fi24Alpha.Pc.v20, CFSG.KD.Fi24Alpha.Pc.v21, CFSG.KD.Fi24Alpha.Pc.v22, CFSG.KD.Fi24Alpha.Pc.v23, CFSG.KD.Fi24Alpha.Pc.v24, CFSG.KD.Fi24Alpha.Pc.v25, CFSG.KD.Fi24Alpha.Pc.v26, CFSG.KD.Fi24Alpha.Pc.v27, CFSG.KD.Fi24Alpha.Pc.v28, CFSG.KD.Fi24Alpha.Pc.v29]
theorem CFSG.KD.Fi24Alpha.Pc.p28 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Alpha.Pc.l30) 2 28 CFSG.KD.Fi24Alpha.Pc.l28) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v30 : Nat := CFSG.KD.Fi24Alpha.KV0 30
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v31 : Nat := CFSG.KD.Fi24Alpha.KV0 31
theorem CFSG.KD.Fi24Alpha.Pc.f1 : Nat.beq (runC AR SD 16 (finC AR SD (nat_lit 1) 16 32) 2 30 CFSG.KD.Fi24Alpha.Pc.l30) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk1 : chk (nat_lit 1) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 1) (lo := 16) (hi := 32) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 18) CFSG.KD.Fi24Alpha.Pc.p16 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 20) CFSG.KD.Fi24Alpha.Pc.p18 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 22) CFSG.KD.Fi24Alpha.Pc.p20 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 24) CFSG.KD.Fi24Alpha.Pc.p22 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 26) CFSG.KD.Fi24Alpha.Pc.p24 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 28) CFSG.KD.Fi24Alpha.Pc.p26 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 30) CFSG.KD.Fi24Alpha.Pc.p28 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f1

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v32 : Nat := CFSG.KD.Fi24Alpha.KV0 32
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v33 : Nat := CFSG.KD.Fi24Alpha.KV0 33
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l34 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v32, CFSG.KD.Fi24Alpha.Pc.v33]
theorem CFSG.KD.Fi24Alpha.Pc.p32 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Alpha.Pc.l34) 2 32 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v34 : Nat := CFSG.KD.Fi24Alpha.KV0 34
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v35 : Nat := CFSG.KD.Fi24Alpha.KV0 35
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l36 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v32, CFSG.KD.Fi24Alpha.Pc.v33, CFSG.KD.Fi24Alpha.Pc.v34, CFSG.KD.Fi24Alpha.Pc.v35]
theorem CFSG.KD.Fi24Alpha.Pc.p34 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Alpha.Pc.l36) 2 34 CFSG.KD.Fi24Alpha.Pc.l34) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v36 : Nat := CFSG.KD.Fi24Alpha.KV0 36
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v37 : Nat := CFSG.KD.Fi24Alpha.KV0 37
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l38 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v32, CFSG.KD.Fi24Alpha.Pc.v33, CFSG.KD.Fi24Alpha.Pc.v34, CFSG.KD.Fi24Alpha.Pc.v35, CFSG.KD.Fi24Alpha.Pc.v36, CFSG.KD.Fi24Alpha.Pc.v37]
theorem CFSG.KD.Fi24Alpha.Pc.p36 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Alpha.Pc.l38) 2 36 CFSG.KD.Fi24Alpha.Pc.l36) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v38 : Nat := CFSG.KD.Fi24Alpha.KV0 38
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v39 : Nat := CFSG.KD.Fi24Alpha.KV0 39
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l40 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v32, CFSG.KD.Fi24Alpha.Pc.v33, CFSG.KD.Fi24Alpha.Pc.v34, CFSG.KD.Fi24Alpha.Pc.v35, CFSG.KD.Fi24Alpha.Pc.v36, CFSG.KD.Fi24Alpha.Pc.v37, CFSG.KD.Fi24Alpha.Pc.v38, CFSG.KD.Fi24Alpha.Pc.v39]
theorem CFSG.KD.Fi24Alpha.Pc.p38 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Alpha.Pc.l40) 2 38 CFSG.KD.Fi24Alpha.Pc.l38) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v40 : Nat := CFSG.KD.Fi24Alpha.KV0 40
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v41 : Nat := CFSG.KD.Fi24Alpha.KV0 41
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l42 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v32, CFSG.KD.Fi24Alpha.Pc.v33, CFSG.KD.Fi24Alpha.Pc.v34, CFSG.KD.Fi24Alpha.Pc.v35, CFSG.KD.Fi24Alpha.Pc.v36, CFSG.KD.Fi24Alpha.Pc.v37, CFSG.KD.Fi24Alpha.Pc.v38, CFSG.KD.Fi24Alpha.Pc.v39, CFSG.KD.Fi24Alpha.Pc.v40, CFSG.KD.Fi24Alpha.Pc.v41]
theorem CFSG.KD.Fi24Alpha.Pc.p40 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Alpha.Pc.l42) 2 40 CFSG.KD.Fi24Alpha.Pc.l40) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v42 : Nat := CFSG.KD.Fi24Alpha.KV0 42
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v43 : Nat := CFSG.KD.Fi24Alpha.KV0 43
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l44 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v32, CFSG.KD.Fi24Alpha.Pc.v33, CFSG.KD.Fi24Alpha.Pc.v34, CFSG.KD.Fi24Alpha.Pc.v35, CFSG.KD.Fi24Alpha.Pc.v36, CFSG.KD.Fi24Alpha.Pc.v37, CFSG.KD.Fi24Alpha.Pc.v38, CFSG.KD.Fi24Alpha.Pc.v39, CFSG.KD.Fi24Alpha.Pc.v40, CFSG.KD.Fi24Alpha.Pc.v41, CFSG.KD.Fi24Alpha.Pc.v42, CFSG.KD.Fi24Alpha.Pc.v43]
theorem CFSG.KD.Fi24Alpha.Pc.p42 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Alpha.Pc.l44) 2 42 CFSG.KD.Fi24Alpha.Pc.l42) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v44 : Nat := CFSG.KD.Fi24Alpha.KV0 44
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v45 : Nat := CFSG.KD.Fi24Alpha.KV0 45
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l46 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v32, CFSG.KD.Fi24Alpha.Pc.v33, CFSG.KD.Fi24Alpha.Pc.v34, CFSG.KD.Fi24Alpha.Pc.v35, CFSG.KD.Fi24Alpha.Pc.v36, CFSG.KD.Fi24Alpha.Pc.v37, CFSG.KD.Fi24Alpha.Pc.v38, CFSG.KD.Fi24Alpha.Pc.v39, CFSG.KD.Fi24Alpha.Pc.v40, CFSG.KD.Fi24Alpha.Pc.v41, CFSG.KD.Fi24Alpha.Pc.v42, CFSG.KD.Fi24Alpha.Pc.v43, CFSG.KD.Fi24Alpha.Pc.v44, CFSG.KD.Fi24Alpha.Pc.v45]
theorem CFSG.KD.Fi24Alpha.Pc.p44 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Alpha.Pc.l46) 2 44 CFSG.KD.Fi24Alpha.Pc.l44) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v46 : Nat := CFSG.KD.Fi24Alpha.KV0 46
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v47 : Nat := CFSG.KD.Fi24Alpha.KV0 47
theorem CFSG.KD.Fi24Alpha.Pc.f2 : Nat.beq (runC AR SD 32 (finC AR SD (nat_lit 2) 32 48) 2 46 CFSG.KD.Fi24Alpha.Pc.l46) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk2 : chk (nat_lit 2) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 2) (lo := 32) (hi := 48) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 34) CFSG.KD.Fi24Alpha.Pc.p32 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 36) CFSG.KD.Fi24Alpha.Pc.p34 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 38) CFSG.KD.Fi24Alpha.Pc.p36 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 40) CFSG.KD.Fi24Alpha.Pc.p38 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 42) CFSG.KD.Fi24Alpha.Pc.p40 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 44) CFSG.KD.Fi24Alpha.Pc.p42 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 46) CFSG.KD.Fi24Alpha.Pc.p44 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f2

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v48 : Nat := CFSG.KD.Fi24Alpha.KV0 48
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v49 : Nat := CFSG.KD.Fi24Alpha.KV0 49
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l50 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v48, CFSG.KD.Fi24Alpha.Pc.v49]
theorem CFSG.KD.Fi24Alpha.Pc.p48 : Nat.beq (runC AR SD 48 (ckL CFSG.KD.Fi24Alpha.Pc.l50) 2 48 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v50 : Nat := CFSG.KD.Fi24Alpha.KV0 50
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v51 : Nat := CFSG.KD.Fi24Alpha.KV0 51
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l52 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v48, CFSG.KD.Fi24Alpha.Pc.v49, CFSG.KD.Fi24Alpha.Pc.v50, CFSG.KD.Fi24Alpha.Pc.v51]
theorem CFSG.KD.Fi24Alpha.Pc.p50 : Nat.beq (runC AR SD 48 (ckL CFSG.KD.Fi24Alpha.Pc.l52) 2 50 CFSG.KD.Fi24Alpha.Pc.l50) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v52 : Nat := CFSG.KD.Fi24Alpha.KV0 52
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v53 : Nat := CFSG.KD.Fi24Alpha.KV0 53
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l54 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v48, CFSG.KD.Fi24Alpha.Pc.v49, CFSG.KD.Fi24Alpha.Pc.v50, CFSG.KD.Fi24Alpha.Pc.v51, CFSG.KD.Fi24Alpha.Pc.v52, CFSG.KD.Fi24Alpha.Pc.v53]
theorem CFSG.KD.Fi24Alpha.Pc.p52 : Nat.beq (runC AR SD 48 (ckL CFSG.KD.Fi24Alpha.Pc.l54) 2 52 CFSG.KD.Fi24Alpha.Pc.l52) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v54 : Nat := CFSG.KD.Fi24Alpha.KV0 54
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v55 : Nat := CFSG.KD.Fi24Alpha.KV0 55
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l56 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v48, CFSG.KD.Fi24Alpha.Pc.v49, CFSG.KD.Fi24Alpha.Pc.v50, CFSG.KD.Fi24Alpha.Pc.v51, CFSG.KD.Fi24Alpha.Pc.v52, CFSG.KD.Fi24Alpha.Pc.v53, CFSG.KD.Fi24Alpha.Pc.v54, CFSG.KD.Fi24Alpha.Pc.v55]
theorem CFSG.KD.Fi24Alpha.Pc.p54 : Nat.beq (runC AR SD 48 (ckL CFSG.KD.Fi24Alpha.Pc.l56) 2 54 CFSG.KD.Fi24Alpha.Pc.l54) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v56 : Nat := CFSG.KD.Fi24Alpha.KV0 56
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v57 : Nat := CFSG.KD.Fi24Alpha.KV0 57
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l58 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v48, CFSG.KD.Fi24Alpha.Pc.v49, CFSG.KD.Fi24Alpha.Pc.v50, CFSG.KD.Fi24Alpha.Pc.v51, CFSG.KD.Fi24Alpha.Pc.v52, CFSG.KD.Fi24Alpha.Pc.v53, CFSG.KD.Fi24Alpha.Pc.v54, CFSG.KD.Fi24Alpha.Pc.v55, CFSG.KD.Fi24Alpha.Pc.v56, CFSG.KD.Fi24Alpha.Pc.v57]
theorem CFSG.KD.Fi24Alpha.Pc.p56 : Nat.beq (runC AR SD 48 (ckL CFSG.KD.Fi24Alpha.Pc.l58) 2 56 CFSG.KD.Fi24Alpha.Pc.l56) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v58 : Nat := CFSG.KD.Fi24Alpha.KV0 58
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v59 : Nat := CFSG.KD.Fi24Alpha.KV0 59
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l60 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v48, CFSG.KD.Fi24Alpha.Pc.v49, CFSG.KD.Fi24Alpha.Pc.v50, CFSG.KD.Fi24Alpha.Pc.v51, CFSG.KD.Fi24Alpha.Pc.v52, CFSG.KD.Fi24Alpha.Pc.v53, CFSG.KD.Fi24Alpha.Pc.v54, CFSG.KD.Fi24Alpha.Pc.v55, CFSG.KD.Fi24Alpha.Pc.v56, CFSG.KD.Fi24Alpha.Pc.v57, CFSG.KD.Fi24Alpha.Pc.v58, CFSG.KD.Fi24Alpha.Pc.v59]
theorem CFSG.KD.Fi24Alpha.Pc.p58 : Nat.beq (runC AR SD 48 (ckL CFSG.KD.Fi24Alpha.Pc.l60) 2 58 CFSG.KD.Fi24Alpha.Pc.l58) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v60 : Nat := CFSG.KD.Fi24Alpha.KV0 60
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v61 : Nat := CFSG.KD.Fi24Alpha.KV0 61
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l62 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v48, CFSG.KD.Fi24Alpha.Pc.v49, CFSG.KD.Fi24Alpha.Pc.v50, CFSG.KD.Fi24Alpha.Pc.v51, CFSG.KD.Fi24Alpha.Pc.v52, CFSG.KD.Fi24Alpha.Pc.v53, CFSG.KD.Fi24Alpha.Pc.v54, CFSG.KD.Fi24Alpha.Pc.v55, CFSG.KD.Fi24Alpha.Pc.v56, CFSG.KD.Fi24Alpha.Pc.v57, CFSG.KD.Fi24Alpha.Pc.v58, CFSG.KD.Fi24Alpha.Pc.v59, CFSG.KD.Fi24Alpha.Pc.v60, CFSG.KD.Fi24Alpha.Pc.v61]
theorem CFSG.KD.Fi24Alpha.Pc.p60 : Nat.beq (runC AR SD 48 (ckL CFSG.KD.Fi24Alpha.Pc.l62) 2 60 CFSG.KD.Fi24Alpha.Pc.l60) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v62 : Nat := CFSG.KD.Fi24Alpha.KV0 62
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v63 : Nat := CFSG.KD.Fi24Alpha.KV0 63
theorem CFSG.KD.Fi24Alpha.Pc.f3 : Nat.beq (runC AR SD 48 (finC AR SD (nat_lit 3) 48 64) 2 62 CFSG.KD.Fi24Alpha.Pc.l62) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk3 : chk (nat_lit 3) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 3) (lo := 48) (hi := 64) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 50) CFSG.KD.Fi24Alpha.Pc.p48 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 52) CFSG.KD.Fi24Alpha.Pc.p50 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 54) CFSG.KD.Fi24Alpha.Pc.p52 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 56) CFSG.KD.Fi24Alpha.Pc.p54 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 58) CFSG.KD.Fi24Alpha.Pc.p56 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 60) CFSG.KD.Fi24Alpha.Pc.p58 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 62) CFSG.KD.Fi24Alpha.Pc.p60 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f3

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v64 : Nat := CFSG.KD.Fi24Alpha.KV0 64
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v65 : Nat := CFSG.KD.Fi24Alpha.KV0 65
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l66 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v64, CFSG.KD.Fi24Alpha.Pc.v65]
theorem CFSG.KD.Fi24Alpha.Pc.p64 : Nat.beq (runC AR SD 64 (ckL CFSG.KD.Fi24Alpha.Pc.l66) 2 64 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a66_3 : Nat := CFSG.KD.Fi24Alpha.KV0 66
theorem CFSG.KD.Fi24Alpha.Pc.q66_3 : Nat.beq (powTop AR.mul (getV AR SD 64 CFSG.KD.Fi24Alpha.Pc.l66 (SD.na.getD 66 0)) (SD.nk.getD 66 1) 3 (ckP CFSG.KD.Fi24Alpha.Pc.a66_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a66_2 : Nat := CFSG.KD.Fi24Alpha.KV0 67
theorem CFSG.KD.Fi24Alpha.Pc.q66_2 : Nat.beq (powTop AR.mul (getV AR SD 64 CFSG.KD.Fi24Alpha.Pc.l66 (SD.na.getD 66 0)) (SD.nk.getD 66 1) 2 (ckP CFSG.KD.Fi24Alpha.Pc.a66_2) 1 CFSG.KD.Fi24Alpha.Pc.a66_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a66_1 : Nat := CFSG.KD.Fi24Alpha.KV0 68
theorem CFSG.KD.Fi24Alpha.Pc.q66_1 : Nat.beq (powTop AR.mul (getV AR SD 64 CFSG.KD.Fi24Alpha.Pc.l66 (SD.na.getD 66 0)) (SD.nk.getD 66 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a66_1) 1 CFSG.KD.Fi24Alpha.Pc.a66_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v66 : Nat := CFSG.KD.Fi24Alpha.KV0 69
theorem CFSG.KD.Fi24Alpha.Pc.r66 : Nat.beq (powR AR.mul AR.one (getV AR SD 64 CFSG.KD.Fi24Alpha.Pc.l66 (SD.na.getD 66 0)) (SD.nk.getD 66 1) 1 CFSG.KD.Fi24Alpha.Pc.a66_1 true) CFSG.KD.Fi24Alpha.Pc.v66 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v67 : Nat := CFSG.KD.Fi24Alpha.KV0 70
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v68 : Nat := CFSG.KD.Fi24Alpha.KV0 71
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l67 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v64, CFSG.KD.Fi24Alpha.Pc.v65, CFSG.KD.Fi24Alpha.Pc.v66]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l69 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v64, CFSG.KD.Fi24Alpha.Pc.v65, CFSG.KD.Fi24Alpha.Pc.v66, CFSG.KD.Fi24Alpha.Pc.v67, CFSG.KD.Fi24Alpha.Pc.v68]
theorem CFSG.KD.Fi24Alpha.Pc.p67 : Nat.beq (runC AR SD 64 (ckL CFSG.KD.Fi24Alpha.Pc.l69) 2 67 CFSG.KD.Fi24Alpha.Pc.l67) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v69 : Nat := CFSG.KD.Fi24Alpha.KV0 72
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v70 : Nat := CFSG.KD.Fi24Alpha.KV0 73
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l71 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v64, CFSG.KD.Fi24Alpha.Pc.v65, CFSG.KD.Fi24Alpha.Pc.v66, CFSG.KD.Fi24Alpha.Pc.v67, CFSG.KD.Fi24Alpha.Pc.v68, CFSG.KD.Fi24Alpha.Pc.v69, CFSG.KD.Fi24Alpha.Pc.v70]
theorem CFSG.KD.Fi24Alpha.Pc.p69 : Nat.beq (runC AR SD 64 (ckL CFSG.KD.Fi24Alpha.Pc.l71) 2 69 CFSG.KD.Fi24Alpha.Pc.l69) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v71 : Nat := CFSG.KD.Fi24Alpha.KV0 74
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v72 : Nat := CFSG.KD.Fi24Alpha.KV0 75
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l73 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v64, CFSG.KD.Fi24Alpha.Pc.v65, CFSG.KD.Fi24Alpha.Pc.v66, CFSG.KD.Fi24Alpha.Pc.v67, CFSG.KD.Fi24Alpha.Pc.v68, CFSG.KD.Fi24Alpha.Pc.v69, CFSG.KD.Fi24Alpha.Pc.v70, CFSG.KD.Fi24Alpha.Pc.v71, CFSG.KD.Fi24Alpha.Pc.v72]
theorem CFSG.KD.Fi24Alpha.Pc.p71 : Nat.beq (runC AR SD 64 (ckL CFSG.KD.Fi24Alpha.Pc.l73) 2 71 CFSG.KD.Fi24Alpha.Pc.l71) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v73 : Nat := CFSG.KD.Fi24Alpha.KV0 76
theorem CFSG.KD.Fi24Alpha.Pc.f4 : Nat.beq (runC AR SD 64 (finC AR SD (nat_lit 4) 64 74) 1 73 CFSG.KD.Fi24Alpha.Pc.l73) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk4 : chk (nat_lit 4) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 4) (lo := 64) (hi := 74) (m := 10) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 10) (m2 := 8) (j2 := 66) CFSG.KD.Fi24Alpha.Pc.p64 rfl rfl).trans ((runC_node (m := 8) (m2 := 7) (j2 := 67) (Lr := CFSG.KD.Fi24Alpha.Pc.l67) ((nodeV_pow (R := AR) (D := SD) (lo := 64) (L := CFSG.KD.Fi24Alpha.Pc.l66) (j := 66) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 64 CFSG.KD.Fi24Alpha.Pc.l66 (SD.na.getD 66 0)) (SD.nk.getD 66 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q66_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Alpha.Pc.q66_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Alpha.Pc.q66_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r66)))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 69) CFSG.KD.Fi24Alpha.Pc.p67 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 71) CFSG.KD.Fi24Alpha.Pc.p69 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 73) CFSG.KD.Fi24Alpha.Pc.p71 rfl rfl))))))).trans CFSG.KD.Fi24Alpha.Pc.f4

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v74 : Nat := CFSG.KD.Fi24Alpha.KV0 77
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l75 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v74]
theorem CFSG.KD.Fi24Alpha.Pc.p74 : Nat.beq (runC AR SD 74 (ckL CFSG.KD.Fi24Alpha.Pc.l75) 1 74 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a75_3 : Nat := CFSG.KD.Fi24Alpha.KV0 78
theorem CFSG.KD.Fi24Alpha.Pc.q75_3 : Nat.beq (powTop AR.mul (getV AR SD 74 CFSG.KD.Fi24Alpha.Pc.l75 (SD.na.getD 75 0)) (SD.nk.getD 75 1) 3 (ckP CFSG.KD.Fi24Alpha.Pc.a75_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a75_2 : Nat := CFSG.KD.Fi24Alpha.KV0 79
theorem CFSG.KD.Fi24Alpha.Pc.q75_2 : Nat.beq (powTop AR.mul (getV AR SD 74 CFSG.KD.Fi24Alpha.Pc.l75 (SD.na.getD 75 0)) (SD.nk.getD 75 1) 2 (ckP CFSG.KD.Fi24Alpha.Pc.a75_2) 1 CFSG.KD.Fi24Alpha.Pc.a75_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a75_1 : Nat := CFSG.KD.Fi24Alpha.KV0 80
theorem CFSG.KD.Fi24Alpha.Pc.q75_1 : Nat.beq (powTop AR.mul (getV AR SD 74 CFSG.KD.Fi24Alpha.Pc.l75 (SD.na.getD 75 0)) (SD.nk.getD 75 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a75_1) 1 CFSG.KD.Fi24Alpha.Pc.a75_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v75 : Nat := CFSG.KD.Fi24Alpha.KV0 81
theorem CFSG.KD.Fi24Alpha.Pc.r75 : Nat.beq (powR AR.mul AR.one (getV AR SD 74 CFSG.KD.Fi24Alpha.Pc.l75 (SD.na.getD 75 0)) (SD.nk.getD 75 1) 1 CFSG.KD.Fi24Alpha.Pc.a75_1 true) CFSG.KD.Fi24Alpha.Pc.v75 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v76 : Nat := CFSG.KD.Fi24Alpha.KV0 82
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v77 : Nat := CFSG.KD.Fi24Alpha.KV0 83
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l76 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v74, CFSG.KD.Fi24Alpha.Pc.v75]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l78 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v74, CFSG.KD.Fi24Alpha.Pc.v75, CFSG.KD.Fi24Alpha.Pc.v76, CFSG.KD.Fi24Alpha.Pc.v77]
theorem CFSG.KD.Fi24Alpha.Pc.p76 : Nat.beq (runC AR SD 74 (ckL CFSG.KD.Fi24Alpha.Pc.l78) 2 76 CFSG.KD.Fi24Alpha.Pc.l76) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v78 : Nat := CFSG.KD.Fi24Alpha.KV0 84
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v79 : Nat := CFSG.KD.Fi24Alpha.KV0 85
theorem CFSG.KD.Fi24Alpha.Pc.f5 : Nat.beq (runC AR SD 74 (finC AR SD (nat_lit 5) 74 80) 2 78 CFSG.KD.Fi24Alpha.Pc.l78) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk5 : chk (nat_lit 5) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 5) (lo := 74) (hi := 80) (m := 6) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 6) (m2 := 5) (j2 := 75) CFSG.KD.Fi24Alpha.Pc.p74 rfl rfl).trans ((runC_node (m := 5) (m2 := 4) (j2 := 76) (Lr := CFSG.KD.Fi24Alpha.Pc.l76) ((nodeV_pow (R := AR) (D := SD) (lo := 74) (L := CFSG.KD.Fi24Alpha.Pc.l75) (j := 75) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 74 CFSG.KD.Fi24Alpha.Pc.l75 (SD.na.getD 75 0)) (SD.nk.getD 75 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q75_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Alpha.Pc.q75_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Alpha.Pc.q75_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r75)))))) (by quickRfl) rfl rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 78) CFSG.KD.Fi24Alpha.Pc.p76 rfl rfl))))).trans CFSG.KD.Fi24Alpha.Pc.f5

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a80_3 : Nat := CFSG.KD.Fi24Alpha.KV0 86
theorem CFSG.KD.Fi24Alpha.Pc.q80_3 : Nat.beq (powTop AR.mul (getV AR SD 80 [] (SD.na.getD 80 0)) (SD.nk.getD 80 1) 3 (ckP CFSG.KD.Fi24Alpha.Pc.a80_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a80_2 : Nat := CFSG.KD.Fi24Alpha.KV0 87
theorem CFSG.KD.Fi24Alpha.Pc.q80_2 : Nat.beq (powTop AR.mul (getV AR SD 80 [] (SD.na.getD 80 0)) (SD.nk.getD 80 1) 2 (ckP CFSG.KD.Fi24Alpha.Pc.a80_2) 1 CFSG.KD.Fi24Alpha.Pc.a80_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a80_1 : Nat := CFSG.KD.Fi24Alpha.KV0 88
theorem CFSG.KD.Fi24Alpha.Pc.q80_1 : Nat.beq (powTop AR.mul (getV AR SD 80 [] (SD.na.getD 80 0)) (SD.nk.getD 80 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a80_1) 1 CFSG.KD.Fi24Alpha.Pc.a80_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v80 : Nat := CFSG.KD.Fi24Alpha.KV0 89
theorem CFSG.KD.Fi24Alpha.Pc.r80 : Nat.beq (powR AR.mul AR.one (getV AR SD 80 [] (SD.na.getD 80 0)) (SD.nk.getD 80 1) 1 CFSG.KD.Fi24Alpha.Pc.a80_1 true) CFSG.KD.Fi24Alpha.Pc.v80 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v81 : Nat := CFSG.KD.Fi24Alpha.KV0 90
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v82 : Nat := CFSG.KD.Fi24Alpha.KV0 91
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l81 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v80]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l83 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v80, CFSG.KD.Fi24Alpha.Pc.v81, CFSG.KD.Fi24Alpha.Pc.v82]
theorem CFSG.KD.Fi24Alpha.Pc.p81 : Nat.beq (runC AR SD 80 (ckL CFSG.KD.Fi24Alpha.Pc.l83) 2 81 CFSG.KD.Fi24Alpha.Pc.l81) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v83 : Nat := CFSG.KD.Fi24Alpha.KV0 92
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v84 : Nat := CFSG.KD.Fi24Alpha.KV0 93
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l85 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v80, CFSG.KD.Fi24Alpha.Pc.v81, CFSG.KD.Fi24Alpha.Pc.v82, CFSG.KD.Fi24Alpha.Pc.v83, CFSG.KD.Fi24Alpha.Pc.v84]
theorem CFSG.KD.Fi24Alpha.Pc.p83 : Nat.beq (runC AR SD 80 (ckL CFSG.KD.Fi24Alpha.Pc.l85) 2 83 CFSG.KD.Fi24Alpha.Pc.l83) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v85 : Nat := CFSG.KD.Fi24Alpha.KV0 94
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v86 : Nat := CFSG.KD.Fi24Alpha.KV0 95
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l87 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v80, CFSG.KD.Fi24Alpha.Pc.v81, CFSG.KD.Fi24Alpha.Pc.v82, CFSG.KD.Fi24Alpha.Pc.v83, CFSG.KD.Fi24Alpha.Pc.v84, CFSG.KD.Fi24Alpha.Pc.v85, CFSG.KD.Fi24Alpha.Pc.v86]
theorem CFSG.KD.Fi24Alpha.Pc.p85 : Nat.beq (runC AR SD 80 (ckL CFSG.KD.Fi24Alpha.Pc.l87) 2 85 CFSG.KD.Fi24Alpha.Pc.l85) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v87 : Nat := CFSG.KD.Fi24Alpha.KV0 96
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v88 : Nat := CFSG.KD.Fi24Alpha.KV0 97
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l89 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v80, CFSG.KD.Fi24Alpha.Pc.v81, CFSG.KD.Fi24Alpha.Pc.v82, CFSG.KD.Fi24Alpha.Pc.v83, CFSG.KD.Fi24Alpha.Pc.v84, CFSG.KD.Fi24Alpha.Pc.v85, CFSG.KD.Fi24Alpha.Pc.v86, CFSG.KD.Fi24Alpha.Pc.v87, CFSG.KD.Fi24Alpha.Pc.v88]
theorem CFSG.KD.Fi24Alpha.Pc.p87 : Nat.beq (runC AR SD 80 (ckL CFSG.KD.Fi24Alpha.Pc.l89) 2 87 CFSG.KD.Fi24Alpha.Pc.l87) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v89 : Nat := CFSG.KD.Fi24Alpha.KV0 98
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v90 : Nat := CFSG.KD.Fi24Alpha.KV0 99
theorem CFSG.KD.Fi24Alpha.Pc.f6 : Nat.beq (runC AR SD 80 (finC AR SD (nat_lit 6) 80 91) 2 89 CFSG.KD.Fi24Alpha.Pc.l89) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk6 : chk (nat_lit 6) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 6) (lo := 80) (hi := 91) (m := 11) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 11) (m2 := 10) (j2 := 81) (Lr := CFSG.KD.Fi24Alpha.Pc.l81) ((nodeV_pow (R := AR) (D := SD) (lo := 80) (L := []) (j := 80) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 80 [] (SD.na.getD 80 0)) (SD.nk.getD 80 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q80_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Alpha.Pc.q80_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Alpha.Pc.q80_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r80)))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 83) CFSG.KD.Fi24Alpha.Pc.p81 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 85) CFSG.KD.Fi24Alpha.Pc.p83 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 87) CFSG.KD.Fi24Alpha.Pc.p85 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 89) CFSG.KD.Fi24Alpha.Pc.p87 rfl rfl))))))).trans CFSG.KD.Fi24Alpha.Pc.f6

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v91 : Nat := CFSG.KD.Fi24Alpha.KV0 100
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v92 : Nat := CFSG.KD.Fi24Alpha.KV0 101
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l93 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v91, CFSG.KD.Fi24Alpha.Pc.v92]
theorem CFSG.KD.Fi24Alpha.Pc.p91 : Nat.beq (runC AR SD 91 (ckL CFSG.KD.Fi24Alpha.Pc.l93) 2 91 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v93 : Nat := CFSG.KD.Fi24Alpha.KV0 102
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l94 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v91, CFSG.KD.Fi24Alpha.Pc.v92, CFSG.KD.Fi24Alpha.Pc.v93]
theorem CFSG.KD.Fi24Alpha.Pc.p93 : Nat.beq (runC AR SD 91 (ckL CFSG.KD.Fi24Alpha.Pc.l94) 1 93 CFSG.KD.Fi24Alpha.Pc.l93) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a94_1 : Nat := CFSG.KD.Fi24Alpha.KV0 103
theorem CFSG.KD.Fi24Alpha.Pc.q94_1 : Nat.beq (powTop AR.mul (getV AR SD 91 CFSG.KD.Fi24Alpha.Pc.l94 (SD.na.getD 94 0)) (SD.nk.getD 94 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a94_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v94 : Nat := CFSG.KD.Fi24Alpha.KV0 104
theorem CFSG.KD.Fi24Alpha.Pc.r94 : Nat.beq (powR AR.mul AR.one (getV AR SD 91 CFSG.KD.Fi24Alpha.Pc.l94 (SD.na.getD 94 0)) (SD.nk.getD 94 1) 1 CFSG.KD.Fi24Alpha.Pc.a94_1 true) CFSG.KD.Fi24Alpha.Pc.v94 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v95 : Nat := CFSG.KD.Fi24Alpha.KV0 105
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v96 : Nat := CFSG.KD.Fi24Alpha.KV0 106
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l95 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v91, CFSG.KD.Fi24Alpha.Pc.v92, CFSG.KD.Fi24Alpha.Pc.v93, CFSG.KD.Fi24Alpha.Pc.v94]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l97 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v91, CFSG.KD.Fi24Alpha.Pc.v92, CFSG.KD.Fi24Alpha.Pc.v93, CFSG.KD.Fi24Alpha.Pc.v94, CFSG.KD.Fi24Alpha.Pc.v95, CFSG.KD.Fi24Alpha.Pc.v96]
theorem CFSG.KD.Fi24Alpha.Pc.p95 : Nat.beq (runC AR SD 91 (ckL CFSG.KD.Fi24Alpha.Pc.l97) 2 95 CFSG.KD.Fi24Alpha.Pc.l95) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v97 : Nat := CFSG.KD.Fi24Alpha.KV0 107
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v98 : Nat := CFSG.KD.Fi24Alpha.KV0 108
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l99 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v91, CFSG.KD.Fi24Alpha.Pc.v92, CFSG.KD.Fi24Alpha.Pc.v93, CFSG.KD.Fi24Alpha.Pc.v94, CFSG.KD.Fi24Alpha.Pc.v95, CFSG.KD.Fi24Alpha.Pc.v96, CFSG.KD.Fi24Alpha.Pc.v97, CFSG.KD.Fi24Alpha.Pc.v98]
theorem CFSG.KD.Fi24Alpha.Pc.p97 : Nat.beq (runC AR SD 91 (ckL CFSG.KD.Fi24Alpha.Pc.l99) 2 97 CFSG.KD.Fi24Alpha.Pc.l97) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v99 : Nat := CFSG.KD.Fi24Alpha.KV0 109
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v100 : Nat := CFSG.KD.Fi24Alpha.KV0 110
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l101 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v91, CFSG.KD.Fi24Alpha.Pc.v92, CFSG.KD.Fi24Alpha.Pc.v93, CFSG.KD.Fi24Alpha.Pc.v94, CFSG.KD.Fi24Alpha.Pc.v95, CFSG.KD.Fi24Alpha.Pc.v96, CFSG.KD.Fi24Alpha.Pc.v97, CFSG.KD.Fi24Alpha.Pc.v98, CFSG.KD.Fi24Alpha.Pc.v99, CFSG.KD.Fi24Alpha.Pc.v100]
theorem CFSG.KD.Fi24Alpha.Pc.p99 : Nat.beq (runC AR SD 91 (ckL CFSG.KD.Fi24Alpha.Pc.l101) 2 99 CFSG.KD.Fi24Alpha.Pc.l99) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v101 : Nat := CFSG.KD.Fi24Alpha.KV0 111
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v102 : Nat := CFSG.KD.Fi24Alpha.KV0 112
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l103 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v91, CFSG.KD.Fi24Alpha.Pc.v92, CFSG.KD.Fi24Alpha.Pc.v93, CFSG.KD.Fi24Alpha.Pc.v94, CFSG.KD.Fi24Alpha.Pc.v95, CFSG.KD.Fi24Alpha.Pc.v96, CFSG.KD.Fi24Alpha.Pc.v97, CFSG.KD.Fi24Alpha.Pc.v98, CFSG.KD.Fi24Alpha.Pc.v99, CFSG.KD.Fi24Alpha.Pc.v100, CFSG.KD.Fi24Alpha.Pc.v101, CFSG.KD.Fi24Alpha.Pc.v102]
theorem CFSG.KD.Fi24Alpha.Pc.p101 : Nat.beq (runC AR SD 91 (ckL CFSG.KD.Fi24Alpha.Pc.l103) 2 101 CFSG.KD.Fi24Alpha.Pc.l101) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v103 : Nat := CFSG.KD.Fi24Alpha.KV0 113
theorem CFSG.KD.Fi24Alpha.Pc.f7 : Nat.beq (runC AR SD 91 (finC AR SD (nat_lit 7) 91 104) 1 103 CFSG.KD.Fi24Alpha.Pc.l103) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk7 : chk (nat_lit 7) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 7) (lo := 91) (hi := 104) (m := 13) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 13) (m2 := 11) (j2 := 93) CFSG.KD.Fi24Alpha.Pc.p91 rfl rfl).trans ((runC_seq (m := 11) (m2 := 10) (j2 := 94) CFSG.KD.Fi24Alpha.Pc.p93 rfl rfl).trans ((runC_node (m := 10) (m2 := 9) (j2 := 95) (Lr := CFSG.KD.Fi24Alpha.Pc.l95) ((nodeV_pow (R := AR) (D := SD) (lo := 91) (L := CFSG.KD.Fi24Alpha.Pc.l94) (j := 94) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 91 CFSG.KD.Fi24Alpha.Pc.l94 (SD.na.getD 94 0)) (SD.nk.getD 94 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q94_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r94)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 97) CFSG.KD.Fi24Alpha.Pc.p95 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 99) CFSG.KD.Fi24Alpha.Pc.p97 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 101) CFSG.KD.Fi24Alpha.Pc.p99 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 103) CFSG.KD.Fi24Alpha.Pc.p101 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f7

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v104 : Nat := CFSG.KD.Fi24Alpha.KV0 114
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v105 : Nat := CFSG.KD.Fi24Alpha.KV0 115
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l106 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v104, CFSG.KD.Fi24Alpha.Pc.v105]
theorem CFSG.KD.Fi24Alpha.Pc.p104 : Nat.beq (runC AR SD 104 (ckL CFSG.KD.Fi24Alpha.Pc.l106) 2 104 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v106 : Nat := CFSG.KD.Fi24Alpha.KV0 116
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v107 : Nat := CFSG.KD.Fi24Alpha.KV0 117
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l108 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v104, CFSG.KD.Fi24Alpha.Pc.v105, CFSG.KD.Fi24Alpha.Pc.v106, CFSG.KD.Fi24Alpha.Pc.v107]
theorem CFSG.KD.Fi24Alpha.Pc.p106 : Nat.beq (runC AR SD 104 (ckL CFSG.KD.Fi24Alpha.Pc.l108) 2 106 CFSG.KD.Fi24Alpha.Pc.l106) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v108 : Nat := CFSG.KD.Fi24Alpha.KV0 118
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v109 : Nat := CFSG.KD.Fi24Alpha.KV0 119
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l110 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v104, CFSG.KD.Fi24Alpha.Pc.v105, CFSG.KD.Fi24Alpha.Pc.v106, CFSG.KD.Fi24Alpha.Pc.v107, CFSG.KD.Fi24Alpha.Pc.v108, CFSG.KD.Fi24Alpha.Pc.v109]
theorem CFSG.KD.Fi24Alpha.Pc.p108 : Nat.beq (runC AR SD 104 (ckL CFSG.KD.Fi24Alpha.Pc.l110) 2 108 CFSG.KD.Fi24Alpha.Pc.l108) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v110 : Nat := CFSG.KD.Fi24Alpha.KV0 120
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v111 : Nat := CFSG.KD.Fi24Alpha.KV0 121
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l112 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v104, CFSG.KD.Fi24Alpha.Pc.v105, CFSG.KD.Fi24Alpha.Pc.v106, CFSG.KD.Fi24Alpha.Pc.v107, CFSG.KD.Fi24Alpha.Pc.v108, CFSG.KD.Fi24Alpha.Pc.v109, CFSG.KD.Fi24Alpha.Pc.v110, CFSG.KD.Fi24Alpha.Pc.v111]
theorem CFSG.KD.Fi24Alpha.Pc.p110 : Nat.beq (runC AR SD 104 (ckL CFSG.KD.Fi24Alpha.Pc.l112) 2 110 CFSG.KD.Fi24Alpha.Pc.l110) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v112 : Nat := CFSG.KD.Fi24Alpha.KV0 122
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v113 : Nat := CFSG.KD.Fi24Alpha.KV0 123
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l114 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v104, CFSG.KD.Fi24Alpha.Pc.v105, CFSG.KD.Fi24Alpha.Pc.v106, CFSG.KD.Fi24Alpha.Pc.v107, CFSG.KD.Fi24Alpha.Pc.v108, CFSG.KD.Fi24Alpha.Pc.v109, CFSG.KD.Fi24Alpha.Pc.v110, CFSG.KD.Fi24Alpha.Pc.v111, CFSG.KD.Fi24Alpha.Pc.v112, CFSG.KD.Fi24Alpha.Pc.v113]
theorem CFSG.KD.Fi24Alpha.Pc.p112 : Nat.beq (runC AR SD 104 (ckL CFSG.KD.Fi24Alpha.Pc.l114) 2 112 CFSG.KD.Fi24Alpha.Pc.l112) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v114 : Nat := CFSG.KD.Fi24Alpha.KV0 124
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v115 : Nat := CFSG.KD.Fi24Alpha.KV0 125
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l116 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v104, CFSG.KD.Fi24Alpha.Pc.v105, CFSG.KD.Fi24Alpha.Pc.v106, CFSG.KD.Fi24Alpha.Pc.v107, CFSG.KD.Fi24Alpha.Pc.v108, CFSG.KD.Fi24Alpha.Pc.v109, CFSG.KD.Fi24Alpha.Pc.v110, CFSG.KD.Fi24Alpha.Pc.v111, CFSG.KD.Fi24Alpha.Pc.v112, CFSG.KD.Fi24Alpha.Pc.v113, CFSG.KD.Fi24Alpha.Pc.v114, CFSG.KD.Fi24Alpha.Pc.v115]
theorem CFSG.KD.Fi24Alpha.Pc.p114 : Nat.beq (runC AR SD 104 (ckL CFSG.KD.Fi24Alpha.Pc.l116) 2 114 CFSG.KD.Fi24Alpha.Pc.l114) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v116 : Nat := CFSG.KD.Fi24Alpha.KV0 126
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l117 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v104, CFSG.KD.Fi24Alpha.Pc.v105, CFSG.KD.Fi24Alpha.Pc.v106, CFSG.KD.Fi24Alpha.Pc.v107, CFSG.KD.Fi24Alpha.Pc.v108, CFSG.KD.Fi24Alpha.Pc.v109, CFSG.KD.Fi24Alpha.Pc.v110, CFSG.KD.Fi24Alpha.Pc.v111, CFSG.KD.Fi24Alpha.Pc.v112, CFSG.KD.Fi24Alpha.Pc.v113, CFSG.KD.Fi24Alpha.Pc.v114, CFSG.KD.Fi24Alpha.Pc.v115, CFSG.KD.Fi24Alpha.Pc.v116]
theorem CFSG.KD.Fi24Alpha.Pc.p116 : Nat.beq (runC AR SD 104 (ckL CFSG.KD.Fi24Alpha.Pc.l117) 1 116 CFSG.KD.Fi24Alpha.Pc.l116) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a117_1 : Nat := CFSG.KD.Fi24Alpha.KV0 127
theorem CFSG.KD.Fi24Alpha.Pc.q117_1 : Nat.beq (powTop AR.mul (getV AR SD 104 CFSG.KD.Fi24Alpha.Pc.l117 (SD.na.getD 117 0)) (SD.nk.getD 117 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a117_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v117 : Nat := CFSG.KD.Fi24Alpha.KV0 128
theorem CFSG.KD.Fi24Alpha.Pc.r117 : Nat.beq (powR AR.mul AR.one (getV AR SD 104 CFSG.KD.Fi24Alpha.Pc.l117 (SD.na.getD 117 0)) (SD.nk.getD 117 1) 1 CFSG.KD.Fi24Alpha.Pc.a117_1 true) CFSG.KD.Fi24Alpha.Pc.v117 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l118 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v104, CFSG.KD.Fi24Alpha.Pc.v105, CFSG.KD.Fi24Alpha.Pc.v106, CFSG.KD.Fi24Alpha.Pc.v107, CFSG.KD.Fi24Alpha.Pc.v108, CFSG.KD.Fi24Alpha.Pc.v109, CFSG.KD.Fi24Alpha.Pc.v110, CFSG.KD.Fi24Alpha.Pc.v111, CFSG.KD.Fi24Alpha.Pc.v112, CFSG.KD.Fi24Alpha.Pc.v113, CFSG.KD.Fi24Alpha.Pc.v114, CFSG.KD.Fi24Alpha.Pc.v115, CFSG.KD.Fi24Alpha.Pc.v116, CFSG.KD.Fi24Alpha.Pc.v117]
theorem CFSG.KD.Fi24Alpha.Pc.f8 : Nat.beq (runC AR SD 104 (finC AR SD (nat_lit 8) 104 118) 0 118 CFSG.KD.Fi24Alpha.Pc.l118) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk8 : chk (nat_lit 8) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 8) (lo := 104) (hi := 118) (m := 14) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 14) (m2 := 12) (j2 := 106) CFSG.KD.Fi24Alpha.Pc.p104 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 108) CFSG.KD.Fi24Alpha.Pc.p106 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 110) CFSG.KD.Fi24Alpha.Pc.p108 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 112) CFSG.KD.Fi24Alpha.Pc.p110 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 114) CFSG.KD.Fi24Alpha.Pc.p112 rfl rfl).trans ((runC_seq (m := 4) (m2 := 2) (j2 := 116) CFSG.KD.Fi24Alpha.Pc.p114 rfl rfl).trans ((runC_seq (m := 2) (m2 := 1) (j2 := 117) CFSG.KD.Fi24Alpha.Pc.p116 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 118) (Lr := CFSG.KD.Fi24Alpha.Pc.l118) ((nodeV_pow (R := AR) (D := SD) (lo := 104) (L := CFSG.KD.Fi24Alpha.Pc.l117) (j := 117) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 104 CFSG.KD.Fi24Alpha.Pc.l117 (SD.na.getD 117 0)) (SD.nk.getD 117 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q117_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r117)))) (by quickRfl) rfl rfl rfl)))))))))).trans CFSG.KD.Fi24Alpha.Pc.f8

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v118 : Nat := CFSG.KD.Fi24Alpha.KV0 129
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v119 : Nat := CFSG.KD.Fi24Alpha.KV0 130
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l120 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v118, CFSG.KD.Fi24Alpha.Pc.v119]
theorem CFSG.KD.Fi24Alpha.Pc.p118 : Nat.beq (runC AR SD 118 (ckL CFSG.KD.Fi24Alpha.Pc.l120) 2 118 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v120 : Nat := CFSG.KD.Fi24Alpha.KV0 131
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l121 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v118, CFSG.KD.Fi24Alpha.Pc.v119, CFSG.KD.Fi24Alpha.Pc.v120]
theorem CFSG.KD.Fi24Alpha.Pc.p120 : Nat.beq (runC AR SD 118 (ckL CFSG.KD.Fi24Alpha.Pc.l121) 1 120 CFSG.KD.Fi24Alpha.Pc.l120) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a121_1 : Nat := CFSG.KD.Fi24Alpha.KV0 132
theorem CFSG.KD.Fi24Alpha.Pc.q121_1 : Nat.beq (powTop AR.mul (getV AR SD 118 CFSG.KD.Fi24Alpha.Pc.l121 (SD.na.getD 121 0)) (SD.nk.getD 121 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a121_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v121 : Nat := CFSG.KD.Fi24Alpha.KV0 133
theorem CFSG.KD.Fi24Alpha.Pc.r121 : Nat.beq (powR AR.mul AR.one (getV AR SD 118 CFSG.KD.Fi24Alpha.Pc.l121 (SD.na.getD 121 0)) (SD.nk.getD 121 1) 1 CFSG.KD.Fi24Alpha.Pc.a121_1 true) CFSG.KD.Fi24Alpha.Pc.v121 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v122 : Nat := CFSG.KD.Fi24Alpha.KV0 134
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v123 : Nat := CFSG.KD.Fi24Alpha.KV0 135
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l122 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v118, CFSG.KD.Fi24Alpha.Pc.v119, CFSG.KD.Fi24Alpha.Pc.v120, CFSG.KD.Fi24Alpha.Pc.v121]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l124 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v118, CFSG.KD.Fi24Alpha.Pc.v119, CFSG.KD.Fi24Alpha.Pc.v120, CFSG.KD.Fi24Alpha.Pc.v121, CFSG.KD.Fi24Alpha.Pc.v122, CFSG.KD.Fi24Alpha.Pc.v123]
theorem CFSG.KD.Fi24Alpha.Pc.p122 : Nat.beq (runC AR SD 118 (ckL CFSG.KD.Fi24Alpha.Pc.l124) 2 122 CFSG.KD.Fi24Alpha.Pc.l122) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v124 : Nat := CFSG.KD.Fi24Alpha.KV0 136
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v125 : Nat := CFSG.KD.Fi24Alpha.KV0 137
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l126 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v118, CFSG.KD.Fi24Alpha.Pc.v119, CFSG.KD.Fi24Alpha.Pc.v120, CFSG.KD.Fi24Alpha.Pc.v121, CFSG.KD.Fi24Alpha.Pc.v122, CFSG.KD.Fi24Alpha.Pc.v123, CFSG.KD.Fi24Alpha.Pc.v124, CFSG.KD.Fi24Alpha.Pc.v125]
theorem CFSG.KD.Fi24Alpha.Pc.p124 : Nat.beq (runC AR SD 118 (ckL CFSG.KD.Fi24Alpha.Pc.l126) 2 124 CFSG.KD.Fi24Alpha.Pc.l124) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v126 : Nat := CFSG.KD.Fi24Alpha.KV0 138
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l127 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v118, CFSG.KD.Fi24Alpha.Pc.v119, CFSG.KD.Fi24Alpha.Pc.v120, CFSG.KD.Fi24Alpha.Pc.v121, CFSG.KD.Fi24Alpha.Pc.v122, CFSG.KD.Fi24Alpha.Pc.v123, CFSG.KD.Fi24Alpha.Pc.v124, CFSG.KD.Fi24Alpha.Pc.v125, CFSG.KD.Fi24Alpha.Pc.v126]
theorem CFSG.KD.Fi24Alpha.Pc.p126 : Nat.beq (runC AR SD 118 (ckL CFSG.KD.Fi24Alpha.Pc.l127) 1 126 CFSG.KD.Fi24Alpha.Pc.l126) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a127_3 : Nat := CFSG.KD.Fi24Alpha.KV0 139
theorem CFSG.KD.Fi24Alpha.Pc.q127_3 : Nat.beq (powTop AR.mul (getV AR SD 118 CFSG.KD.Fi24Alpha.Pc.l127 (SD.na.getD 127 0)) (SD.nk.getD 127 1) 3 (ckP CFSG.KD.Fi24Alpha.Pc.a127_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a127_2 : Nat := CFSG.KD.Fi24Alpha.KV0 140
theorem CFSG.KD.Fi24Alpha.Pc.q127_2 : Nat.beq (powTop AR.mul (getV AR SD 118 CFSG.KD.Fi24Alpha.Pc.l127 (SD.na.getD 127 0)) (SD.nk.getD 127 1) 2 (ckP CFSG.KD.Fi24Alpha.Pc.a127_2) 1 CFSG.KD.Fi24Alpha.Pc.a127_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v127 : Nat := CFSG.KD.Fi24Alpha.KV0 141
theorem CFSG.KD.Fi24Alpha.Pc.r127 : Nat.beq (powR AR.mul AR.one (getV AR SD 118 CFSG.KD.Fi24Alpha.Pc.l127 (SD.na.getD 127 0)) (SD.nk.getD 127 1) 2 CFSG.KD.Fi24Alpha.Pc.a127_2 true) CFSG.KD.Fi24Alpha.Pc.v127 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l128 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v118, CFSG.KD.Fi24Alpha.Pc.v119, CFSG.KD.Fi24Alpha.Pc.v120, CFSG.KD.Fi24Alpha.Pc.v121, CFSG.KD.Fi24Alpha.Pc.v122, CFSG.KD.Fi24Alpha.Pc.v123, CFSG.KD.Fi24Alpha.Pc.v124, CFSG.KD.Fi24Alpha.Pc.v125, CFSG.KD.Fi24Alpha.Pc.v126, CFSG.KD.Fi24Alpha.Pc.v127]
theorem CFSG.KD.Fi24Alpha.Pc.f9 : Nat.beq (runC AR SD 118 (finC AR SD (nat_lit 9) 118 128) 0 128 CFSG.KD.Fi24Alpha.Pc.l128) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk9 : chk (nat_lit 9) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 9) (lo := 118) (hi := 128) (m := 10) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 10) (m2 := 8) (j2 := 120) CFSG.KD.Fi24Alpha.Pc.p118 rfl rfl).trans ((runC_seq (m := 8) (m2 := 7) (j2 := 121) CFSG.KD.Fi24Alpha.Pc.p120 rfl rfl).trans ((runC_node (m := 7) (m2 := 6) (j2 := 122) (Lr := CFSG.KD.Fi24Alpha.Pc.l122) ((nodeV_pow (R := AR) (D := SD) (lo := 118) (L := CFSG.KD.Fi24Alpha.Pc.l121) (j := 121) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 118 CFSG.KD.Fi24Alpha.Pc.l121 (SD.na.getD 121 0)) (SD.nk.getD 121 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q121_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r121)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 124) CFSG.KD.Fi24Alpha.Pc.p122 rfl rfl).trans ((runC_seq (m := 4) (m2 := 2) (j2 := 126) CFSG.KD.Fi24Alpha.Pc.p124 rfl rfl).trans ((runC_seq (m := 2) (m2 := 1) (j2 := 127) CFSG.KD.Fi24Alpha.Pc.p126 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 128) (Lr := CFSG.KD.Fi24Alpha.Pc.l128) ((nodeV_pow (R := AR) (D := SD) (lo := 118) (L := CFSG.KD.Fi24Alpha.Pc.l127) (j := 127) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 118 CFSG.KD.Fi24Alpha.Pc.l127 (SD.na.getD 127 0)) (SD.nk.getD 127 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q127_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Alpha.Pc.q127_2 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r127))))) (by quickRfl) rfl rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f9

end
