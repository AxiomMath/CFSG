module

public import Certificates.Kernel.Sporadic.Fi24Tc.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Tc KV0 "Certificates/Kernel/Sporadic/Fi24Tc/data/v0.bin" 152491 4 16164046 9067044338027223063

public section

open CFSG.KD.Fi24Tc CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v0 : Nat := CFSG.KD.Fi24Tc.KV0 0
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1 : Nat := CFSG.KD.Fi24Tc.KV0 1
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l2 : List Nat := [CFSG.KD.Fi24Tc.Pc.v0, CFSG.KD.Fi24Tc.Pc.v1]
theorem CFSG.KD.Fi24Tc.Pc.p0 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Tc.Pc.l2) 2 0 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v2 : Nat := CFSG.KD.Fi24Tc.KV0 2
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v3 : Nat := CFSG.KD.Fi24Tc.KV0 3
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l4 : List Nat := [CFSG.KD.Fi24Tc.Pc.v0, CFSG.KD.Fi24Tc.Pc.v1, CFSG.KD.Fi24Tc.Pc.v2, CFSG.KD.Fi24Tc.Pc.v3]
theorem CFSG.KD.Fi24Tc.Pc.p2 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Tc.Pc.l4) 2 2 CFSG.KD.Fi24Tc.Pc.l2) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v4 : Nat := CFSG.KD.Fi24Tc.KV0 4
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v5 : Nat := CFSG.KD.Fi24Tc.KV0 5
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l6 : List Nat := [CFSG.KD.Fi24Tc.Pc.v0, CFSG.KD.Fi24Tc.Pc.v1, CFSG.KD.Fi24Tc.Pc.v2, CFSG.KD.Fi24Tc.Pc.v3, CFSG.KD.Fi24Tc.Pc.v4, CFSG.KD.Fi24Tc.Pc.v5]
theorem CFSG.KD.Fi24Tc.Pc.p4 : Nat.beq (runC AR SD 0 (ckL CFSG.KD.Fi24Tc.Pc.l6) 2 4 CFSG.KD.Fi24Tc.Pc.l4) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f0 : Nat.beq (runC AR SD 0 (finC AR SD (nat_lit 0) 0 8) 2 6 CFSG.KD.Fi24Tc.Pc.l6) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk0 : chk (nat_lit 0) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 0) (lo := 0) (hi := 8) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 2) CFSG.KD.Fi24Tc.Pc.p0 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 4) CFSG.KD.Fi24Tc.Pc.p2 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 6) CFSG.KD.Fi24Tc.Pc.p4 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f0

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v8 : Nat := CFSG.KD.Fi24Tc.KV0 6
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v9 : Nat := CFSG.KD.Fi24Tc.KV0 7
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l10 : List Nat := [CFSG.KD.Fi24Tc.Pc.v8, CFSG.KD.Fi24Tc.Pc.v9]
theorem CFSG.KD.Fi24Tc.Pc.p8 : Nat.beq (runC AR SD 8 (ckL CFSG.KD.Fi24Tc.Pc.l10) 2 8 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v10 : Nat := CFSG.KD.Fi24Tc.KV0 8
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v11 : Nat := CFSG.KD.Fi24Tc.KV0 9
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l12 : List Nat := [CFSG.KD.Fi24Tc.Pc.v8, CFSG.KD.Fi24Tc.Pc.v9, CFSG.KD.Fi24Tc.Pc.v10, CFSG.KD.Fi24Tc.Pc.v11]
theorem CFSG.KD.Fi24Tc.Pc.p10 : Nat.beq (runC AR SD 8 (ckL CFSG.KD.Fi24Tc.Pc.l12) 2 10 CFSG.KD.Fi24Tc.Pc.l10) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v12 : Nat := CFSG.KD.Fi24Tc.KV0 10
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v13 : Nat := CFSG.KD.Fi24Tc.KV0 11
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l14 : List Nat := [CFSG.KD.Fi24Tc.Pc.v8, CFSG.KD.Fi24Tc.Pc.v9, CFSG.KD.Fi24Tc.Pc.v10, CFSG.KD.Fi24Tc.Pc.v11, CFSG.KD.Fi24Tc.Pc.v12, CFSG.KD.Fi24Tc.Pc.v13]
theorem CFSG.KD.Fi24Tc.Pc.p12 : Nat.beq (runC AR SD 8 (ckL CFSG.KD.Fi24Tc.Pc.l14) 2 12 CFSG.KD.Fi24Tc.Pc.l12) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f1 : Nat.beq (runC AR SD 8 (finC AR SD (nat_lit 1) 8 16) 2 14 CFSG.KD.Fi24Tc.Pc.l14) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk1 : chk (nat_lit 1) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 1) (lo := 8) (hi := 16) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 10) CFSG.KD.Fi24Tc.Pc.p8 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 12) CFSG.KD.Fi24Tc.Pc.p10 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 14) CFSG.KD.Fi24Tc.Pc.p12 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f1

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v16 : Nat := CFSG.KD.Fi24Tc.KV0 12
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v17 : Nat := CFSG.KD.Fi24Tc.KV0 13
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l18 : List Nat := [CFSG.KD.Fi24Tc.Pc.v16, CFSG.KD.Fi24Tc.Pc.v17]
theorem CFSG.KD.Fi24Tc.Pc.p16 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Tc.Pc.l18) 2 16 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v18 : Nat := CFSG.KD.Fi24Tc.KV0 14
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v19 : Nat := CFSG.KD.Fi24Tc.KV0 15
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l20 : List Nat := [CFSG.KD.Fi24Tc.Pc.v16, CFSG.KD.Fi24Tc.Pc.v17, CFSG.KD.Fi24Tc.Pc.v18, CFSG.KD.Fi24Tc.Pc.v19]
theorem CFSG.KD.Fi24Tc.Pc.p18 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Tc.Pc.l20) 2 18 CFSG.KD.Fi24Tc.Pc.l18) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v20 : Nat := CFSG.KD.Fi24Tc.KV0 16
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v21 : Nat := CFSG.KD.Fi24Tc.KV0 17
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l22 : List Nat := [CFSG.KD.Fi24Tc.Pc.v16, CFSG.KD.Fi24Tc.Pc.v17, CFSG.KD.Fi24Tc.Pc.v18, CFSG.KD.Fi24Tc.Pc.v19, CFSG.KD.Fi24Tc.Pc.v20, CFSG.KD.Fi24Tc.Pc.v21]
theorem CFSG.KD.Fi24Tc.Pc.p20 : Nat.beq (runC AR SD 16 (ckL CFSG.KD.Fi24Tc.Pc.l22) 2 20 CFSG.KD.Fi24Tc.Pc.l20) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f2 : Nat.beq (runC AR SD 16 (finC AR SD (nat_lit 2) 16 24) 2 22 CFSG.KD.Fi24Tc.Pc.l22) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk2 : chk (nat_lit 2) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 2) (lo := 16) (hi := 24) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 18) CFSG.KD.Fi24Tc.Pc.p16 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 20) CFSG.KD.Fi24Tc.Pc.p18 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 22) CFSG.KD.Fi24Tc.Pc.p20 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f2

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v24 : Nat := CFSG.KD.Fi24Tc.KV0 18
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v25 : Nat := CFSG.KD.Fi24Tc.KV0 19
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l26 : List Nat := [CFSG.KD.Fi24Tc.Pc.v24, CFSG.KD.Fi24Tc.Pc.v25]
theorem CFSG.KD.Fi24Tc.Pc.p24 : Nat.beq (runC AR SD 24 (ckL CFSG.KD.Fi24Tc.Pc.l26) 2 24 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v26 : Nat := CFSG.KD.Fi24Tc.KV0 20
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v27 : Nat := CFSG.KD.Fi24Tc.KV0 21
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l28 : List Nat := [CFSG.KD.Fi24Tc.Pc.v24, CFSG.KD.Fi24Tc.Pc.v25, CFSG.KD.Fi24Tc.Pc.v26, CFSG.KD.Fi24Tc.Pc.v27]
theorem CFSG.KD.Fi24Tc.Pc.p26 : Nat.beq (runC AR SD 24 (ckL CFSG.KD.Fi24Tc.Pc.l28) 2 26 CFSG.KD.Fi24Tc.Pc.l26) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v28 : Nat := CFSG.KD.Fi24Tc.KV0 22
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v29 : Nat := CFSG.KD.Fi24Tc.KV0 23
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l30 : List Nat := [CFSG.KD.Fi24Tc.Pc.v24, CFSG.KD.Fi24Tc.Pc.v25, CFSG.KD.Fi24Tc.Pc.v26, CFSG.KD.Fi24Tc.Pc.v27, CFSG.KD.Fi24Tc.Pc.v28, CFSG.KD.Fi24Tc.Pc.v29]
theorem CFSG.KD.Fi24Tc.Pc.p28 : Nat.beq (runC AR SD 24 (ckL CFSG.KD.Fi24Tc.Pc.l30) 2 28 CFSG.KD.Fi24Tc.Pc.l28) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f3 : Nat.beq (runC AR SD 24 (finC AR SD (nat_lit 3) 24 32) 2 30 CFSG.KD.Fi24Tc.Pc.l30) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk3 : chk (nat_lit 3) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 3) (lo := 24) (hi := 32) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 26) CFSG.KD.Fi24Tc.Pc.p24 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 28) CFSG.KD.Fi24Tc.Pc.p26 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 30) CFSG.KD.Fi24Tc.Pc.p28 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f3

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v32 : Nat := CFSG.KD.Fi24Tc.KV0 24
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v33 : Nat := CFSG.KD.Fi24Tc.KV0 25
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l34 : List Nat := [CFSG.KD.Fi24Tc.Pc.v32, CFSG.KD.Fi24Tc.Pc.v33]
theorem CFSG.KD.Fi24Tc.Pc.p32 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Tc.Pc.l34) 2 32 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v34 : Nat := CFSG.KD.Fi24Tc.KV0 26
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v35 : Nat := CFSG.KD.Fi24Tc.KV0 27
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l36 : List Nat := [CFSG.KD.Fi24Tc.Pc.v32, CFSG.KD.Fi24Tc.Pc.v33, CFSG.KD.Fi24Tc.Pc.v34, CFSG.KD.Fi24Tc.Pc.v35]
theorem CFSG.KD.Fi24Tc.Pc.p34 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Tc.Pc.l36) 2 34 CFSG.KD.Fi24Tc.Pc.l34) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v36 : Nat := CFSG.KD.Fi24Tc.KV0 28
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v37 : Nat := CFSG.KD.Fi24Tc.KV0 29
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l38 : List Nat := [CFSG.KD.Fi24Tc.Pc.v32, CFSG.KD.Fi24Tc.Pc.v33, CFSG.KD.Fi24Tc.Pc.v34, CFSG.KD.Fi24Tc.Pc.v35, CFSG.KD.Fi24Tc.Pc.v36, CFSG.KD.Fi24Tc.Pc.v37]
theorem CFSG.KD.Fi24Tc.Pc.p36 : Nat.beq (runC AR SD 32 (ckL CFSG.KD.Fi24Tc.Pc.l38) 2 36 CFSG.KD.Fi24Tc.Pc.l36) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f4 : Nat.beq (runC AR SD 32 (finC AR SD (nat_lit 4) 32 40) 2 38 CFSG.KD.Fi24Tc.Pc.l38) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk4 : chk (nat_lit 4) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 4) (lo := 32) (hi := 40) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 34) CFSG.KD.Fi24Tc.Pc.p32 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 36) CFSG.KD.Fi24Tc.Pc.p34 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 38) CFSG.KD.Fi24Tc.Pc.p36 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f4

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v40 : Nat := CFSG.KD.Fi24Tc.KV0 30
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v41 : Nat := CFSG.KD.Fi24Tc.KV0 31
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l42 : List Nat := [CFSG.KD.Fi24Tc.Pc.v40, CFSG.KD.Fi24Tc.Pc.v41]
theorem CFSG.KD.Fi24Tc.Pc.p40 : Nat.beq (runC AR SD 40 (ckL CFSG.KD.Fi24Tc.Pc.l42) 2 40 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v42 : Nat := CFSG.KD.Fi24Tc.KV0 32
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v43 : Nat := CFSG.KD.Fi24Tc.KV0 33
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l44 : List Nat := [CFSG.KD.Fi24Tc.Pc.v40, CFSG.KD.Fi24Tc.Pc.v41, CFSG.KD.Fi24Tc.Pc.v42, CFSG.KD.Fi24Tc.Pc.v43]
theorem CFSG.KD.Fi24Tc.Pc.p42 : Nat.beq (runC AR SD 40 (ckL CFSG.KD.Fi24Tc.Pc.l44) 2 42 CFSG.KD.Fi24Tc.Pc.l42) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v44 : Nat := CFSG.KD.Fi24Tc.KV0 34
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v45 : Nat := CFSG.KD.Fi24Tc.KV0 35
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l46 : List Nat := [CFSG.KD.Fi24Tc.Pc.v40, CFSG.KD.Fi24Tc.Pc.v41, CFSG.KD.Fi24Tc.Pc.v42, CFSG.KD.Fi24Tc.Pc.v43, CFSG.KD.Fi24Tc.Pc.v44, CFSG.KD.Fi24Tc.Pc.v45]
theorem CFSG.KD.Fi24Tc.Pc.p44 : Nat.beq (runC AR SD 40 (ckL CFSG.KD.Fi24Tc.Pc.l46) 2 44 CFSG.KD.Fi24Tc.Pc.l44) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f5 : Nat.beq (runC AR SD 40 (finC AR SD (nat_lit 5) 40 48) 2 46 CFSG.KD.Fi24Tc.Pc.l46) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk5 : chk (nat_lit 5) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 5) (lo := 40) (hi := 48) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 42) CFSG.KD.Fi24Tc.Pc.p40 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 44) CFSG.KD.Fi24Tc.Pc.p42 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 46) CFSG.KD.Fi24Tc.Pc.p44 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f5

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v48 : Nat := CFSG.KD.Fi24Tc.KV0 36
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v49 : Nat := CFSG.KD.Fi24Tc.KV0 37
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l50 : List Nat := [CFSG.KD.Fi24Tc.Pc.v48, CFSG.KD.Fi24Tc.Pc.v49]
theorem CFSG.KD.Fi24Tc.Pc.p48 : Nat.beq (runC AR SD 48 (ckL CFSG.KD.Fi24Tc.Pc.l50) 2 48 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v50 : Nat := CFSG.KD.Fi24Tc.KV0 38
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v51 : Nat := CFSG.KD.Fi24Tc.KV0 39
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l52 : List Nat := [CFSG.KD.Fi24Tc.Pc.v48, CFSG.KD.Fi24Tc.Pc.v49, CFSG.KD.Fi24Tc.Pc.v50, CFSG.KD.Fi24Tc.Pc.v51]
theorem CFSG.KD.Fi24Tc.Pc.p50 : Nat.beq (runC AR SD 48 (ckL CFSG.KD.Fi24Tc.Pc.l52) 2 50 CFSG.KD.Fi24Tc.Pc.l50) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v52 : Nat := CFSG.KD.Fi24Tc.KV0 40
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l53 : List Nat := [CFSG.KD.Fi24Tc.Pc.v48, CFSG.KD.Fi24Tc.Pc.v49, CFSG.KD.Fi24Tc.Pc.v50, CFSG.KD.Fi24Tc.Pc.v51, CFSG.KD.Fi24Tc.Pc.v52]
theorem CFSG.KD.Fi24Tc.Pc.p52 : Nat.beq (runC AR SD 48 (ckL CFSG.KD.Fi24Tc.Pc.l53) 1 52 CFSG.KD.Fi24Tc.Pc.l52) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a53_1 : Nat := CFSG.KD.Fi24Tc.KV0 41
theorem CFSG.KD.Fi24Tc.Pc.q53_1 : Nat.beq (powTop AR.mul (getV AR SD 48 CFSG.KD.Fi24Tc.Pc.l53 (SD.na.getD 53 0)) (SD.nk.getD 53 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a53_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v53 : Nat := CFSG.KD.Fi24Tc.KV0 42
theorem CFSG.KD.Fi24Tc.Pc.r53 : Nat.beq (powR AR.mul AR.one (getV AR SD 48 CFSG.KD.Fi24Tc.Pc.l53 (SD.na.getD 53 0)) (SD.nk.getD 53 1) 1 CFSG.KD.Fi24Tc.Pc.a53_1 true) CFSG.KD.Fi24Tc.Pc.v53 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l54 : List Nat := [CFSG.KD.Fi24Tc.Pc.v48, CFSG.KD.Fi24Tc.Pc.v49, CFSG.KD.Fi24Tc.Pc.v50, CFSG.KD.Fi24Tc.Pc.v51, CFSG.KD.Fi24Tc.Pc.v52, CFSG.KD.Fi24Tc.Pc.v53]
theorem CFSG.KD.Fi24Tc.Pc.f6 : Nat.beq (runC AR SD 48 (finC AR SD (nat_lit 6) 48 54) 0 54 CFSG.KD.Fi24Tc.Pc.l54) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk6 : chk (nat_lit 6) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 6) (lo := 48) (hi := 54) (m := 6) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 6) (m2 := 4) (j2 := 50) CFSG.KD.Fi24Tc.Pc.p48 rfl rfl).trans ((runC_seq (m := 4) (m2 := 2) (j2 := 52) CFSG.KD.Fi24Tc.Pc.p50 rfl rfl).trans ((runC_seq (m := 2) (m2 := 1) (j2 := 53) CFSG.KD.Fi24Tc.Pc.p52 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 54) (Lr := CFSG.KD.Fi24Tc.Pc.l54) ((nodeV_pow (R := AR) (D := SD) (lo := 48) (L := CFSG.KD.Fi24Tc.Pc.l53) (j := 53) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 48 CFSG.KD.Fi24Tc.Pc.l53 (SD.na.getD 53 0)) (SD.nk.getD 53 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q53_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r53)))) (by quickRfl) rfl rfl rfl)))))).trans CFSG.KD.Fi24Tc.Pc.f6

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v54 : Nat := CFSG.KD.Fi24Tc.KV0 43
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v55 : Nat := CFSG.KD.Fi24Tc.KV0 44
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l56 : List Nat := [CFSG.KD.Fi24Tc.Pc.v54, CFSG.KD.Fi24Tc.Pc.v55]
theorem CFSG.KD.Fi24Tc.Pc.p54 : Nat.beq (runC AR SD 54 (ckL CFSG.KD.Fi24Tc.Pc.l56) 2 54 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v56 : Nat := CFSG.KD.Fi24Tc.KV0 45
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v57 : Nat := CFSG.KD.Fi24Tc.KV0 46
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l58 : List Nat := [CFSG.KD.Fi24Tc.Pc.v54, CFSG.KD.Fi24Tc.Pc.v55, CFSG.KD.Fi24Tc.Pc.v56, CFSG.KD.Fi24Tc.Pc.v57]
theorem CFSG.KD.Fi24Tc.Pc.p56 : Nat.beq (runC AR SD 54 (ckL CFSG.KD.Fi24Tc.Pc.l58) 2 56 CFSG.KD.Fi24Tc.Pc.l56) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v58 : Nat := CFSG.KD.Fi24Tc.KV0 47
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v59 : Nat := CFSG.KD.Fi24Tc.KV0 48
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l60 : List Nat := [CFSG.KD.Fi24Tc.Pc.v54, CFSG.KD.Fi24Tc.Pc.v55, CFSG.KD.Fi24Tc.Pc.v56, CFSG.KD.Fi24Tc.Pc.v57, CFSG.KD.Fi24Tc.Pc.v58, CFSG.KD.Fi24Tc.Pc.v59]
theorem CFSG.KD.Fi24Tc.Pc.p58 : Nat.beq (runC AR SD 54 (ckL CFSG.KD.Fi24Tc.Pc.l60) 2 58 CFSG.KD.Fi24Tc.Pc.l58) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f7 : Nat.beq (runC AR SD 54 (finC AR SD (nat_lit 7) 54 62) 2 60 CFSG.KD.Fi24Tc.Pc.l60) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk7 : chk (nat_lit 7) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 7) (lo := 54) (hi := 62) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 56) CFSG.KD.Fi24Tc.Pc.p54 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 58) CFSG.KD.Fi24Tc.Pc.p56 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 60) CFSG.KD.Fi24Tc.Pc.p58 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f7

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v62 : Nat := CFSG.KD.Fi24Tc.KV0 49
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v63 : Nat := CFSG.KD.Fi24Tc.KV0 50
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l64 : List Nat := [CFSG.KD.Fi24Tc.Pc.v62, CFSG.KD.Fi24Tc.Pc.v63]
theorem CFSG.KD.Fi24Tc.Pc.p62 : Nat.beq (runC AR SD 62 (ckL CFSG.KD.Fi24Tc.Pc.l64) 2 62 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v64 : Nat := CFSG.KD.Fi24Tc.KV0 51
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v65 : Nat := CFSG.KD.Fi24Tc.KV0 52
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l66 : List Nat := [CFSG.KD.Fi24Tc.Pc.v62, CFSG.KD.Fi24Tc.Pc.v63, CFSG.KD.Fi24Tc.Pc.v64, CFSG.KD.Fi24Tc.Pc.v65]
theorem CFSG.KD.Fi24Tc.Pc.p64 : Nat.beq (runC AR SD 62 (ckL CFSG.KD.Fi24Tc.Pc.l66) 2 64 CFSG.KD.Fi24Tc.Pc.l64) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a66_1 : Nat := CFSG.KD.Fi24Tc.KV0 53
theorem CFSG.KD.Fi24Tc.Pc.q66_1 : Nat.beq (powTop AR.mul (getV AR SD 62 CFSG.KD.Fi24Tc.Pc.l66 (SD.na.getD 66 0)) (SD.nk.getD 66 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a66_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v66 : Nat := CFSG.KD.Fi24Tc.KV0 54
theorem CFSG.KD.Fi24Tc.Pc.r66 : Nat.beq (powR AR.mul AR.one (getV AR SD 62 CFSG.KD.Fi24Tc.Pc.l66 (SD.na.getD 66 0)) (SD.nk.getD 66 1) 1 CFSG.KD.Fi24Tc.Pc.a66_1 true) CFSG.KD.Fi24Tc.Pc.v66 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l67 : List Nat := [CFSG.KD.Fi24Tc.Pc.v62, CFSG.KD.Fi24Tc.Pc.v63, CFSG.KD.Fi24Tc.Pc.v64, CFSG.KD.Fi24Tc.Pc.v65, CFSG.KD.Fi24Tc.Pc.v66]
theorem CFSG.KD.Fi24Tc.Pc.f8 : Nat.beq (runC AR SD 62 (finC AR SD (nat_lit 8) 62 67) 0 67 CFSG.KD.Fi24Tc.Pc.l67) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk8 : chk (nat_lit 8) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 8) (lo := 62) (hi := 67) (m := 5) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 5) (m2 := 3) (j2 := 64) CFSG.KD.Fi24Tc.Pc.p62 rfl rfl).trans ((runC_seq (m := 3) (m2 := 1) (j2 := 66) CFSG.KD.Fi24Tc.Pc.p64 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 67) (Lr := CFSG.KD.Fi24Tc.Pc.l67) ((nodeV_pow (R := AR) (D := SD) (lo := 62) (L := CFSG.KD.Fi24Tc.Pc.l66) (j := 66) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 62 CFSG.KD.Fi24Tc.Pc.l66 (SD.na.getD 66 0)) (SD.nk.getD 66 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q66_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r66)))) (by quickRfl) rfl rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f8

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v67 : Nat := CFSG.KD.Fi24Tc.KV0 55
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v68 : Nat := CFSG.KD.Fi24Tc.KV0 56
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l69 : List Nat := [CFSG.KD.Fi24Tc.Pc.v67, CFSG.KD.Fi24Tc.Pc.v68]
theorem CFSG.KD.Fi24Tc.Pc.p67 : Nat.beq (runC AR SD 67 (ckL CFSG.KD.Fi24Tc.Pc.l69) 2 67 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v69 : Nat := CFSG.KD.Fi24Tc.KV0 57
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v70 : Nat := CFSG.KD.Fi24Tc.KV0 58
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l71 : List Nat := [CFSG.KD.Fi24Tc.Pc.v67, CFSG.KD.Fi24Tc.Pc.v68, CFSG.KD.Fi24Tc.Pc.v69, CFSG.KD.Fi24Tc.Pc.v70]
theorem CFSG.KD.Fi24Tc.Pc.p69 : Nat.beq (runC AR SD 67 (ckL CFSG.KD.Fi24Tc.Pc.l71) 2 69 CFSG.KD.Fi24Tc.Pc.l69) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v71 : Nat := CFSG.KD.Fi24Tc.KV0 59
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v72 : Nat := CFSG.KD.Fi24Tc.KV0 60
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l73 : List Nat := [CFSG.KD.Fi24Tc.Pc.v67, CFSG.KD.Fi24Tc.Pc.v68, CFSG.KD.Fi24Tc.Pc.v69, CFSG.KD.Fi24Tc.Pc.v70, CFSG.KD.Fi24Tc.Pc.v71, CFSG.KD.Fi24Tc.Pc.v72]
theorem CFSG.KD.Fi24Tc.Pc.p71 : Nat.beq (runC AR SD 67 (ckL CFSG.KD.Fi24Tc.Pc.l73) 2 71 CFSG.KD.Fi24Tc.Pc.l71) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f9 : Nat.beq (runC AR SD 67 (finC AR SD (nat_lit 9) 67 75) 2 73 CFSG.KD.Fi24Tc.Pc.l73) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk9 : chk (nat_lit 9) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 9) (lo := 67) (hi := 75) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 69) CFSG.KD.Fi24Tc.Pc.p67 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 71) CFSG.KD.Fi24Tc.Pc.p69 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 73) CFSG.KD.Fi24Tc.Pc.p71 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f9

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v75 : Nat := CFSG.KD.Fi24Tc.KV0 61
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v76 : Nat := CFSG.KD.Fi24Tc.KV0 62
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l77 : List Nat := [CFSG.KD.Fi24Tc.Pc.v75, CFSG.KD.Fi24Tc.Pc.v76]
theorem CFSG.KD.Fi24Tc.Pc.p75 : Nat.beq (runC AR SD 75 (ckL CFSG.KD.Fi24Tc.Pc.l77) 2 75 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v77 : Nat := CFSG.KD.Fi24Tc.KV0 63
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v78 : Nat := CFSG.KD.Fi24Tc.KV0 64
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l79 : List Nat := [CFSG.KD.Fi24Tc.Pc.v75, CFSG.KD.Fi24Tc.Pc.v76, CFSG.KD.Fi24Tc.Pc.v77, CFSG.KD.Fi24Tc.Pc.v78]
theorem CFSG.KD.Fi24Tc.Pc.p77 : Nat.beq (runC AR SD 75 (ckL CFSG.KD.Fi24Tc.Pc.l79) 2 77 CFSG.KD.Fi24Tc.Pc.l77) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v79 : Nat := CFSG.KD.Fi24Tc.KV0 65
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v80 : Nat := CFSG.KD.Fi24Tc.KV0 66
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l81 : List Nat := [CFSG.KD.Fi24Tc.Pc.v75, CFSG.KD.Fi24Tc.Pc.v76, CFSG.KD.Fi24Tc.Pc.v77, CFSG.KD.Fi24Tc.Pc.v78, CFSG.KD.Fi24Tc.Pc.v79, CFSG.KD.Fi24Tc.Pc.v80]
theorem CFSG.KD.Fi24Tc.Pc.p79 : Nat.beq (runC AR SD 75 (ckL CFSG.KD.Fi24Tc.Pc.l81) 2 79 CFSG.KD.Fi24Tc.Pc.l79) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f10 : Nat.beq (runC AR SD 75 (finC AR SD (nat_lit 10) 75 83) 2 81 CFSG.KD.Fi24Tc.Pc.l81) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk10 : chk (nat_lit 10) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 10) (lo := 75) (hi := 83) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 77) CFSG.KD.Fi24Tc.Pc.p75 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 79) CFSG.KD.Fi24Tc.Pc.p77 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 81) CFSG.KD.Fi24Tc.Pc.p79 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f10

theorem CFSG.KD.Fi24Tc.Pc.f11 : Nat.beq (runC AR SD 83 (finC AR SD (nat_lit 11) 83 85) 2 83 []) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk11 : chk (nat_lit 11) = true :=
  (chunkOK_eq (R := AR) (D := SD) (c := nat_lit 11) (lo := 83) (hi := 85) (m := 2) rfl rfl rfl).trans CFSG.KD.Fi24Tc.Pc.f11

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a85_3 : Nat := CFSG.KD.Fi24Tc.KV0 67
theorem CFSG.KD.Fi24Tc.Pc.q85_3 : Nat.beq (powTop AR.mul (getV AR SD 85 [] (SD.na.getD 85 0)) (SD.nk.getD 85 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a85_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a85_2 : Nat := CFSG.KD.Fi24Tc.KV0 68
theorem CFSG.KD.Fi24Tc.Pc.q85_2 : Nat.beq (powTop AR.mul (getV AR SD 85 [] (SD.na.getD 85 0)) (SD.nk.getD 85 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a85_2) 1 CFSG.KD.Fi24Tc.Pc.a85_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a85_1 : Nat := CFSG.KD.Fi24Tc.KV0 69
theorem CFSG.KD.Fi24Tc.Pc.q85_1 : Nat.beq (powTop AR.mul (getV AR SD 85 [] (SD.na.getD 85 0)) (SD.nk.getD 85 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a85_1) 1 CFSG.KD.Fi24Tc.Pc.a85_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v85 : Nat := CFSG.KD.Fi24Tc.KV0 70
theorem CFSG.KD.Fi24Tc.Pc.r85 : Nat.beq (powR AR.mul AR.one (getV AR SD 85 [] (SD.na.getD 85 0)) (SD.nk.getD 85 1) 1 CFSG.KD.Fi24Tc.Pc.a85_1 true) CFSG.KD.Fi24Tc.Pc.v85 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l86 : List Nat := [CFSG.KD.Fi24Tc.Pc.v85]
theorem CFSG.KD.Fi24Tc.Pc.f12 : Nat.beq (runC AR SD 85 (finC AR SD (nat_lit 12) 85 87) 1 86 CFSG.KD.Fi24Tc.Pc.l86) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk12 : chk (nat_lit 12) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 12) (lo := 85) (hi := 87) (m := 2) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 2) (m2 := 1) (j2 := 86) (Lr := CFSG.KD.Fi24Tc.Pc.l86) ((nodeV_pow (R := AR) (D := SD) (lo := 85) (L := []) (j := 85) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 85 [] (SD.na.getD 85 0)) (SD.nk.getD 85 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q85_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q85_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q85_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r85)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f12

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v87 : Nat := CFSG.KD.Fi24Tc.KV0 71
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v88 : Nat := CFSG.KD.Fi24Tc.KV0 72
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l89 : List Nat := [CFSG.KD.Fi24Tc.Pc.v87, CFSG.KD.Fi24Tc.Pc.v88]
theorem CFSG.KD.Fi24Tc.Pc.p87 : Nat.beq (runC AR SD 87 (ckL CFSG.KD.Fi24Tc.Pc.l89) 2 87 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v89 : Nat := CFSG.KD.Fi24Tc.KV0 73
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v90 : Nat := CFSG.KD.Fi24Tc.KV0 74
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l91 : List Nat := [CFSG.KD.Fi24Tc.Pc.v87, CFSG.KD.Fi24Tc.Pc.v88, CFSG.KD.Fi24Tc.Pc.v89, CFSG.KD.Fi24Tc.Pc.v90]
theorem CFSG.KD.Fi24Tc.Pc.p89 : Nat.beq (runC AR SD 87 (ckL CFSG.KD.Fi24Tc.Pc.l91) 2 89 CFSG.KD.Fi24Tc.Pc.l89) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v91 : Nat := CFSG.KD.Fi24Tc.KV0 75
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v92 : Nat := CFSG.KD.Fi24Tc.KV0 76
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l93 : List Nat := [CFSG.KD.Fi24Tc.Pc.v87, CFSG.KD.Fi24Tc.Pc.v88, CFSG.KD.Fi24Tc.Pc.v89, CFSG.KD.Fi24Tc.Pc.v90, CFSG.KD.Fi24Tc.Pc.v91, CFSG.KD.Fi24Tc.Pc.v92]
theorem CFSG.KD.Fi24Tc.Pc.p91 : Nat.beq (runC AR SD 87 (ckL CFSG.KD.Fi24Tc.Pc.l93) 2 91 CFSG.KD.Fi24Tc.Pc.l91) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f13 : Nat.beq (runC AR SD 87 (finC AR SD (nat_lit 13) 87 95) 2 93 CFSG.KD.Fi24Tc.Pc.l93) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk13 : chk (nat_lit 13) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 13) (lo := 87) (hi := 95) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 89) CFSG.KD.Fi24Tc.Pc.p87 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 91) CFSG.KD.Fi24Tc.Pc.p89 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 93) CFSG.KD.Fi24Tc.Pc.p91 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f13

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v95 : Nat := CFSG.KD.Fi24Tc.KV0 77
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v96 : Nat := CFSG.KD.Fi24Tc.KV0 78
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l97 : List Nat := [CFSG.KD.Fi24Tc.Pc.v95, CFSG.KD.Fi24Tc.Pc.v96]
theorem CFSG.KD.Fi24Tc.Pc.p95 : Nat.beq (runC AR SD 95 (ckL CFSG.KD.Fi24Tc.Pc.l97) 2 95 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v97 : Nat := CFSG.KD.Fi24Tc.KV0 79
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v98 : Nat := CFSG.KD.Fi24Tc.KV0 80
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l99 : List Nat := [CFSG.KD.Fi24Tc.Pc.v95, CFSG.KD.Fi24Tc.Pc.v96, CFSG.KD.Fi24Tc.Pc.v97, CFSG.KD.Fi24Tc.Pc.v98]
theorem CFSG.KD.Fi24Tc.Pc.p97 : Nat.beq (runC AR SD 95 (ckL CFSG.KD.Fi24Tc.Pc.l99) 2 97 CFSG.KD.Fi24Tc.Pc.l97) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v99 : Nat := CFSG.KD.Fi24Tc.KV0 81
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v100 : Nat := CFSG.KD.Fi24Tc.KV0 82
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l101 : List Nat := [CFSG.KD.Fi24Tc.Pc.v95, CFSG.KD.Fi24Tc.Pc.v96, CFSG.KD.Fi24Tc.Pc.v97, CFSG.KD.Fi24Tc.Pc.v98, CFSG.KD.Fi24Tc.Pc.v99, CFSG.KD.Fi24Tc.Pc.v100]
theorem CFSG.KD.Fi24Tc.Pc.p99 : Nat.beq (runC AR SD 95 (ckL CFSG.KD.Fi24Tc.Pc.l101) 2 99 CFSG.KD.Fi24Tc.Pc.l99) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f14 : Nat.beq (runC AR SD 95 (finC AR SD (nat_lit 14) 95 103) 2 101 CFSG.KD.Fi24Tc.Pc.l101) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk14 : chk (nat_lit 14) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 14) (lo := 95) (hi := 103) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 97) CFSG.KD.Fi24Tc.Pc.p95 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 99) CFSG.KD.Fi24Tc.Pc.p97 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 101) CFSG.KD.Fi24Tc.Pc.p99 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f14

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v103 : Nat := CFSG.KD.Fi24Tc.KV0 83
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v104 : Nat := CFSG.KD.Fi24Tc.KV0 84
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l105 : List Nat := [CFSG.KD.Fi24Tc.Pc.v103, CFSG.KD.Fi24Tc.Pc.v104]
theorem CFSG.KD.Fi24Tc.Pc.p103 : Nat.beq (runC AR SD 103 (ckL CFSG.KD.Fi24Tc.Pc.l105) 2 103 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v105 : Nat := CFSG.KD.Fi24Tc.KV0 85
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v106 : Nat := CFSG.KD.Fi24Tc.KV0 86
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l107 : List Nat := [CFSG.KD.Fi24Tc.Pc.v103, CFSG.KD.Fi24Tc.Pc.v104, CFSG.KD.Fi24Tc.Pc.v105, CFSG.KD.Fi24Tc.Pc.v106]
theorem CFSG.KD.Fi24Tc.Pc.p105 : Nat.beq (runC AR SD 103 (ckL CFSG.KD.Fi24Tc.Pc.l107) 2 105 CFSG.KD.Fi24Tc.Pc.l105) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v107 : Nat := CFSG.KD.Fi24Tc.KV0 87
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v108 : Nat := CFSG.KD.Fi24Tc.KV0 88
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l109 : List Nat := [CFSG.KD.Fi24Tc.Pc.v103, CFSG.KD.Fi24Tc.Pc.v104, CFSG.KD.Fi24Tc.Pc.v105, CFSG.KD.Fi24Tc.Pc.v106, CFSG.KD.Fi24Tc.Pc.v107, CFSG.KD.Fi24Tc.Pc.v108]
theorem CFSG.KD.Fi24Tc.Pc.p107 : Nat.beq (runC AR SD 103 (ckL CFSG.KD.Fi24Tc.Pc.l109) 2 107 CFSG.KD.Fi24Tc.Pc.l107) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f15 : Nat.beq (runC AR SD 103 (finC AR SD (nat_lit 15) 103 110) 1 109 CFSG.KD.Fi24Tc.Pc.l109) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk15 : chk (nat_lit 15) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 15) (lo := 103) (hi := 110) (m := 7) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 7) (m2 := 5) (j2 := 105) CFSG.KD.Fi24Tc.Pc.p103 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 107) CFSG.KD.Fi24Tc.Pc.p105 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 109) CFSG.KD.Fi24Tc.Pc.p107 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f15

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a110_1 : Nat := CFSG.KD.Fi24Tc.KV0 104
theorem CFSG.KD.Fi24Tc.Pc.q110_1 : Nat.beq (powTop AR.mul (getV AR SD 110 [] (SD.na.getD 110 0)) (SD.nk.getD 110 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a110_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v110 : Nat := CFSG.KD.Fi24Tc.KV0 105
theorem CFSG.KD.Fi24Tc.Pc.r110 : Nat.beq (powR AR.mul AR.one (getV AR SD 110 [] (SD.na.getD 110 0)) (SD.nk.getD 110 1) 1 CFSG.KD.Fi24Tc.Pc.a110_1 true) CFSG.KD.Fi24Tc.Pc.v110 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l111 : List Nat := [CFSG.KD.Fi24Tc.Pc.v110]
theorem CFSG.KD.Fi24Tc.Pc.f16 : Nat.beq (runC AR SD 110 (finC AR SD (nat_lit 16) 110 112) 1 111 CFSG.KD.Fi24Tc.Pc.l111) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk16 : chk (nat_lit 16) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 16) (lo := 110) (hi := 112) (m := 2) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 2) (m2 := 1) (j2 := 111) (Lr := CFSG.KD.Fi24Tc.Pc.l111) ((nodeV_pow (R := AR) (D := SD) (lo := 110) (L := []) (j := 110) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 110 [] (SD.na.getD 110 0)) (SD.nk.getD 110 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q110_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r110)))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f16

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a112_3 : Nat := CFSG.KD.Fi24Tc.KV0 89
theorem CFSG.KD.Fi24Tc.Pc.q112_3 : Nat.beq (powTop AR.mul (getV AR SD 112 [] (SD.na.getD 112 0)) (SD.nk.getD 112 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a112_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a112_2 : Nat := CFSG.KD.Fi24Tc.KV0 90
theorem CFSG.KD.Fi24Tc.Pc.q112_2 : Nat.beq (powTop AR.mul (getV AR SD 112 [] (SD.na.getD 112 0)) (SD.nk.getD 112 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a112_2) 1 CFSG.KD.Fi24Tc.Pc.a112_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a112_1 : Nat := CFSG.KD.Fi24Tc.KV0 91
theorem CFSG.KD.Fi24Tc.Pc.q112_1 : Nat.beq (powTop AR.mul (getV AR SD 112 [] (SD.na.getD 112 0)) (SD.nk.getD 112 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a112_1) 1 CFSG.KD.Fi24Tc.Pc.a112_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v112 : Nat := CFSG.KD.Fi24Tc.KV0 92
theorem CFSG.KD.Fi24Tc.Pc.r112 : Nat.beq (powR AR.mul AR.one (getV AR SD 112 [] (SD.na.getD 112 0)) (SD.nk.getD 112 1) 1 CFSG.KD.Fi24Tc.Pc.a112_1 true) CFSG.KD.Fi24Tc.Pc.v112 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l113 : List Nat := [CFSG.KD.Fi24Tc.Pc.v112]
theorem CFSG.KD.Fi24Tc.Pc.f17 : Nat.beq (runC AR SD 112 (finC AR SD (nat_lit 17) 112 114) 1 113 CFSG.KD.Fi24Tc.Pc.l113) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk17 : chk (nat_lit 17) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 17) (lo := 112) (hi := 114) (m := 2) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 2) (m2 := 1) (j2 := 113) (Lr := CFSG.KD.Fi24Tc.Pc.l113) ((nodeV_pow (R := AR) (D := SD) (lo := 112) (L := []) (j := 112) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 112 [] (SD.na.getD 112 0)) (SD.nk.getD 112 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q112_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q112_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q112_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r112)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f17

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v114 : Nat := CFSG.KD.Fi24Tc.KV0 93
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l115 : List Nat := [CFSG.KD.Fi24Tc.Pc.v114]
theorem CFSG.KD.Fi24Tc.Pc.p114 : Nat.beq (runC AR SD 114 (ckL CFSG.KD.Fi24Tc.Pc.l115) 1 114 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a115_2 : Nat := CFSG.KD.Fi24Tc.KV0 94
theorem CFSG.KD.Fi24Tc.Pc.q115_2 : Nat.beq (powTop AR.mul (getV AR SD 114 CFSG.KD.Fi24Tc.Pc.l115 (SD.na.getD 115 0)) (SD.nk.getD 115 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a115_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v115 : Nat := CFSG.KD.Fi24Tc.KV0 95
theorem CFSG.KD.Fi24Tc.Pc.r115 : Nat.beq (powR AR.mul AR.one (getV AR SD 114 CFSG.KD.Fi24Tc.Pc.l115 (SD.na.getD 115 0)) (SD.nk.getD 115 1) 2 CFSG.KD.Fi24Tc.Pc.a115_2 true) CFSG.KD.Fi24Tc.Pc.v115 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l116 : List Nat := [CFSG.KD.Fi24Tc.Pc.v114, CFSG.KD.Fi24Tc.Pc.v115]
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v116 : Nat := CFSG.KD.Fi24Tc.KV0 96
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v117 : Nat := CFSG.KD.Fi24Tc.KV0 97
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l118 : List Nat := [CFSG.KD.Fi24Tc.Pc.v114, CFSG.KD.Fi24Tc.Pc.v115, CFSG.KD.Fi24Tc.Pc.v116, CFSG.KD.Fi24Tc.Pc.v117]
theorem CFSG.KD.Fi24Tc.Pc.p116 : Nat.beq (runC AR SD 114 (ckL CFSG.KD.Fi24Tc.Pc.l118) 2 116 CFSG.KD.Fi24Tc.Pc.l116) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f18 : Nat.beq (runC AR SD 114 (finC AR SD (nat_lit 18) 114 119) 1 118 CFSG.KD.Fi24Tc.Pc.l118) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk18 : chk (nat_lit 18) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 18) (lo := 114) (hi := 119) (m := 5) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 5) (m2 := 4) (j2 := 115) CFSG.KD.Fi24Tc.Pc.p114 rfl rfl).trans ((runC_node (m := 4) (m2 := 3) (j2 := 116) (Lr := CFSG.KD.Fi24Tc.Pc.l116) ((nodeV_pow (R := AR) (D := SD) (lo := 114) (L := CFSG.KD.Fi24Tc.Pc.l115) (j := 115) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 114 CFSG.KD.Fi24Tc.Pc.l115 (SD.na.getD 115 0)) (SD.nk.getD 115 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q115_2 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r115)))) (by quickRfl) rfl rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 118) CFSG.KD.Fi24Tc.Pc.p116 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f18

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v119 : Nat := CFSG.KD.Fi24Tc.KV0 98
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v120 : Nat := CFSG.KD.Fi24Tc.KV0 99
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l121 : List Nat := [CFSG.KD.Fi24Tc.Pc.v119, CFSG.KD.Fi24Tc.Pc.v120]
theorem CFSG.KD.Fi24Tc.Pc.p119 : Nat.beq (runC AR SD 119 (ckL CFSG.KD.Fi24Tc.Pc.l121) 2 119 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v121 : Nat := CFSG.KD.Fi24Tc.KV0 100
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v122 : Nat := CFSG.KD.Fi24Tc.KV0 101
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l123 : List Nat := [CFSG.KD.Fi24Tc.Pc.v119, CFSG.KD.Fi24Tc.Pc.v120, CFSG.KD.Fi24Tc.Pc.v121, CFSG.KD.Fi24Tc.Pc.v122]
theorem CFSG.KD.Fi24Tc.Pc.p121 : Nat.beq (runC AR SD 119 (ckL CFSG.KD.Fi24Tc.Pc.l123) 2 121 CFSG.KD.Fi24Tc.Pc.l121) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v123 : Nat := CFSG.KD.Fi24Tc.KV0 102
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v124 : Nat := CFSG.KD.Fi24Tc.KV0 103
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l125 : List Nat := [CFSG.KD.Fi24Tc.Pc.v119, CFSG.KD.Fi24Tc.Pc.v120, CFSG.KD.Fi24Tc.Pc.v121, CFSG.KD.Fi24Tc.Pc.v122, CFSG.KD.Fi24Tc.Pc.v123, CFSG.KD.Fi24Tc.Pc.v124]
theorem CFSG.KD.Fi24Tc.Pc.p123 : Nat.beq (runC AR SD 119 (ckL CFSG.KD.Fi24Tc.Pc.l125) 2 123 CFSG.KD.Fi24Tc.Pc.l123) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f19 : Nat.beq (runC AR SD 119 (finC AR SD (nat_lit 19) 119 127) 2 125 CFSG.KD.Fi24Tc.Pc.l125) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk19 : chk (nat_lit 19) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 19) (lo := 119) (hi := 127) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 121) CFSG.KD.Fi24Tc.Pc.p119 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 123) CFSG.KD.Fi24Tc.Pc.p121 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 125) CFSG.KD.Fi24Tc.Pc.p123 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f19

end
