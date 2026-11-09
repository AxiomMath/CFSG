module

public import Certificates.Kernel.Sporadic.Fi24Alpha.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Alpha KV7 "Certificates/Kernel/Sporadic/Fi24Alpha/data/v7.bin" 152491 4 23636105 13314961142507947061

public section

open CFSG.KD.Fi24Alpha CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v991 : Nat := CFSG.KD.Fi24Alpha.KV7 0
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v992 : Nat := CFSG.KD.Fi24Alpha.KV7 1
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l993 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v991, CFSG.KD.Fi24Alpha.Pc.v992]
theorem CFSG.KD.Fi24Alpha.Pc.p991 : Nat.beq (runC AR SD 991 (ckL CFSG.KD.Fi24Alpha.Pc.l993) 2 991 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v993 : Nat := CFSG.KD.Fi24Alpha.KV7 2
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v994 : Nat := CFSG.KD.Fi24Alpha.KV7 3
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l995 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v991, CFSG.KD.Fi24Alpha.Pc.v992, CFSG.KD.Fi24Alpha.Pc.v993, CFSG.KD.Fi24Alpha.Pc.v994]
theorem CFSG.KD.Fi24Alpha.Pc.p993 : Nat.beq (runC AR SD 991 (ckL CFSG.KD.Fi24Alpha.Pc.l995) 2 993 CFSG.KD.Fi24Alpha.Pc.l993) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v995 : Nat := CFSG.KD.Fi24Alpha.KV7 4
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v996 : Nat := CFSG.KD.Fi24Alpha.KV7 5
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l997 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v991, CFSG.KD.Fi24Alpha.Pc.v992, CFSG.KD.Fi24Alpha.Pc.v993, CFSG.KD.Fi24Alpha.Pc.v994, CFSG.KD.Fi24Alpha.Pc.v995, CFSG.KD.Fi24Alpha.Pc.v996]
theorem CFSG.KD.Fi24Alpha.Pc.p995 : Nat.beq (runC AR SD 991 (ckL CFSG.KD.Fi24Alpha.Pc.l997) 2 995 CFSG.KD.Fi24Alpha.Pc.l995) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v997 : Nat := CFSG.KD.Fi24Alpha.KV7 6
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v998 : Nat := CFSG.KD.Fi24Alpha.KV7 7
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l999 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v991, CFSG.KD.Fi24Alpha.Pc.v992, CFSG.KD.Fi24Alpha.Pc.v993, CFSG.KD.Fi24Alpha.Pc.v994, CFSG.KD.Fi24Alpha.Pc.v995, CFSG.KD.Fi24Alpha.Pc.v996, CFSG.KD.Fi24Alpha.Pc.v997, CFSG.KD.Fi24Alpha.Pc.v998]
theorem CFSG.KD.Fi24Alpha.Pc.p997 : Nat.beq (runC AR SD 991 (ckL CFSG.KD.Fi24Alpha.Pc.l999) 2 997 CFSG.KD.Fi24Alpha.Pc.l997) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v999 : Nat := CFSG.KD.Fi24Alpha.KV7 8
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1000 : Nat := CFSG.KD.Fi24Alpha.KV7 9
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1001 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v991, CFSG.KD.Fi24Alpha.Pc.v992, CFSG.KD.Fi24Alpha.Pc.v993, CFSG.KD.Fi24Alpha.Pc.v994, CFSG.KD.Fi24Alpha.Pc.v995, CFSG.KD.Fi24Alpha.Pc.v996, CFSG.KD.Fi24Alpha.Pc.v997, CFSG.KD.Fi24Alpha.Pc.v998, CFSG.KD.Fi24Alpha.Pc.v999, CFSG.KD.Fi24Alpha.Pc.v1000]
theorem CFSG.KD.Fi24Alpha.Pc.p999 : Nat.beq (runC AR SD 991 (ckL CFSG.KD.Fi24Alpha.Pc.l1001) 2 999 CFSG.KD.Fi24Alpha.Pc.l999) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1001 : Nat := CFSG.KD.Fi24Alpha.KV7 10
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1002 : Nat := CFSG.KD.Fi24Alpha.KV7 11
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1003 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v991, CFSG.KD.Fi24Alpha.Pc.v992, CFSG.KD.Fi24Alpha.Pc.v993, CFSG.KD.Fi24Alpha.Pc.v994, CFSG.KD.Fi24Alpha.Pc.v995, CFSG.KD.Fi24Alpha.Pc.v996, CFSG.KD.Fi24Alpha.Pc.v997, CFSG.KD.Fi24Alpha.Pc.v998, CFSG.KD.Fi24Alpha.Pc.v999, CFSG.KD.Fi24Alpha.Pc.v1000, CFSG.KD.Fi24Alpha.Pc.v1001, CFSG.KD.Fi24Alpha.Pc.v1002]
theorem CFSG.KD.Fi24Alpha.Pc.p1001 : Nat.beq (runC AR SD 991 (ckL CFSG.KD.Fi24Alpha.Pc.l1003) 2 1001 CFSG.KD.Fi24Alpha.Pc.l1001) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1003 : Nat := CFSG.KD.Fi24Alpha.KV7 12
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1004 : Nat := CFSG.KD.Fi24Alpha.KV7 13
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1005 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v991, CFSG.KD.Fi24Alpha.Pc.v992, CFSG.KD.Fi24Alpha.Pc.v993, CFSG.KD.Fi24Alpha.Pc.v994, CFSG.KD.Fi24Alpha.Pc.v995, CFSG.KD.Fi24Alpha.Pc.v996, CFSG.KD.Fi24Alpha.Pc.v997, CFSG.KD.Fi24Alpha.Pc.v998, CFSG.KD.Fi24Alpha.Pc.v999, CFSG.KD.Fi24Alpha.Pc.v1000, CFSG.KD.Fi24Alpha.Pc.v1001, CFSG.KD.Fi24Alpha.Pc.v1002, CFSG.KD.Fi24Alpha.Pc.v1003, CFSG.KD.Fi24Alpha.Pc.v1004]
theorem CFSG.KD.Fi24Alpha.Pc.p1003 : Nat.beq (runC AR SD 991 (ckL CFSG.KD.Fi24Alpha.Pc.l1005) 2 1003 CFSG.KD.Fi24Alpha.Pc.l1003) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1005 : Nat := CFSG.KD.Fi24Alpha.KV7 14
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1006 : Nat := CFSG.KD.Fi24Alpha.KV7 15
theorem CFSG.KD.Fi24Alpha.Pc.f70 : Nat.beq (runC AR SD 991 (finC AR SD (nat_lit 70) 991 1007) 2 1005 CFSG.KD.Fi24Alpha.Pc.l1005) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk70 : chk (nat_lit 70) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 70) (lo := 991) (hi := 1007) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 993) CFSG.KD.Fi24Alpha.Pc.p991 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 995) CFSG.KD.Fi24Alpha.Pc.p993 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 997) CFSG.KD.Fi24Alpha.Pc.p995 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 999) CFSG.KD.Fi24Alpha.Pc.p997 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1001) CFSG.KD.Fi24Alpha.Pc.p999 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1003) CFSG.KD.Fi24Alpha.Pc.p1001 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1005) CFSG.KD.Fi24Alpha.Pc.p1003 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f70

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1007 : Nat := CFSG.KD.Fi24Alpha.KV7 16
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1008 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1007]
theorem CFSG.KD.Fi24Alpha.Pc.p1007 : Nat.beq (runC AR SD 1007 (ckL CFSG.KD.Fi24Alpha.Pc.l1008) 1 1007 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1008 : Nat := CFSG.KD.Fi24Alpha.KV7 17
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1009 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1007, CFSG.KD.Fi24Alpha.Pc.v1008]
theorem CFSG.KD.Fi24Alpha.Pc.p1008 : Nat.beq (runC AR SD 1007 (ckL CFSG.KD.Fi24Alpha.Pc.l1009) 1 1008 CFSG.KD.Fi24Alpha.Pc.l1008) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1009 : Nat := CFSG.KD.Fi24Alpha.KV7 18
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1010 : Nat := CFSG.KD.Fi24Alpha.KV7 19
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1011 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1007, CFSG.KD.Fi24Alpha.Pc.v1008, CFSG.KD.Fi24Alpha.Pc.v1009, CFSG.KD.Fi24Alpha.Pc.v1010]
theorem CFSG.KD.Fi24Alpha.Pc.p1009 : Nat.beq (runC AR SD 1007 (ckL CFSG.KD.Fi24Alpha.Pc.l1011) 2 1009 CFSG.KD.Fi24Alpha.Pc.l1009) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1011 : Nat := CFSG.KD.Fi24Alpha.KV7 20
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1012 : Nat := CFSG.KD.Fi24Alpha.KV7 21
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1013 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1007, CFSG.KD.Fi24Alpha.Pc.v1008, CFSG.KD.Fi24Alpha.Pc.v1009, CFSG.KD.Fi24Alpha.Pc.v1010, CFSG.KD.Fi24Alpha.Pc.v1011, CFSG.KD.Fi24Alpha.Pc.v1012]
theorem CFSG.KD.Fi24Alpha.Pc.p1011 : Nat.beq (runC AR SD 1007 (ckL CFSG.KD.Fi24Alpha.Pc.l1013) 2 1011 CFSG.KD.Fi24Alpha.Pc.l1011) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1013 : Nat := CFSG.KD.Fi24Alpha.KV7 22
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1014 : Nat := CFSG.KD.Fi24Alpha.KV7 23
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1015 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1007, CFSG.KD.Fi24Alpha.Pc.v1008, CFSG.KD.Fi24Alpha.Pc.v1009, CFSG.KD.Fi24Alpha.Pc.v1010, CFSG.KD.Fi24Alpha.Pc.v1011, CFSG.KD.Fi24Alpha.Pc.v1012, CFSG.KD.Fi24Alpha.Pc.v1013, CFSG.KD.Fi24Alpha.Pc.v1014]
theorem CFSG.KD.Fi24Alpha.Pc.p1013 : Nat.beq (runC AR SD 1007 (ckL CFSG.KD.Fi24Alpha.Pc.l1015) 2 1013 CFSG.KD.Fi24Alpha.Pc.l1013) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1015 : Nat := CFSG.KD.Fi24Alpha.KV7 24
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1016 : Nat := CFSG.KD.Fi24Alpha.KV7 25
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1017 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1007, CFSG.KD.Fi24Alpha.Pc.v1008, CFSG.KD.Fi24Alpha.Pc.v1009, CFSG.KD.Fi24Alpha.Pc.v1010, CFSG.KD.Fi24Alpha.Pc.v1011, CFSG.KD.Fi24Alpha.Pc.v1012, CFSG.KD.Fi24Alpha.Pc.v1013, CFSG.KD.Fi24Alpha.Pc.v1014, CFSG.KD.Fi24Alpha.Pc.v1015, CFSG.KD.Fi24Alpha.Pc.v1016]
theorem CFSG.KD.Fi24Alpha.Pc.p1015 : Nat.beq (runC AR SD 1007 (ckL CFSG.KD.Fi24Alpha.Pc.l1017) 2 1015 CFSG.KD.Fi24Alpha.Pc.l1015) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1017 : Nat := CFSG.KD.Fi24Alpha.KV7 26
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1018 : Nat := CFSG.KD.Fi24Alpha.KV7 27
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1019 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1007, CFSG.KD.Fi24Alpha.Pc.v1008, CFSG.KD.Fi24Alpha.Pc.v1009, CFSG.KD.Fi24Alpha.Pc.v1010, CFSG.KD.Fi24Alpha.Pc.v1011, CFSG.KD.Fi24Alpha.Pc.v1012, CFSG.KD.Fi24Alpha.Pc.v1013, CFSG.KD.Fi24Alpha.Pc.v1014, CFSG.KD.Fi24Alpha.Pc.v1015, CFSG.KD.Fi24Alpha.Pc.v1016, CFSG.KD.Fi24Alpha.Pc.v1017, CFSG.KD.Fi24Alpha.Pc.v1018]
theorem CFSG.KD.Fi24Alpha.Pc.p1017 : Nat.beq (runC AR SD 1007 (ckL CFSG.KD.Fi24Alpha.Pc.l1019) 2 1017 CFSG.KD.Fi24Alpha.Pc.l1017) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1019 : Nat := CFSG.KD.Fi24Alpha.KV7 28
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1020 : Nat := CFSG.KD.Fi24Alpha.KV7 29
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1021 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1007, CFSG.KD.Fi24Alpha.Pc.v1008, CFSG.KD.Fi24Alpha.Pc.v1009, CFSG.KD.Fi24Alpha.Pc.v1010, CFSG.KD.Fi24Alpha.Pc.v1011, CFSG.KD.Fi24Alpha.Pc.v1012, CFSG.KD.Fi24Alpha.Pc.v1013, CFSG.KD.Fi24Alpha.Pc.v1014, CFSG.KD.Fi24Alpha.Pc.v1015, CFSG.KD.Fi24Alpha.Pc.v1016, CFSG.KD.Fi24Alpha.Pc.v1017, CFSG.KD.Fi24Alpha.Pc.v1018, CFSG.KD.Fi24Alpha.Pc.v1019, CFSG.KD.Fi24Alpha.Pc.v1020]
theorem CFSG.KD.Fi24Alpha.Pc.p1019 : Nat.beq (runC AR SD 1007 (ckL CFSG.KD.Fi24Alpha.Pc.l1021) 2 1019 CFSG.KD.Fi24Alpha.Pc.l1019) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1021 : Nat := CFSG.KD.Fi24Alpha.KV7 30
theorem CFSG.KD.Fi24Alpha.Pc.f71 : Nat.beq (runC AR SD 1007 (finC AR SD (nat_lit 71) 1007 1022) 1 1021 CFSG.KD.Fi24Alpha.Pc.l1021) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk71 : chk (nat_lit 71) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 71) (lo := 1007) (hi := 1022) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 14) (j2 := 1008) CFSG.KD.Fi24Alpha.Pc.p1007 rfl rfl).trans ((runC_seq (m := 14) (m2 := 13) (j2 := 1009) CFSG.KD.Fi24Alpha.Pc.p1008 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 1011) CFSG.KD.Fi24Alpha.Pc.p1009 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 1013) CFSG.KD.Fi24Alpha.Pc.p1011 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 1015) CFSG.KD.Fi24Alpha.Pc.p1013 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 1017) CFSG.KD.Fi24Alpha.Pc.p1015 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 1019) CFSG.KD.Fi24Alpha.Pc.p1017 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 1021) CFSG.KD.Fi24Alpha.Pc.p1019 rfl rfl)))))))))).trans CFSG.KD.Fi24Alpha.Pc.f71

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1022 : Nat := CFSG.KD.Fi24Alpha.KV7 31
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1023 : Nat := CFSG.KD.Fi24Alpha.KV7 32
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1024 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1022, CFSG.KD.Fi24Alpha.Pc.v1023]
theorem CFSG.KD.Fi24Alpha.Pc.p1022 : Nat.beq (runC AR SD 1022 (ckL CFSG.KD.Fi24Alpha.Pc.l1024) 2 1022 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1024 : Nat := CFSG.KD.Fi24Alpha.KV7 33
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1025 : Nat := CFSG.KD.Fi24Alpha.KV7 34
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1026 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1022, CFSG.KD.Fi24Alpha.Pc.v1023, CFSG.KD.Fi24Alpha.Pc.v1024, CFSG.KD.Fi24Alpha.Pc.v1025]
theorem CFSG.KD.Fi24Alpha.Pc.p1024 : Nat.beq (runC AR SD 1022 (ckL CFSG.KD.Fi24Alpha.Pc.l1026) 2 1024 CFSG.KD.Fi24Alpha.Pc.l1024) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1026 : Nat := CFSG.KD.Fi24Alpha.KV7 35
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1027 : Nat := CFSG.KD.Fi24Alpha.KV7 36
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1028 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1022, CFSG.KD.Fi24Alpha.Pc.v1023, CFSG.KD.Fi24Alpha.Pc.v1024, CFSG.KD.Fi24Alpha.Pc.v1025, CFSG.KD.Fi24Alpha.Pc.v1026, CFSG.KD.Fi24Alpha.Pc.v1027]
theorem CFSG.KD.Fi24Alpha.Pc.p1026 : Nat.beq (runC AR SD 1022 (ckL CFSG.KD.Fi24Alpha.Pc.l1028) 2 1026 CFSG.KD.Fi24Alpha.Pc.l1026) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1028 : Nat := CFSG.KD.Fi24Alpha.KV7 37
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1029 : Nat := CFSG.KD.Fi24Alpha.KV7 38
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1030 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1022, CFSG.KD.Fi24Alpha.Pc.v1023, CFSG.KD.Fi24Alpha.Pc.v1024, CFSG.KD.Fi24Alpha.Pc.v1025, CFSG.KD.Fi24Alpha.Pc.v1026, CFSG.KD.Fi24Alpha.Pc.v1027, CFSG.KD.Fi24Alpha.Pc.v1028, CFSG.KD.Fi24Alpha.Pc.v1029]
theorem CFSG.KD.Fi24Alpha.Pc.p1028 : Nat.beq (runC AR SD 1022 (ckL CFSG.KD.Fi24Alpha.Pc.l1030) 2 1028 CFSG.KD.Fi24Alpha.Pc.l1028) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1030 : Nat := CFSG.KD.Fi24Alpha.KV7 39
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1031 : Nat := CFSG.KD.Fi24Alpha.KV7 40
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1032 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1022, CFSG.KD.Fi24Alpha.Pc.v1023, CFSG.KD.Fi24Alpha.Pc.v1024, CFSG.KD.Fi24Alpha.Pc.v1025, CFSG.KD.Fi24Alpha.Pc.v1026, CFSG.KD.Fi24Alpha.Pc.v1027, CFSG.KD.Fi24Alpha.Pc.v1028, CFSG.KD.Fi24Alpha.Pc.v1029, CFSG.KD.Fi24Alpha.Pc.v1030, CFSG.KD.Fi24Alpha.Pc.v1031]
theorem CFSG.KD.Fi24Alpha.Pc.p1030 : Nat.beq (runC AR SD 1022 (ckL CFSG.KD.Fi24Alpha.Pc.l1032) 2 1030 CFSG.KD.Fi24Alpha.Pc.l1030) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1032 : Nat := CFSG.KD.Fi24Alpha.KV7 41
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1033 : Nat := CFSG.KD.Fi24Alpha.KV7 42
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1034 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1022, CFSG.KD.Fi24Alpha.Pc.v1023, CFSG.KD.Fi24Alpha.Pc.v1024, CFSG.KD.Fi24Alpha.Pc.v1025, CFSG.KD.Fi24Alpha.Pc.v1026, CFSG.KD.Fi24Alpha.Pc.v1027, CFSG.KD.Fi24Alpha.Pc.v1028, CFSG.KD.Fi24Alpha.Pc.v1029, CFSG.KD.Fi24Alpha.Pc.v1030, CFSG.KD.Fi24Alpha.Pc.v1031, CFSG.KD.Fi24Alpha.Pc.v1032, CFSG.KD.Fi24Alpha.Pc.v1033]
theorem CFSG.KD.Fi24Alpha.Pc.p1032 : Nat.beq (runC AR SD 1022 (ckL CFSG.KD.Fi24Alpha.Pc.l1034) 2 1032 CFSG.KD.Fi24Alpha.Pc.l1032) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1034 : Nat := CFSG.KD.Fi24Alpha.KV7 43
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1035 : Nat := CFSG.KD.Fi24Alpha.KV7 44
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1036 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1022, CFSG.KD.Fi24Alpha.Pc.v1023, CFSG.KD.Fi24Alpha.Pc.v1024, CFSG.KD.Fi24Alpha.Pc.v1025, CFSG.KD.Fi24Alpha.Pc.v1026, CFSG.KD.Fi24Alpha.Pc.v1027, CFSG.KD.Fi24Alpha.Pc.v1028, CFSG.KD.Fi24Alpha.Pc.v1029, CFSG.KD.Fi24Alpha.Pc.v1030, CFSG.KD.Fi24Alpha.Pc.v1031, CFSG.KD.Fi24Alpha.Pc.v1032, CFSG.KD.Fi24Alpha.Pc.v1033, CFSG.KD.Fi24Alpha.Pc.v1034, CFSG.KD.Fi24Alpha.Pc.v1035]
theorem CFSG.KD.Fi24Alpha.Pc.p1034 : Nat.beq (runC AR SD 1022 (ckL CFSG.KD.Fi24Alpha.Pc.l1036) 2 1034 CFSG.KD.Fi24Alpha.Pc.l1034) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1036 : Nat := CFSG.KD.Fi24Alpha.KV7 45
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1037 : Nat := CFSG.KD.Fi24Alpha.KV7 46
theorem CFSG.KD.Fi24Alpha.Pc.f72 : Nat.beq (runC AR SD 1022 (finC AR SD (nat_lit 72) 1022 1038) 2 1036 CFSG.KD.Fi24Alpha.Pc.l1036) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk72 : chk (nat_lit 72) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 72) (lo := 1022) (hi := 1038) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1024) CFSG.KD.Fi24Alpha.Pc.p1022 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1026) CFSG.KD.Fi24Alpha.Pc.p1024 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1028) CFSG.KD.Fi24Alpha.Pc.p1026 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1030) CFSG.KD.Fi24Alpha.Pc.p1028 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1032) CFSG.KD.Fi24Alpha.Pc.p1030 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1034) CFSG.KD.Fi24Alpha.Pc.p1032 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1036) CFSG.KD.Fi24Alpha.Pc.p1034 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f72

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1038 : Nat := CFSG.KD.Fi24Alpha.KV7 47
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1039 : Nat := CFSG.KD.Fi24Alpha.KV7 48
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1040 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1038, CFSG.KD.Fi24Alpha.Pc.v1039]
theorem CFSG.KD.Fi24Alpha.Pc.p1038 : Nat.beq (runC AR SD 1038 (ckL CFSG.KD.Fi24Alpha.Pc.l1040) 2 1038 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1040 : Nat := CFSG.KD.Fi24Alpha.KV7 49
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1041 : Nat := CFSG.KD.Fi24Alpha.KV7 50
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1042 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1038, CFSG.KD.Fi24Alpha.Pc.v1039, CFSG.KD.Fi24Alpha.Pc.v1040, CFSG.KD.Fi24Alpha.Pc.v1041]
theorem CFSG.KD.Fi24Alpha.Pc.p1040 : Nat.beq (runC AR SD 1038 (ckL CFSG.KD.Fi24Alpha.Pc.l1042) 2 1040 CFSG.KD.Fi24Alpha.Pc.l1040) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1042 : Nat := CFSG.KD.Fi24Alpha.KV7 51
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1043 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1038, CFSG.KD.Fi24Alpha.Pc.v1039, CFSG.KD.Fi24Alpha.Pc.v1040, CFSG.KD.Fi24Alpha.Pc.v1041, CFSG.KD.Fi24Alpha.Pc.v1042]
theorem CFSG.KD.Fi24Alpha.Pc.p1042 : Nat.beq (runC AR SD 1038 (ckL CFSG.KD.Fi24Alpha.Pc.l1043) 1 1042 CFSG.KD.Fi24Alpha.Pc.l1042) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1043 : Nat := CFSG.KD.Fi24Alpha.KV7 52
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1044 : Nat := CFSG.KD.Fi24Alpha.KV7 53
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1045 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1038, CFSG.KD.Fi24Alpha.Pc.v1039, CFSG.KD.Fi24Alpha.Pc.v1040, CFSG.KD.Fi24Alpha.Pc.v1041, CFSG.KD.Fi24Alpha.Pc.v1042, CFSG.KD.Fi24Alpha.Pc.v1043, CFSG.KD.Fi24Alpha.Pc.v1044]
theorem CFSG.KD.Fi24Alpha.Pc.p1043 : Nat.beq (runC AR SD 1038 (ckL CFSG.KD.Fi24Alpha.Pc.l1045) 2 1043 CFSG.KD.Fi24Alpha.Pc.l1043) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1045 : Nat := CFSG.KD.Fi24Alpha.KV7 54
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1046 : Nat := CFSG.KD.Fi24Alpha.KV7 55
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1047 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1038, CFSG.KD.Fi24Alpha.Pc.v1039, CFSG.KD.Fi24Alpha.Pc.v1040, CFSG.KD.Fi24Alpha.Pc.v1041, CFSG.KD.Fi24Alpha.Pc.v1042, CFSG.KD.Fi24Alpha.Pc.v1043, CFSG.KD.Fi24Alpha.Pc.v1044, CFSG.KD.Fi24Alpha.Pc.v1045, CFSG.KD.Fi24Alpha.Pc.v1046]
theorem CFSG.KD.Fi24Alpha.Pc.p1045 : Nat.beq (runC AR SD 1038 (ckL CFSG.KD.Fi24Alpha.Pc.l1047) 2 1045 CFSG.KD.Fi24Alpha.Pc.l1045) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1047 : Nat := CFSG.KD.Fi24Alpha.KV7 56
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1048 : Nat := CFSG.KD.Fi24Alpha.KV7 57
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1049 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1038, CFSG.KD.Fi24Alpha.Pc.v1039, CFSG.KD.Fi24Alpha.Pc.v1040, CFSG.KD.Fi24Alpha.Pc.v1041, CFSG.KD.Fi24Alpha.Pc.v1042, CFSG.KD.Fi24Alpha.Pc.v1043, CFSG.KD.Fi24Alpha.Pc.v1044, CFSG.KD.Fi24Alpha.Pc.v1045, CFSG.KD.Fi24Alpha.Pc.v1046, CFSG.KD.Fi24Alpha.Pc.v1047, CFSG.KD.Fi24Alpha.Pc.v1048]
theorem CFSG.KD.Fi24Alpha.Pc.p1047 : Nat.beq (runC AR SD 1038 (ckL CFSG.KD.Fi24Alpha.Pc.l1049) 2 1047 CFSG.KD.Fi24Alpha.Pc.l1047) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1049 : Nat := CFSG.KD.Fi24Alpha.KV7 58
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1050 : Nat := CFSG.KD.Fi24Alpha.KV7 59
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1051 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1038, CFSG.KD.Fi24Alpha.Pc.v1039, CFSG.KD.Fi24Alpha.Pc.v1040, CFSG.KD.Fi24Alpha.Pc.v1041, CFSG.KD.Fi24Alpha.Pc.v1042, CFSG.KD.Fi24Alpha.Pc.v1043, CFSG.KD.Fi24Alpha.Pc.v1044, CFSG.KD.Fi24Alpha.Pc.v1045, CFSG.KD.Fi24Alpha.Pc.v1046, CFSG.KD.Fi24Alpha.Pc.v1047, CFSG.KD.Fi24Alpha.Pc.v1048, CFSG.KD.Fi24Alpha.Pc.v1049, CFSG.KD.Fi24Alpha.Pc.v1050]
theorem CFSG.KD.Fi24Alpha.Pc.p1049 : Nat.beq (runC AR SD 1038 (ckL CFSG.KD.Fi24Alpha.Pc.l1051) 2 1049 CFSG.KD.Fi24Alpha.Pc.l1049) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1051 : Nat := CFSG.KD.Fi24Alpha.KV7 60
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1052 : Nat := CFSG.KD.Fi24Alpha.KV7 61
theorem CFSG.KD.Fi24Alpha.Pc.f73 : Nat.beq (runC AR SD 1038 (finC AR SD (nat_lit 73) 1038 1053) 2 1051 CFSG.KD.Fi24Alpha.Pc.l1051) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk73 : chk (nat_lit 73) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 73) (lo := 1038) (hi := 1053) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 1040) CFSG.KD.Fi24Alpha.Pc.p1038 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 1042) CFSG.KD.Fi24Alpha.Pc.p1040 rfl rfl).trans ((runC_seq (m := 11) (m2 := 10) (j2 := 1043) CFSG.KD.Fi24Alpha.Pc.p1042 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1045) CFSG.KD.Fi24Alpha.Pc.p1043 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1047) CFSG.KD.Fi24Alpha.Pc.p1045 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1049) CFSG.KD.Fi24Alpha.Pc.p1047 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1051) CFSG.KD.Fi24Alpha.Pc.p1049 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f73

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1053 : Nat := CFSG.KD.Fi24Alpha.KV7 62
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1054 : Nat := CFSG.KD.Fi24Alpha.KV7 63
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1055 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1053, CFSG.KD.Fi24Alpha.Pc.v1054]
theorem CFSG.KD.Fi24Alpha.Pc.p1053 : Nat.beq (runC AR SD 1053 (ckL CFSG.KD.Fi24Alpha.Pc.l1055) 2 1053 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1055 : Nat := CFSG.KD.Fi24Alpha.KV7 64
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1056 : Nat := CFSG.KD.Fi24Alpha.KV7 65
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1057 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1053, CFSG.KD.Fi24Alpha.Pc.v1054, CFSG.KD.Fi24Alpha.Pc.v1055, CFSG.KD.Fi24Alpha.Pc.v1056]
theorem CFSG.KD.Fi24Alpha.Pc.p1055 : Nat.beq (runC AR SD 1053 (ckL CFSG.KD.Fi24Alpha.Pc.l1057) 2 1055 CFSG.KD.Fi24Alpha.Pc.l1055) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1057 : Nat := CFSG.KD.Fi24Alpha.KV7 66
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1058 : Nat := CFSG.KD.Fi24Alpha.KV7 67
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1059 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1053, CFSG.KD.Fi24Alpha.Pc.v1054, CFSG.KD.Fi24Alpha.Pc.v1055, CFSG.KD.Fi24Alpha.Pc.v1056, CFSG.KD.Fi24Alpha.Pc.v1057, CFSG.KD.Fi24Alpha.Pc.v1058]
theorem CFSG.KD.Fi24Alpha.Pc.p1057 : Nat.beq (runC AR SD 1053 (ckL CFSG.KD.Fi24Alpha.Pc.l1059) 2 1057 CFSG.KD.Fi24Alpha.Pc.l1057) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1059 : Nat := CFSG.KD.Fi24Alpha.KV7 68
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1060 : Nat := CFSG.KD.Fi24Alpha.KV7 69
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1061 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1053, CFSG.KD.Fi24Alpha.Pc.v1054, CFSG.KD.Fi24Alpha.Pc.v1055, CFSG.KD.Fi24Alpha.Pc.v1056, CFSG.KD.Fi24Alpha.Pc.v1057, CFSG.KD.Fi24Alpha.Pc.v1058, CFSG.KD.Fi24Alpha.Pc.v1059, CFSG.KD.Fi24Alpha.Pc.v1060]
theorem CFSG.KD.Fi24Alpha.Pc.p1059 : Nat.beq (runC AR SD 1053 (ckL CFSG.KD.Fi24Alpha.Pc.l1061) 2 1059 CFSG.KD.Fi24Alpha.Pc.l1059) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1061 : Nat := CFSG.KD.Fi24Alpha.KV7 70
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1062 : Nat := CFSG.KD.Fi24Alpha.KV7 71
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1063 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1053, CFSG.KD.Fi24Alpha.Pc.v1054, CFSG.KD.Fi24Alpha.Pc.v1055, CFSG.KD.Fi24Alpha.Pc.v1056, CFSG.KD.Fi24Alpha.Pc.v1057, CFSG.KD.Fi24Alpha.Pc.v1058, CFSG.KD.Fi24Alpha.Pc.v1059, CFSG.KD.Fi24Alpha.Pc.v1060, CFSG.KD.Fi24Alpha.Pc.v1061, CFSG.KD.Fi24Alpha.Pc.v1062]
theorem CFSG.KD.Fi24Alpha.Pc.p1061 : Nat.beq (runC AR SD 1053 (ckL CFSG.KD.Fi24Alpha.Pc.l1063) 2 1061 CFSG.KD.Fi24Alpha.Pc.l1061) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1063 : Nat := CFSG.KD.Fi24Alpha.KV7 72
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1064 : Nat := CFSG.KD.Fi24Alpha.KV7 73
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1065 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1053, CFSG.KD.Fi24Alpha.Pc.v1054, CFSG.KD.Fi24Alpha.Pc.v1055, CFSG.KD.Fi24Alpha.Pc.v1056, CFSG.KD.Fi24Alpha.Pc.v1057, CFSG.KD.Fi24Alpha.Pc.v1058, CFSG.KD.Fi24Alpha.Pc.v1059, CFSG.KD.Fi24Alpha.Pc.v1060, CFSG.KD.Fi24Alpha.Pc.v1061, CFSG.KD.Fi24Alpha.Pc.v1062, CFSG.KD.Fi24Alpha.Pc.v1063, CFSG.KD.Fi24Alpha.Pc.v1064]
theorem CFSG.KD.Fi24Alpha.Pc.p1063 : Nat.beq (runC AR SD 1053 (ckL CFSG.KD.Fi24Alpha.Pc.l1065) 2 1063 CFSG.KD.Fi24Alpha.Pc.l1063) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1065 : Nat := CFSG.KD.Fi24Alpha.KV7 74
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1066 : Nat := CFSG.KD.Fi24Alpha.KV7 75
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1067 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1053, CFSG.KD.Fi24Alpha.Pc.v1054, CFSG.KD.Fi24Alpha.Pc.v1055, CFSG.KD.Fi24Alpha.Pc.v1056, CFSG.KD.Fi24Alpha.Pc.v1057, CFSG.KD.Fi24Alpha.Pc.v1058, CFSG.KD.Fi24Alpha.Pc.v1059, CFSG.KD.Fi24Alpha.Pc.v1060, CFSG.KD.Fi24Alpha.Pc.v1061, CFSG.KD.Fi24Alpha.Pc.v1062, CFSG.KD.Fi24Alpha.Pc.v1063, CFSG.KD.Fi24Alpha.Pc.v1064, CFSG.KD.Fi24Alpha.Pc.v1065, CFSG.KD.Fi24Alpha.Pc.v1066]
theorem CFSG.KD.Fi24Alpha.Pc.p1065 : Nat.beq (runC AR SD 1053 (ckL CFSG.KD.Fi24Alpha.Pc.l1067) 2 1065 CFSG.KD.Fi24Alpha.Pc.l1065) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1067 : Nat := CFSG.KD.Fi24Alpha.KV7 76
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1068 : Nat := CFSG.KD.Fi24Alpha.KV7 77
theorem CFSG.KD.Fi24Alpha.Pc.f74 : Nat.beq (runC AR SD 1053 (finC AR SD (nat_lit 74) 1053 1069) 2 1067 CFSG.KD.Fi24Alpha.Pc.l1067) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk74 : chk (nat_lit 74) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 74) (lo := 1053) (hi := 1069) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1055) CFSG.KD.Fi24Alpha.Pc.p1053 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1057) CFSG.KD.Fi24Alpha.Pc.p1055 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1059) CFSG.KD.Fi24Alpha.Pc.p1057 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1061) CFSG.KD.Fi24Alpha.Pc.p1059 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1063) CFSG.KD.Fi24Alpha.Pc.p1061 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1065) CFSG.KD.Fi24Alpha.Pc.p1063 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1067) CFSG.KD.Fi24Alpha.Pc.p1065 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f74

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1069 : Nat := CFSG.KD.Fi24Alpha.KV7 78
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1070 : Nat := CFSG.KD.Fi24Alpha.KV7 79
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1071 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1069, CFSG.KD.Fi24Alpha.Pc.v1070]
theorem CFSG.KD.Fi24Alpha.Pc.p1069 : Nat.beq (runC AR SD 1069 (ckL CFSG.KD.Fi24Alpha.Pc.l1071) 2 1069 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1071 : Nat := CFSG.KD.Fi24Alpha.KV7 80
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1072 : Nat := CFSG.KD.Fi24Alpha.KV7 81
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1073 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1069, CFSG.KD.Fi24Alpha.Pc.v1070, CFSG.KD.Fi24Alpha.Pc.v1071, CFSG.KD.Fi24Alpha.Pc.v1072]
theorem CFSG.KD.Fi24Alpha.Pc.p1071 : Nat.beq (runC AR SD 1069 (ckL CFSG.KD.Fi24Alpha.Pc.l1073) 2 1071 CFSG.KD.Fi24Alpha.Pc.l1071) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1073 : Nat := CFSG.KD.Fi24Alpha.KV7 82
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1074 : Nat := CFSG.KD.Fi24Alpha.KV7 83
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1075 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1069, CFSG.KD.Fi24Alpha.Pc.v1070, CFSG.KD.Fi24Alpha.Pc.v1071, CFSG.KD.Fi24Alpha.Pc.v1072, CFSG.KD.Fi24Alpha.Pc.v1073, CFSG.KD.Fi24Alpha.Pc.v1074]
theorem CFSG.KD.Fi24Alpha.Pc.p1073 : Nat.beq (runC AR SD 1069 (ckL CFSG.KD.Fi24Alpha.Pc.l1075) 2 1073 CFSG.KD.Fi24Alpha.Pc.l1073) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1075 : Nat := CFSG.KD.Fi24Alpha.KV7 84
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1076 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1069, CFSG.KD.Fi24Alpha.Pc.v1070, CFSG.KD.Fi24Alpha.Pc.v1071, CFSG.KD.Fi24Alpha.Pc.v1072, CFSG.KD.Fi24Alpha.Pc.v1073, CFSG.KD.Fi24Alpha.Pc.v1074, CFSG.KD.Fi24Alpha.Pc.v1075]
theorem CFSG.KD.Fi24Alpha.Pc.p1075 : Nat.beq (runC AR SD 1069 (ckL CFSG.KD.Fi24Alpha.Pc.l1076) 1 1075 CFSG.KD.Fi24Alpha.Pc.l1075) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1076 : Nat := CFSG.KD.Fi24Alpha.KV7 85
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1077 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1069, CFSG.KD.Fi24Alpha.Pc.v1070, CFSG.KD.Fi24Alpha.Pc.v1071, CFSG.KD.Fi24Alpha.Pc.v1072, CFSG.KD.Fi24Alpha.Pc.v1073, CFSG.KD.Fi24Alpha.Pc.v1074, CFSG.KD.Fi24Alpha.Pc.v1075, CFSG.KD.Fi24Alpha.Pc.v1076]
theorem CFSG.KD.Fi24Alpha.Pc.p1076 : Nat.beq (runC AR SD 1069 (ckL CFSG.KD.Fi24Alpha.Pc.l1077) 1 1076 CFSG.KD.Fi24Alpha.Pc.l1076) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1077 : Nat := CFSG.KD.Fi24Alpha.KV7 86
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1078 : Nat := CFSG.KD.Fi24Alpha.KV7 87
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1079 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1069, CFSG.KD.Fi24Alpha.Pc.v1070, CFSG.KD.Fi24Alpha.Pc.v1071, CFSG.KD.Fi24Alpha.Pc.v1072, CFSG.KD.Fi24Alpha.Pc.v1073, CFSG.KD.Fi24Alpha.Pc.v1074, CFSG.KD.Fi24Alpha.Pc.v1075, CFSG.KD.Fi24Alpha.Pc.v1076, CFSG.KD.Fi24Alpha.Pc.v1077, CFSG.KD.Fi24Alpha.Pc.v1078]
theorem CFSG.KD.Fi24Alpha.Pc.p1077 : Nat.beq (runC AR SD 1069 (ckL CFSG.KD.Fi24Alpha.Pc.l1079) 2 1077 CFSG.KD.Fi24Alpha.Pc.l1077) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1079 : Nat := CFSG.KD.Fi24Alpha.KV7 88
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1080 : Nat := CFSG.KD.Fi24Alpha.KV7 89
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1081 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1069, CFSG.KD.Fi24Alpha.Pc.v1070, CFSG.KD.Fi24Alpha.Pc.v1071, CFSG.KD.Fi24Alpha.Pc.v1072, CFSG.KD.Fi24Alpha.Pc.v1073, CFSG.KD.Fi24Alpha.Pc.v1074, CFSG.KD.Fi24Alpha.Pc.v1075, CFSG.KD.Fi24Alpha.Pc.v1076, CFSG.KD.Fi24Alpha.Pc.v1077, CFSG.KD.Fi24Alpha.Pc.v1078, CFSG.KD.Fi24Alpha.Pc.v1079, CFSG.KD.Fi24Alpha.Pc.v1080]
theorem CFSG.KD.Fi24Alpha.Pc.p1079 : Nat.beq (runC AR SD 1069 (ckL CFSG.KD.Fi24Alpha.Pc.l1081) 2 1079 CFSG.KD.Fi24Alpha.Pc.l1079) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1081 : Nat := CFSG.KD.Fi24Alpha.KV7 90
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1082 : Nat := CFSG.KD.Fi24Alpha.KV7 91
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1083 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1069, CFSG.KD.Fi24Alpha.Pc.v1070, CFSG.KD.Fi24Alpha.Pc.v1071, CFSG.KD.Fi24Alpha.Pc.v1072, CFSG.KD.Fi24Alpha.Pc.v1073, CFSG.KD.Fi24Alpha.Pc.v1074, CFSG.KD.Fi24Alpha.Pc.v1075, CFSG.KD.Fi24Alpha.Pc.v1076, CFSG.KD.Fi24Alpha.Pc.v1077, CFSG.KD.Fi24Alpha.Pc.v1078, CFSG.KD.Fi24Alpha.Pc.v1079, CFSG.KD.Fi24Alpha.Pc.v1080, CFSG.KD.Fi24Alpha.Pc.v1081, CFSG.KD.Fi24Alpha.Pc.v1082]
theorem CFSG.KD.Fi24Alpha.Pc.p1081 : Nat.beq (runC AR SD 1069 (ckL CFSG.KD.Fi24Alpha.Pc.l1083) 2 1081 CFSG.KD.Fi24Alpha.Pc.l1081) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1083 : Nat := CFSG.KD.Fi24Alpha.KV7 92
theorem CFSG.KD.Fi24Alpha.Pc.f75 : Nat.beq (runC AR SD 1069 (finC AR SD (nat_lit 75) 1069 1084) 1 1083 CFSG.KD.Fi24Alpha.Pc.l1083) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk75 : chk (nat_lit 75) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 75) (lo := 1069) (hi := 1084) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 1071) CFSG.KD.Fi24Alpha.Pc.p1069 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 1073) CFSG.KD.Fi24Alpha.Pc.p1071 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 1075) CFSG.KD.Fi24Alpha.Pc.p1073 rfl rfl).trans ((runC_seq (m := 9) (m2 := 8) (j2 := 1076) CFSG.KD.Fi24Alpha.Pc.p1075 rfl rfl).trans ((runC_seq (m := 8) (m2 := 7) (j2 := 1077) CFSG.KD.Fi24Alpha.Pc.p1076 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 1079) CFSG.KD.Fi24Alpha.Pc.p1077 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 1081) CFSG.KD.Fi24Alpha.Pc.p1079 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 1083) CFSG.KD.Fi24Alpha.Pc.p1081 rfl rfl)))))))))).trans CFSG.KD.Fi24Alpha.Pc.f75

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1084 : Nat := CFSG.KD.Fi24Alpha.KV7 93
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1085 : Nat := CFSG.KD.Fi24Alpha.KV7 94
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1086 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1084, CFSG.KD.Fi24Alpha.Pc.v1085]
theorem CFSG.KD.Fi24Alpha.Pc.p1084 : Nat.beq (runC AR SD 1084 (ckL CFSG.KD.Fi24Alpha.Pc.l1086) 2 1084 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1086 : Nat := CFSG.KD.Fi24Alpha.KV7 95
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1087 : Nat := CFSG.KD.Fi24Alpha.KV7 96
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1088 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1084, CFSG.KD.Fi24Alpha.Pc.v1085, CFSG.KD.Fi24Alpha.Pc.v1086, CFSG.KD.Fi24Alpha.Pc.v1087]
theorem CFSG.KD.Fi24Alpha.Pc.p1086 : Nat.beq (runC AR SD 1084 (ckL CFSG.KD.Fi24Alpha.Pc.l1088) 2 1086 CFSG.KD.Fi24Alpha.Pc.l1086) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1088 : Nat := CFSG.KD.Fi24Alpha.KV7 97
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1089 : Nat := CFSG.KD.Fi24Alpha.KV7 98
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1090 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1084, CFSG.KD.Fi24Alpha.Pc.v1085, CFSG.KD.Fi24Alpha.Pc.v1086, CFSG.KD.Fi24Alpha.Pc.v1087, CFSG.KD.Fi24Alpha.Pc.v1088, CFSG.KD.Fi24Alpha.Pc.v1089]
theorem CFSG.KD.Fi24Alpha.Pc.p1088 : Nat.beq (runC AR SD 1084 (ckL CFSG.KD.Fi24Alpha.Pc.l1090) 2 1088 CFSG.KD.Fi24Alpha.Pc.l1088) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1090 : Nat := CFSG.KD.Fi24Alpha.KV7 99
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1091 : Nat := CFSG.KD.Fi24Alpha.KV7 100
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1092 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1084, CFSG.KD.Fi24Alpha.Pc.v1085, CFSG.KD.Fi24Alpha.Pc.v1086, CFSG.KD.Fi24Alpha.Pc.v1087, CFSG.KD.Fi24Alpha.Pc.v1088, CFSG.KD.Fi24Alpha.Pc.v1089, CFSG.KD.Fi24Alpha.Pc.v1090, CFSG.KD.Fi24Alpha.Pc.v1091]
theorem CFSG.KD.Fi24Alpha.Pc.p1090 : Nat.beq (runC AR SD 1084 (ckL CFSG.KD.Fi24Alpha.Pc.l1092) 2 1090 CFSG.KD.Fi24Alpha.Pc.l1090) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1092 : Nat := CFSG.KD.Fi24Alpha.KV7 101
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1093 : Nat := CFSG.KD.Fi24Alpha.KV7 102
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1094 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1084, CFSG.KD.Fi24Alpha.Pc.v1085, CFSG.KD.Fi24Alpha.Pc.v1086, CFSG.KD.Fi24Alpha.Pc.v1087, CFSG.KD.Fi24Alpha.Pc.v1088, CFSG.KD.Fi24Alpha.Pc.v1089, CFSG.KD.Fi24Alpha.Pc.v1090, CFSG.KD.Fi24Alpha.Pc.v1091, CFSG.KD.Fi24Alpha.Pc.v1092, CFSG.KD.Fi24Alpha.Pc.v1093]
theorem CFSG.KD.Fi24Alpha.Pc.p1092 : Nat.beq (runC AR SD 1084 (ckL CFSG.KD.Fi24Alpha.Pc.l1094) 2 1092 CFSG.KD.Fi24Alpha.Pc.l1092) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1094 : Nat := CFSG.KD.Fi24Alpha.KV7 103
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1095 : Nat := CFSG.KD.Fi24Alpha.KV7 104
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1096 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1084, CFSG.KD.Fi24Alpha.Pc.v1085, CFSG.KD.Fi24Alpha.Pc.v1086, CFSG.KD.Fi24Alpha.Pc.v1087, CFSG.KD.Fi24Alpha.Pc.v1088, CFSG.KD.Fi24Alpha.Pc.v1089, CFSG.KD.Fi24Alpha.Pc.v1090, CFSG.KD.Fi24Alpha.Pc.v1091, CFSG.KD.Fi24Alpha.Pc.v1092, CFSG.KD.Fi24Alpha.Pc.v1093, CFSG.KD.Fi24Alpha.Pc.v1094, CFSG.KD.Fi24Alpha.Pc.v1095]
theorem CFSG.KD.Fi24Alpha.Pc.p1094 : Nat.beq (runC AR SD 1084 (ckL CFSG.KD.Fi24Alpha.Pc.l1096) 2 1094 CFSG.KD.Fi24Alpha.Pc.l1094) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1096 : Nat := CFSG.KD.Fi24Alpha.KV7 105
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1097 : Nat := CFSG.KD.Fi24Alpha.KV7 106
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1098 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1084, CFSG.KD.Fi24Alpha.Pc.v1085, CFSG.KD.Fi24Alpha.Pc.v1086, CFSG.KD.Fi24Alpha.Pc.v1087, CFSG.KD.Fi24Alpha.Pc.v1088, CFSG.KD.Fi24Alpha.Pc.v1089, CFSG.KD.Fi24Alpha.Pc.v1090, CFSG.KD.Fi24Alpha.Pc.v1091, CFSG.KD.Fi24Alpha.Pc.v1092, CFSG.KD.Fi24Alpha.Pc.v1093, CFSG.KD.Fi24Alpha.Pc.v1094, CFSG.KD.Fi24Alpha.Pc.v1095, CFSG.KD.Fi24Alpha.Pc.v1096, CFSG.KD.Fi24Alpha.Pc.v1097]
theorem CFSG.KD.Fi24Alpha.Pc.p1096 : Nat.beq (runC AR SD 1084 (ckL CFSG.KD.Fi24Alpha.Pc.l1098) 2 1096 CFSG.KD.Fi24Alpha.Pc.l1096) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1098 : Nat := CFSG.KD.Fi24Alpha.KV7 107
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1099 : Nat := CFSG.KD.Fi24Alpha.KV7 108
theorem CFSG.KD.Fi24Alpha.Pc.f76 : Nat.beq (runC AR SD 1084 (finC AR SD (nat_lit 76) 1084 1100) 2 1098 CFSG.KD.Fi24Alpha.Pc.l1098) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk76 : chk (nat_lit 76) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 76) (lo := 1084) (hi := 1100) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1086) CFSG.KD.Fi24Alpha.Pc.p1084 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1088) CFSG.KD.Fi24Alpha.Pc.p1086 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1090) CFSG.KD.Fi24Alpha.Pc.p1088 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1092) CFSG.KD.Fi24Alpha.Pc.p1090 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1094) CFSG.KD.Fi24Alpha.Pc.p1092 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1096) CFSG.KD.Fi24Alpha.Pc.p1094 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1098) CFSG.KD.Fi24Alpha.Pc.p1096 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f76

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1100 : Nat := CFSG.KD.Fi24Alpha.KV7 109
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1101 : Nat := CFSG.KD.Fi24Alpha.KV7 110
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1102 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1100, CFSG.KD.Fi24Alpha.Pc.v1101]
theorem CFSG.KD.Fi24Alpha.Pc.p1100 : Nat.beq (runC AR SD 1100 (ckL CFSG.KD.Fi24Alpha.Pc.l1102) 2 1100 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1102 : Nat := CFSG.KD.Fi24Alpha.KV7 111
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1103 : Nat := CFSG.KD.Fi24Alpha.KV7 112
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1104 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1100, CFSG.KD.Fi24Alpha.Pc.v1101, CFSG.KD.Fi24Alpha.Pc.v1102, CFSG.KD.Fi24Alpha.Pc.v1103]
theorem CFSG.KD.Fi24Alpha.Pc.p1102 : Nat.beq (runC AR SD 1100 (ckL CFSG.KD.Fi24Alpha.Pc.l1104) 2 1102 CFSG.KD.Fi24Alpha.Pc.l1102) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1104 : Nat := CFSG.KD.Fi24Alpha.KV7 113
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1105 : Nat := CFSG.KD.Fi24Alpha.KV7 114
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1106 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1100, CFSG.KD.Fi24Alpha.Pc.v1101, CFSG.KD.Fi24Alpha.Pc.v1102, CFSG.KD.Fi24Alpha.Pc.v1103, CFSG.KD.Fi24Alpha.Pc.v1104, CFSG.KD.Fi24Alpha.Pc.v1105]
theorem CFSG.KD.Fi24Alpha.Pc.p1104 : Nat.beq (runC AR SD 1100 (ckL CFSG.KD.Fi24Alpha.Pc.l1106) 2 1104 CFSG.KD.Fi24Alpha.Pc.l1104) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1106 : Nat := CFSG.KD.Fi24Alpha.KV7 115
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1107 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1100, CFSG.KD.Fi24Alpha.Pc.v1101, CFSG.KD.Fi24Alpha.Pc.v1102, CFSG.KD.Fi24Alpha.Pc.v1103, CFSG.KD.Fi24Alpha.Pc.v1104, CFSG.KD.Fi24Alpha.Pc.v1105, CFSG.KD.Fi24Alpha.Pc.v1106]
theorem CFSG.KD.Fi24Alpha.Pc.p1106 : Nat.beq (runC AR SD 1100 (ckL CFSG.KD.Fi24Alpha.Pc.l1107) 1 1106 CFSG.KD.Fi24Alpha.Pc.l1106) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1107 : Nat := CFSG.KD.Fi24Alpha.KV7 116
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1108 : Nat := CFSG.KD.Fi24Alpha.KV7 117
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1109 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1100, CFSG.KD.Fi24Alpha.Pc.v1101, CFSG.KD.Fi24Alpha.Pc.v1102, CFSG.KD.Fi24Alpha.Pc.v1103, CFSG.KD.Fi24Alpha.Pc.v1104, CFSG.KD.Fi24Alpha.Pc.v1105, CFSG.KD.Fi24Alpha.Pc.v1106, CFSG.KD.Fi24Alpha.Pc.v1107, CFSG.KD.Fi24Alpha.Pc.v1108]
theorem CFSG.KD.Fi24Alpha.Pc.p1107 : Nat.beq (runC AR SD 1100 (ckL CFSG.KD.Fi24Alpha.Pc.l1109) 2 1107 CFSG.KD.Fi24Alpha.Pc.l1107) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1109 : Nat := CFSG.KD.Fi24Alpha.KV7 118
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1110 : Nat := CFSG.KD.Fi24Alpha.KV7 119
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1111 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1100, CFSG.KD.Fi24Alpha.Pc.v1101, CFSG.KD.Fi24Alpha.Pc.v1102, CFSG.KD.Fi24Alpha.Pc.v1103, CFSG.KD.Fi24Alpha.Pc.v1104, CFSG.KD.Fi24Alpha.Pc.v1105, CFSG.KD.Fi24Alpha.Pc.v1106, CFSG.KD.Fi24Alpha.Pc.v1107, CFSG.KD.Fi24Alpha.Pc.v1108, CFSG.KD.Fi24Alpha.Pc.v1109, CFSG.KD.Fi24Alpha.Pc.v1110]
theorem CFSG.KD.Fi24Alpha.Pc.p1109 : Nat.beq (runC AR SD 1100 (ckL CFSG.KD.Fi24Alpha.Pc.l1111) 2 1109 CFSG.KD.Fi24Alpha.Pc.l1109) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1111 : Nat := CFSG.KD.Fi24Alpha.KV7 120
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1112 : Nat := CFSG.KD.Fi24Alpha.KV7 121
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1113 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1100, CFSG.KD.Fi24Alpha.Pc.v1101, CFSG.KD.Fi24Alpha.Pc.v1102, CFSG.KD.Fi24Alpha.Pc.v1103, CFSG.KD.Fi24Alpha.Pc.v1104, CFSG.KD.Fi24Alpha.Pc.v1105, CFSG.KD.Fi24Alpha.Pc.v1106, CFSG.KD.Fi24Alpha.Pc.v1107, CFSG.KD.Fi24Alpha.Pc.v1108, CFSG.KD.Fi24Alpha.Pc.v1109, CFSG.KD.Fi24Alpha.Pc.v1110, CFSG.KD.Fi24Alpha.Pc.v1111, CFSG.KD.Fi24Alpha.Pc.v1112]
theorem CFSG.KD.Fi24Alpha.Pc.p1111 : Nat.beq (runC AR SD 1100 (ckL CFSG.KD.Fi24Alpha.Pc.l1113) 2 1111 CFSG.KD.Fi24Alpha.Pc.l1111) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1113 : Nat := CFSG.KD.Fi24Alpha.KV7 122
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1114 : Nat := CFSG.KD.Fi24Alpha.KV7 123
theorem CFSG.KD.Fi24Alpha.Pc.f77 : Nat.beq (runC AR SD 1100 (finC AR SD (nat_lit 77) 1100 1115) 2 1113 CFSG.KD.Fi24Alpha.Pc.l1113) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk77 : chk (nat_lit 77) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 77) (lo := 1100) (hi := 1115) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 1102) CFSG.KD.Fi24Alpha.Pc.p1100 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 1104) CFSG.KD.Fi24Alpha.Pc.p1102 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 1106) CFSG.KD.Fi24Alpha.Pc.p1104 rfl rfl).trans ((runC_seq (m := 9) (m2 := 8) (j2 := 1107) CFSG.KD.Fi24Alpha.Pc.p1106 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1109) CFSG.KD.Fi24Alpha.Pc.p1107 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1111) CFSG.KD.Fi24Alpha.Pc.p1109 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1113) CFSG.KD.Fi24Alpha.Pc.p1111 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f77

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1115 : Nat := CFSG.KD.Fi24Alpha.KV7 124
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1116 : Nat := CFSG.KD.Fi24Alpha.KV7 125
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1117 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1115, CFSG.KD.Fi24Alpha.Pc.v1116]
theorem CFSG.KD.Fi24Alpha.Pc.p1115 : Nat.beq (runC AR SD 1115 (ckL CFSG.KD.Fi24Alpha.Pc.l1117) 2 1115 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1117 : Nat := CFSG.KD.Fi24Alpha.KV7 126
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1118 : Nat := CFSG.KD.Fi24Alpha.KV7 127
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1119 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1115, CFSG.KD.Fi24Alpha.Pc.v1116, CFSG.KD.Fi24Alpha.Pc.v1117, CFSG.KD.Fi24Alpha.Pc.v1118]
theorem CFSG.KD.Fi24Alpha.Pc.p1117 : Nat.beq (runC AR SD 1115 (ckL CFSG.KD.Fi24Alpha.Pc.l1119) 2 1117 CFSG.KD.Fi24Alpha.Pc.l1117) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1119 : Nat := CFSG.KD.Fi24Alpha.KV7 128
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1120 : Nat := CFSG.KD.Fi24Alpha.KV7 129
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1121 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1115, CFSG.KD.Fi24Alpha.Pc.v1116, CFSG.KD.Fi24Alpha.Pc.v1117, CFSG.KD.Fi24Alpha.Pc.v1118, CFSG.KD.Fi24Alpha.Pc.v1119, CFSG.KD.Fi24Alpha.Pc.v1120]
theorem CFSG.KD.Fi24Alpha.Pc.p1119 : Nat.beq (runC AR SD 1115 (ckL CFSG.KD.Fi24Alpha.Pc.l1121) 2 1119 CFSG.KD.Fi24Alpha.Pc.l1119) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1121 : Nat := CFSG.KD.Fi24Alpha.KV7 130
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1122 : Nat := CFSG.KD.Fi24Alpha.KV7 131
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1123 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1115, CFSG.KD.Fi24Alpha.Pc.v1116, CFSG.KD.Fi24Alpha.Pc.v1117, CFSG.KD.Fi24Alpha.Pc.v1118, CFSG.KD.Fi24Alpha.Pc.v1119, CFSG.KD.Fi24Alpha.Pc.v1120, CFSG.KD.Fi24Alpha.Pc.v1121, CFSG.KD.Fi24Alpha.Pc.v1122]
theorem CFSG.KD.Fi24Alpha.Pc.p1121 : Nat.beq (runC AR SD 1115 (ckL CFSG.KD.Fi24Alpha.Pc.l1123) 2 1121 CFSG.KD.Fi24Alpha.Pc.l1121) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1123 : Nat := CFSG.KD.Fi24Alpha.KV7 132
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1124 : Nat := CFSG.KD.Fi24Alpha.KV7 133
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1125 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1115, CFSG.KD.Fi24Alpha.Pc.v1116, CFSG.KD.Fi24Alpha.Pc.v1117, CFSG.KD.Fi24Alpha.Pc.v1118, CFSG.KD.Fi24Alpha.Pc.v1119, CFSG.KD.Fi24Alpha.Pc.v1120, CFSG.KD.Fi24Alpha.Pc.v1121, CFSG.KD.Fi24Alpha.Pc.v1122, CFSG.KD.Fi24Alpha.Pc.v1123, CFSG.KD.Fi24Alpha.Pc.v1124]
theorem CFSG.KD.Fi24Alpha.Pc.p1123 : Nat.beq (runC AR SD 1115 (ckL CFSG.KD.Fi24Alpha.Pc.l1125) 2 1123 CFSG.KD.Fi24Alpha.Pc.l1123) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1125 : Nat := CFSG.KD.Fi24Alpha.KV7 134
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1126 : Nat := CFSG.KD.Fi24Alpha.KV7 135
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1127 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1115, CFSG.KD.Fi24Alpha.Pc.v1116, CFSG.KD.Fi24Alpha.Pc.v1117, CFSG.KD.Fi24Alpha.Pc.v1118, CFSG.KD.Fi24Alpha.Pc.v1119, CFSG.KD.Fi24Alpha.Pc.v1120, CFSG.KD.Fi24Alpha.Pc.v1121, CFSG.KD.Fi24Alpha.Pc.v1122, CFSG.KD.Fi24Alpha.Pc.v1123, CFSG.KD.Fi24Alpha.Pc.v1124, CFSG.KD.Fi24Alpha.Pc.v1125, CFSG.KD.Fi24Alpha.Pc.v1126]
theorem CFSG.KD.Fi24Alpha.Pc.p1125 : Nat.beq (runC AR SD 1115 (ckL CFSG.KD.Fi24Alpha.Pc.l1127) 2 1125 CFSG.KD.Fi24Alpha.Pc.l1125) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1127 : Nat := CFSG.KD.Fi24Alpha.KV7 136
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1128 : Nat := CFSG.KD.Fi24Alpha.KV7 137
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1129 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1115, CFSG.KD.Fi24Alpha.Pc.v1116, CFSG.KD.Fi24Alpha.Pc.v1117, CFSG.KD.Fi24Alpha.Pc.v1118, CFSG.KD.Fi24Alpha.Pc.v1119, CFSG.KD.Fi24Alpha.Pc.v1120, CFSG.KD.Fi24Alpha.Pc.v1121, CFSG.KD.Fi24Alpha.Pc.v1122, CFSG.KD.Fi24Alpha.Pc.v1123, CFSG.KD.Fi24Alpha.Pc.v1124, CFSG.KD.Fi24Alpha.Pc.v1125, CFSG.KD.Fi24Alpha.Pc.v1126, CFSG.KD.Fi24Alpha.Pc.v1127, CFSG.KD.Fi24Alpha.Pc.v1128]
theorem CFSG.KD.Fi24Alpha.Pc.p1127 : Nat.beq (runC AR SD 1115 (ckL CFSG.KD.Fi24Alpha.Pc.l1129) 2 1127 CFSG.KD.Fi24Alpha.Pc.l1127) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1129 : Nat := CFSG.KD.Fi24Alpha.KV7 138
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1130 : Nat := CFSG.KD.Fi24Alpha.KV7 139
theorem CFSG.KD.Fi24Alpha.Pc.f78 : Nat.beq (runC AR SD 1115 (finC AR SD (nat_lit 78) 1115 1131) 2 1129 CFSG.KD.Fi24Alpha.Pc.l1129) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk78 : chk (nat_lit 78) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 78) (lo := 1115) (hi := 1131) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 1117) CFSG.KD.Fi24Alpha.Pc.p1115 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 1119) CFSG.KD.Fi24Alpha.Pc.p1117 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1121) CFSG.KD.Fi24Alpha.Pc.p1119 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1123) CFSG.KD.Fi24Alpha.Pc.p1121 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1125) CFSG.KD.Fi24Alpha.Pc.p1123 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1127) CFSG.KD.Fi24Alpha.Pc.p1125 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1129) CFSG.KD.Fi24Alpha.Pc.p1127 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f78

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1131 : Nat := CFSG.KD.Fi24Alpha.KV7 140
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1132 : Nat := CFSG.KD.Fi24Alpha.KV7 141
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1133 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1131, CFSG.KD.Fi24Alpha.Pc.v1132]
theorem CFSG.KD.Fi24Alpha.Pc.p1131 : Nat.beq (runC AR SD 1131 (ckL CFSG.KD.Fi24Alpha.Pc.l1133) 2 1131 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1133 : Nat := CFSG.KD.Fi24Alpha.KV7 142
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1134 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1131, CFSG.KD.Fi24Alpha.Pc.v1132, CFSG.KD.Fi24Alpha.Pc.v1133]
theorem CFSG.KD.Fi24Alpha.Pc.p1133 : Nat.beq (runC AR SD 1131 (ckL CFSG.KD.Fi24Alpha.Pc.l1134) 1 1133 CFSG.KD.Fi24Alpha.Pc.l1133) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1134 : Nat := CFSG.KD.Fi24Alpha.KV7 143
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1135 : Nat := CFSG.KD.Fi24Alpha.KV7 144
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1136 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1131, CFSG.KD.Fi24Alpha.Pc.v1132, CFSG.KD.Fi24Alpha.Pc.v1133, CFSG.KD.Fi24Alpha.Pc.v1134, CFSG.KD.Fi24Alpha.Pc.v1135]
theorem CFSG.KD.Fi24Alpha.Pc.p1134 : Nat.beq (runC AR SD 1131 (ckL CFSG.KD.Fi24Alpha.Pc.l1136) 2 1134 CFSG.KD.Fi24Alpha.Pc.l1134) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1136 : Nat := CFSG.KD.Fi24Alpha.KV7 145
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1137 : Nat := CFSG.KD.Fi24Alpha.KV7 146
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1138 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1131, CFSG.KD.Fi24Alpha.Pc.v1132, CFSG.KD.Fi24Alpha.Pc.v1133, CFSG.KD.Fi24Alpha.Pc.v1134, CFSG.KD.Fi24Alpha.Pc.v1135, CFSG.KD.Fi24Alpha.Pc.v1136, CFSG.KD.Fi24Alpha.Pc.v1137]
theorem CFSG.KD.Fi24Alpha.Pc.p1136 : Nat.beq (runC AR SD 1131 (ckL CFSG.KD.Fi24Alpha.Pc.l1138) 2 1136 CFSG.KD.Fi24Alpha.Pc.l1136) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1138 : Nat := CFSG.KD.Fi24Alpha.KV7 147
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1139 : Nat := CFSG.KD.Fi24Alpha.KV7 148
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1140 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1131, CFSG.KD.Fi24Alpha.Pc.v1132, CFSG.KD.Fi24Alpha.Pc.v1133, CFSG.KD.Fi24Alpha.Pc.v1134, CFSG.KD.Fi24Alpha.Pc.v1135, CFSG.KD.Fi24Alpha.Pc.v1136, CFSG.KD.Fi24Alpha.Pc.v1137, CFSG.KD.Fi24Alpha.Pc.v1138, CFSG.KD.Fi24Alpha.Pc.v1139]
theorem CFSG.KD.Fi24Alpha.Pc.p1138 : Nat.beq (runC AR SD 1131 (ckL CFSG.KD.Fi24Alpha.Pc.l1140) 2 1138 CFSG.KD.Fi24Alpha.Pc.l1138) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1140 : Nat := CFSG.KD.Fi24Alpha.KV7 149
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1141 : Nat := CFSG.KD.Fi24Alpha.KV7 150
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1142 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1131, CFSG.KD.Fi24Alpha.Pc.v1132, CFSG.KD.Fi24Alpha.Pc.v1133, CFSG.KD.Fi24Alpha.Pc.v1134, CFSG.KD.Fi24Alpha.Pc.v1135, CFSG.KD.Fi24Alpha.Pc.v1136, CFSG.KD.Fi24Alpha.Pc.v1137, CFSG.KD.Fi24Alpha.Pc.v1138, CFSG.KD.Fi24Alpha.Pc.v1139, CFSG.KD.Fi24Alpha.Pc.v1140, CFSG.KD.Fi24Alpha.Pc.v1141]
theorem CFSG.KD.Fi24Alpha.Pc.p1140 : Nat.beq (runC AR SD 1131 (ckL CFSG.KD.Fi24Alpha.Pc.l1142) 2 1140 CFSG.KD.Fi24Alpha.Pc.l1140) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1142 : Nat := CFSG.KD.Fi24Alpha.KV7 151
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1143 : Nat := CFSG.KD.Fi24Alpha.KV7 152
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l1144 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v1131, CFSG.KD.Fi24Alpha.Pc.v1132, CFSG.KD.Fi24Alpha.Pc.v1133, CFSG.KD.Fi24Alpha.Pc.v1134, CFSG.KD.Fi24Alpha.Pc.v1135, CFSG.KD.Fi24Alpha.Pc.v1136, CFSG.KD.Fi24Alpha.Pc.v1137, CFSG.KD.Fi24Alpha.Pc.v1138, CFSG.KD.Fi24Alpha.Pc.v1139, CFSG.KD.Fi24Alpha.Pc.v1140, CFSG.KD.Fi24Alpha.Pc.v1141, CFSG.KD.Fi24Alpha.Pc.v1142, CFSG.KD.Fi24Alpha.Pc.v1143]
theorem CFSG.KD.Fi24Alpha.Pc.p1142 : Nat.beq (runC AR SD 1131 (ckL CFSG.KD.Fi24Alpha.Pc.l1144) 2 1142 CFSG.KD.Fi24Alpha.Pc.l1142) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1144 : Nat := CFSG.KD.Fi24Alpha.KV7 153
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v1145 : Nat := CFSG.KD.Fi24Alpha.KV7 154
theorem CFSG.KD.Fi24Alpha.Pc.f79 : Nat.beq (runC AR SD 1131 (finC AR SD (nat_lit 79) 1131 1146) 2 1144 CFSG.KD.Fi24Alpha.Pc.l1144) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk79 : chk (nat_lit 79) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 79) (lo := 1131) (hi := 1146) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 1133) CFSG.KD.Fi24Alpha.Pc.p1131 rfl rfl).trans ((runC_seq (m := 13) (m2 := 12) (j2 := 1134) CFSG.KD.Fi24Alpha.Pc.p1133 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 1136) CFSG.KD.Fi24Alpha.Pc.p1134 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 1138) CFSG.KD.Fi24Alpha.Pc.p1136 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 1140) CFSG.KD.Fi24Alpha.Pc.p1138 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1142) CFSG.KD.Fi24Alpha.Pc.p1140 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1144) CFSG.KD.Fi24Alpha.Pc.p1142 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f79

end
