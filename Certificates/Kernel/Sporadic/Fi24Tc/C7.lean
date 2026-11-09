module

public import Certificates.Kernel.Sporadic.Fi24Tc.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Tc KV7 "Certificates/Kernel/Sporadic/Fi24Tc/data/v7.bin" 152491 4 17383974 3371730067597547507

public section

open CFSG.KD.Fi24Tc CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v952 : Nat := CFSG.KD.Fi24Tc.KV7 0
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v953 : Nat := CFSG.KD.Fi24Tc.KV7 1
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l954 : List Nat := [CFSG.KD.Fi24Tc.Pc.v952, CFSG.KD.Fi24Tc.Pc.v953]
theorem CFSG.KD.Fi24Tc.Pc.p952 : Nat.beq (runC AR SD 952 (ckL CFSG.KD.Fi24Tc.Pc.l954) 2 952 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v954 : Nat := CFSG.KD.Fi24Tc.KV7 2
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v955 : Nat := CFSG.KD.Fi24Tc.KV7 3
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l956 : List Nat := [CFSG.KD.Fi24Tc.Pc.v952, CFSG.KD.Fi24Tc.Pc.v953, CFSG.KD.Fi24Tc.Pc.v954, CFSG.KD.Fi24Tc.Pc.v955]
theorem CFSG.KD.Fi24Tc.Pc.p954 : Nat.beq (runC AR SD 952 (ckL CFSG.KD.Fi24Tc.Pc.l956) 2 954 CFSG.KD.Fi24Tc.Pc.l954) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v956 : Nat := CFSG.KD.Fi24Tc.KV7 4
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v957 : Nat := CFSG.KD.Fi24Tc.KV7 5
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l958 : List Nat := [CFSG.KD.Fi24Tc.Pc.v952, CFSG.KD.Fi24Tc.Pc.v953, CFSG.KD.Fi24Tc.Pc.v954, CFSG.KD.Fi24Tc.Pc.v955, CFSG.KD.Fi24Tc.Pc.v956, CFSG.KD.Fi24Tc.Pc.v957]
theorem CFSG.KD.Fi24Tc.Pc.p956 : Nat.beq (runC AR SD 952 (ckL CFSG.KD.Fi24Tc.Pc.l958) 2 956 CFSG.KD.Fi24Tc.Pc.l956) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f140 : Nat.beq (runC AR SD 952 (finC AR SD (nat_lit 140) 952 960) 2 958 CFSG.KD.Fi24Tc.Pc.l958) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk140 : chk (nat_lit 140) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 140) (lo := 952) (hi := 960) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 954) CFSG.KD.Fi24Tc.Pc.p952 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 956) CFSG.KD.Fi24Tc.Pc.p954 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 958) CFSG.KD.Fi24Tc.Pc.p956 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f140

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v960 : Nat := CFSG.KD.Fi24Tc.KV7 6
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v961 : Nat := CFSG.KD.Fi24Tc.KV7 7
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l962 : List Nat := [CFSG.KD.Fi24Tc.Pc.v960, CFSG.KD.Fi24Tc.Pc.v961]
theorem CFSG.KD.Fi24Tc.Pc.p960 : Nat.beq (runC AR SD 960 (ckL CFSG.KD.Fi24Tc.Pc.l962) 2 960 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v962 : Nat := CFSG.KD.Fi24Tc.KV7 8
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l963 : List Nat := [CFSG.KD.Fi24Tc.Pc.v960, CFSG.KD.Fi24Tc.Pc.v961, CFSG.KD.Fi24Tc.Pc.v962]
theorem CFSG.KD.Fi24Tc.Pc.p962 : Nat.beq (runC AR SD 960 (ckL CFSG.KD.Fi24Tc.Pc.l963) 1 962 CFSG.KD.Fi24Tc.Pc.l962) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a963_2 : Nat := CFSG.KD.Fi24Tc.KV7 9
theorem CFSG.KD.Fi24Tc.Pc.q963_2 : Nat.beq (powTop AR.mul (getV AR SD 960 CFSG.KD.Fi24Tc.Pc.l963 (SD.na.getD 963 0)) (SD.nk.getD 963 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a963_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a963_1 : Nat := CFSG.KD.Fi24Tc.KV7 10
theorem CFSG.KD.Fi24Tc.Pc.q963_1 : Nat.beq (powTop AR.mul (getV AR SD 960 CFSG.KD.Fi24Tc.Pc.l963 (SD.na.getD 963 0)) (SD.nk.getD 963 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a963_1) 1 CFSG.KD.Fi24Tc.Pc.a963_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v963 : Nat := CFSG.KD.Fi24Tc.KV7 11
theorem CFSG.KD.Fi24Tc.Pc.r963 : Nat.beq (powR AR.mul AR.one (getV AR SD 960 CFSG.KD.Fi24Tc.Pc.l963 (SD.na.getD 963 0)) (SD.nk.getD 963 1) 1 CFSG.KD.Fi24Tc.Pc.a963_1 true) CFSG.KD.Fi24Tc.Pc.v963 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l964 : List Nat := [CFSG.KD.Fi24Tc.Pc.v960, CFSG.KD.Fi24Tc.Pc.v961, CFSG.KD.Fi24Tc.Pc.v962, CFSG.KD.Fi24Tc.Pc.v963]
theorem CFSG.KD.Fi24Tc.Pc.f141 : Nat.beq (runC AR SD 960 (finC AR SD (nat_lit 141) 960 964) 0 964 CFSG.KD.Fi24Tc.Pc.l964) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk141 : chk (nat_lit 141) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 141) (lo := 960) (hi := 964) (m := 4) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 4) (m2 := 2) (j2 := 962) CFSG.KD.Fi24Tc.Pc.p960 rfl rfl).trans ((runC_seq (m := 2) (m2 := 1) (j2 := 963) CFSG.KD.Fi24Tc.Pc.p962 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 964) (Lr := CFSG.KD.Fi24Tc.Pc.l964) ((nodeV_pow (R := AR) (D := SD) (lo := 960) (L := CFSG.KD.Fi24Tc.Pc.l963) (j := 963) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 960 CFSG.KD.Fi24Tc.Pc.l963 (SD.na.getD 963 0)) (SD.nk.getD 963 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q963_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q963_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r963))))) (by quickRfl) rfl rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f141

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v964 : Nat := CFSG.KD.Fi24Tc.KV7 12
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v965 : Nat := CFSG.KD.Fi24Tc.KV7 13
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l966 : List Nat := [CFSG.KD.Fi24Tc.Pc.v964, CFSG.KD.Fi24Tc.Pc.v965]
theorem CFSG.KD.Fi24Tc.Pc.p964 : Nat.beq (runC AR SD 964 (ckL CFSG.KD.Fi24Tc.Pc.l966) 2 964 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v966 : Nat := CFSG.KD.Fi24Tc.KV7 14
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v967 : Nat := CFSG.KD.Fi24Tc.KV7 15
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l968 : List Nat := [CFSG.KD.Fi24Tc.Pc.v964, CFSG.KD.Fi24Tc.Pc.v965, CFSG.KD.Fi24Tc.Pc.v966, CFSG.KD.Fi24Tc.Pc.v967]
theorem CFSG.KD.Fi24Tc.Pc.p966 : Nat.beq (runC AR SD 964 (ckL CFSG.KD.Fi24Tc.Pc.l968) 2 966 CFSG.KD.Fi24Tc.Pc.l966) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v968 : Nat := CFSG.KD.Fi24Tc.KV7 16
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v969 : Nat := CFSG.KD.Fi24Tc.KV7 17
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l970 : List Nat := [CFSG.KD.Fi24Tc.Pc.v964, CFSG.KD.Fi24Tc.Pc.v965, CFSG.KD.Fi24Tc.Pc.v966, CFSG.KD.Fi24Tc.Pc.v967, CFSG.KD.Fi24Tc.Pc.v968, CFSG.KD.Fi24Tc.Pc.v969]
theorem CFSG.KD.Fi24Tc.Pc.p968 : Nat.beq (runC AR SD 964 (ckL CFSG.KD.Fi24Tc.Pc.l970) 2 968 CFSG.KD.Fi24Tc.Pc.l968) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f142 : Nat.beq (runC AR SD 964 (finC AR SD (nat_lit 142) 964 972) 2 970 CFSG.KD.Fi24Tc.Pc.l970) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk142 : chk (nat_lit 142) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 142) (lo := 964) (hi := 972) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 966) CFSG.KD.Fi24Tc.Pc.p964 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 968) CFSG.KD.Fi24Tc.Pc.p966 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 970) CFSG.KD.Fi24Tc.Pc.p968 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f142

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v972 : Nat := CFSG.KD.Fi24Tc.KV7 18
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v973 : Nat := CFSG.KD.Fi24Tc.KV7 19
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l974 : List Nat := [CFSG.KD.Fi24Tc.Pc.v972, CFSG.KD.Fi24Tc.Pc.v973]
theorem CFSG.KD.Fi24Tc.Pc.p972 : Nat.beq (runC AR SD 972 (ckL CFSG.KD.Fi24Tc.Pc.l974) 2 972 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v974 : Nat := CFSG.KD.Fi24Tc.KV7 20
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v975 : Nat := CFSG.KD.Fi24Tc.KV7 21
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l976 : List Nat := [CFSG.KD.Fi24Tc.Pc.v972, CFSG.KD.Fi24Tc.Pc.v973, CFSG.KD.Fi24Tc.Pc.v974, CFSG.KD.Fi24Tc.Pc.v975]
theorem CFSG.KD.Fi24Tc.Pc.p974 : Nat.beq (runC AR SD 972 (ckL CFSG.KD.Fi24Tc.Pc.l976) 2 974 CFSG.KD.Fi24Tc.Pc.l974) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v976 : Nat := CFSG.KD.Fi24Tc.KV7 22
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v977 : Nat := CFSG.KD.Fi24Tc.KV7 23
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l978 : List Nat := [CFSG.KD.Fi24Tc.Pc.v972, CFSG.KD.Fi24Tc.Pc.v973, CFSG.KD.Fi24Tc.Pc.v974, CFSG.KD.Fi24Tc.Pc.v975, CFSG.KD.Fi24Tc.Pc.v976, CFSG.KD.Fi24Tc.Pc.v977]
theorem CFSG.KD.Fi24Tc.Pc.p976 : Nat.beq (runC AR SD 972 (ckL CFSG.KD.Fi24Tc.Pc.l978) 2 976 CFSG.KD.Fi24Tc.Pc.l976) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f143 : Nat.beq (runC AR SD 972 (finC AR SD (nat_lit 143) 972 980) 2 978 CFSG.KD.Fi24Tc.Pc.l978) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk143 : chk (nat_lit 143) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 143) (lo := 972) (hi := 980) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 974) CFSG.KD.Fi24Tc.Pc.p972 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 976) CFSG.KD.Fi24Tc.Pc.p974 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 978) CFSG.KD.Fi24Tc.Pc.p976 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f143

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v980 : Nat := CFSG.KD.Fi24Tc.KV7 24
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v981 : Nat := CFSG.KD.Fi24Tc.KV7 25
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l982 : List Nat := [CFSG.KD.Fi24Tc.Pc.v980, CFSG.KD.Fi24Tc.Pc.v981]
theorem CFSG.KD.Fi24Tc.Pc.p980 : Nat.beq (runC AR SD 980 (ckL CFSG.KD.Fi24Tc.Pc.l982) 2 980 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v982 : Nat := CFSG.KD.Fi24Tc.KV7 26
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v983 : Nat := CFSG.KD.Fi24Tc.KV7 27
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l984 : List Nat := [CFSG.KD.Fi24Tc.Pc.v980, CFSG.KD.Fi24Tc.Pc.v981, CFSG.KD.Fi24Tc.Pc.v982, CFSG.KD.Fi24Tc.Pc.v983]
theorem CFSG.KD.Fi24Tc.Pc.p982 : Nat.beq (runC AR SD 980 (ckL CFSG.KD.Fi24Tc.Pc.l984) 2 982 CFSG.KD.Fi24Tc.Pc.l982) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v984 : Nat := CFSG.KD.Fi24Tc.KV7 28
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v985 : Nat := CFSG.KD.Fi24Tc.KV7 29
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l986 : List Nat := [CFSG.KD.Fi24Tc.Pc.v980, CFSG.KD.Fi24Tc.Pc.v981, CFSG.KD.Fi24Tc.Pc.v982, CFSG.KD.Fi24Tc.Pc.v983, CFSG.KD.Fi24Tc.Pc.v984, CFSG.KD.Fi24Tc.Pc.v985]
theorem CFSG.KD.Fi24Tc.Pc.p984 : Nat.beq (runC AR SD 980 (ckL CFSG.KD.Fi24Tc.Pc.l986) 2 984 CFSG.KD.Fi24Tc.Pc.l984) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f144 : Nat.beq (runC AR SD 980 (finC AR SD (nat_lit 144) 980 988) 2 986 CFSG.KD.Fi24Tc.Pc.l986) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk144 : chk (nat_lit 144) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 144) (lo := 980) (hi := 988) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 982) CFSG.KD.Fi24Tc.Pc.p980 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 984) CFSG.KD.Fi24Tc.Pc.p982 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 986) CFSG.KD.Fi24Tc.Pc.p984 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f144

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v988 : Nat := CFSG.KD.Fi24Tc.KV7 112
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v989 : Nat := CFSG.KD.Fi24Tc.KV7 113
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l990 : List Nat := [CFSG.KD.Fi24Tc.Pc.v988, CFSG.KD.Fi24Tc.Pc.v989]
theorem CFSG.KD.Fi24Tc.Pc.p988 : Nat.beq (runC AR SD 988 (ckL CFSG.KD.Fi24Tc.Pc.l990) 2 988 []) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f145 : Nat.beq (runC AR SD 988 (finC AR SD (nat_lit 145) 988 992) 2 990 CFSG.KD.Fi24Tc.Pc.l990) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk145 : chk (nat_lit 145) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 145) (lo := 988) (hi := 992) (m := 4) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_seq (m := 4) (m2 := 2) (j2 := 990) CFSG.KD.Fi24Tc.Pc.p988 rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f145

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a992_2 : Nat := CFSG.KD.Fi24Tc.KV7 30
theorem CFSG.KD.Fi24Tc.Pc.q992_2 : Nat.beq (powTop AR.mul (getV AR SD 992 [] (SD.na.getD 992 0)) (SD.nk.getD 992 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a992_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a992_1 : Nat := CFSG.KD.Fi24Tc.KV7 31
theorem CFSG.KD.Fi24Tc.Pc.q992_1 : Nat.beq (powTop AR.mul (getV AR SD 992 [] (SD.na.getD 992 0)) (SD.nk.getD 992 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a992_1) 1 CFSG.KD.Fi24Tc.Pc.a992_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v992 : Nat := CFSG.KD.Fi24Tc.KV7 32
theorem CFSG.KD.Fi24Tc.Pc.r992 : Nat.beq (powR AR.mul AR.one (getV AR SD 992 [] (SD.na.getD 992 0)) (SD.nk.getD 992 1) 1 CFSG.KD.Fi24Tc.Pc.a992_1 true) CFSG.KD.Fi24Tc.Pc.v992 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l993 : List Nat := [CFSG.KD.Fi24Tc.Pc.v992]
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v993 : Nat := CFSG.KD.Fi24Tc.KV7 33
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v994 : Nat := CFSG.KD.Fi24Tc.KV7 34
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l995 : List Nat := [CFSG.KD.Fi24Tc.Pc.v992, CFSG.KD.Fi24Tc.Pc.v993, CFSG.KD.Fi24Tc.Pc.v994]
theorem CFSG.KD.Fi24Tc.Pc.p993 : Nat.beq (runC AR SD 992 (ckL CFSG.KD.Fi24Tc.Pc.l995) 2 993 CFSG.KD.Fi24Tc.Pc.l993) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f146 : Nat.beq (runC AR SD 992 (finC AR SD (nat_lit 146) 992 996) 1 995 CFSG.KD.Fi24Tc.Pc.l995) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk146 : chk (nat_lit 146) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 146) (lo := 992) (hi := 996) (m := 4) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 4) (m2 := 3) (j2 := 993) (Lr := CFSG.KD.Fi24Tc.Pc.l993) ((nodeV_pow (R := AR) (D := SD) (lo := 992) (L := []) (j := 992) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 992 [] (SD.na.getD 992 0)) (SD.nk.getD 992 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q992_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q992_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r992))))) (by quickRfl) rfl rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 995) CFSG.KD.Fi24Tc.Pc.p993 rfl rfl)))).trans CFSG.KD.Fi24Tc.Pc.f146

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v996 : Nat := CFSG.KD.Fi24Tc.KV7 35
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v997 : Nat := CFSG.KD.Fi24Tc.KV7 36
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l998 : List Nat := [CFSG.KD.Fi24Tc.Pc.v996, CFSG.KD.Fi24Tc.Pc.v997]
theorem CFSG.KD.Fi24Tc.Pc.p996 : Nat.beq (runC AR SD 996 (ckL CFSG.KD.Fi24Tc.Pc.l998) 2 996 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v998 : Nat := CFSG.KD.Fi24Tc.KV7 37
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v999 : Nat := CFSG.KD.Fi24Tc.KV7 38
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1000 : List Nat := [CFSG.KD.Fi24Tc.Pc.v996, CFSG.KD.Fi24Tc.Pc.v997, CFSG.KD.Fi24Tc.Pc.v998, CFSG.KD.Fi24Tc.Pc.v999]
theorem CFSG.KD.Fi24Tc.Pc.p998 : Nat.beq (runC AR SD 996 (ckL CFSG.KD.Fi24Tc.Pc.l1000) 2 998 CFSG.KD.Fi24Tc.Pc.l998) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1000 : Nat := CFSG.KD.Fi24Tc.KV7 39
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1001 : Nat := CFSG.KD.Fi24Tc.KV7 40
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1002 : List Nat := [CFSG.KD.Fi24Tc.Pc.v996, CFSG.KD.Fi24Tc.Pc.v997, CFSG.KD.Fi24Tc.Pc.v998, CFSG.KD.Fi24Tc.Pc.v999, CFSG.KD.Fi24Tc.Pc.v1000, CFSG.KD.Fi24Tc.Pc.v1001]
theorem CFSG.KD.Fi24Tc.Pc.p1000 : Nat.beq (runC AR SD 996 (ckL CFSG.KD.Fi24Tc.Pc.l1002) 2 1000 CFSG.KD.Fi24Tc.Pc.l1000) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f147 : Nat.beq (runC AR SD 996 (finC AR SD (nat_lit 147) 996 1004) 2 1002 CFSG.KD.Fi24Tc.Pc.l1002) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk147 : chk (nat_lit 147) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 147) (lo := 996) (hi := 1004) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 998) CFSG.KD.Fi24Tc.Pc.p996 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1000) CFSG.KD.Fi24Tc.Pc.p998 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1002) CFSG.KD.Fi24Tc.Pc.p1000 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f147

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1004 : Nat := CFSG.KD.Fi24Tc.KV7 41
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1005 : Nat := CFSG.KD.Fi24Tc.KV7 42
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1006 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1004, CFSG.KD.Fi24Tc.Pc.v1005]
theorem CFSG.KD.Fi24Tc.Pc.p1004 : Nat.beq (runC AR SD 1004 (ckL CFSG.KD.Fi24Tc.Pc.l1006) 2 1004 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1006 : Nat := CFSG.KD.Fi24Tc.KV7 43
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1007 : Nat := CFSG.KD.Fi24Tc.KV7 44
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1008 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1004, CFSG.KD.Fi24Tc.Pc.v1005, CFSG.KD.Fi24Tc.Pc.v1006, CFSG.KD.Fi24Tc.Pc.v1007]
theorem CFSG.KD.Fi24Tc.Pc.p1006 : Nat.beq (runC AR SD 1004 (ckL CFSG.KD.Fi24Tc.Pc.l1008) 2 1006 CFSG.KD.Fi24Tc.Pc.l1006) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1008 : Nat := CFSG.KD.Fi24Tc.KV7 45
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1009 : Nat := CFSG.KD.Fi24Tc.KV7 46
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1010 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1004, CFSG.KD.Fi24Tc.Pc.v1005, CFSG.KD.Fi24Tc.Pc.v1006, CFSG.KD.Fi24Tc.Pc.v1007, CFSG.KD.Fi24Tc.Pc.v1008, CFSG.KD.Fi24Tc.Pc.v1009]
theorem CFSG.KD.Fi24Tc.Pc.p1008 : Nat.beq (runC AR SD 1004 (ckL CFSG.KD.Fi24Tc.Pc.l1010) 2 1008 CFSG.KD.Fi24Tc.Pc.l1008) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f148 : Nat.beq (runC AR SD 1004 (finC AR SD (nat_lit 148) 1004 1012) 2 1010 CFSG.KD.Fi24Tc.Pc.l1010) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk148 : chk (nat_lit 148) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 148) (lo := 1004) (hi := 1012) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1006) CFSG.KD.Fi24Tc.Pc.p1004 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1008) CFSG.KD.Fi24Tc.Pc.p1006 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1010) CFSG.KD.Fi24Tc.Pc.p1008 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f148

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1012 : Nat := CFSG.KD.Fi24Tc.KV7 47
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1013 : Nat := CFSG.KD.Fi24Tc.KV7 48
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1014 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1012, CFSG.KD.Fi24Tc.Pc.v1013]
theorem CFSG.KD.Fi24Tc.Pc.p1012 : Nat.beq (runC AR SD 1012 (ckL CFSG.KD.Fi24Tc.Pc.l1014) 2 1012 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1014 : Nat := CFSG.KD.Fi24Tc.KV7 49
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1015 : Nat := CFSG.KD.Fi24Tc.KV7 50
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1016 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1012, CFSG.KD.Fi24Tc.Pc.v1013, CFSG.KD.Fi24Tc.Pc.v1014, CFSG.KD.Fi24Tc.Pc.v1015]
theorem CFSG.KD.Fi24Tc.Pc.p1014 : Nat.beq (runC AR SD 1012 (ckL CFSG.KD.Fi24Tc.Pc.l1016) 2 1014 CFSG.KD.Fi24Tc.Pc.l1014) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1016 : Nat := CFSG.KD.Fi24Tc.KV7 51
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1017 : Nat := CFSG.KD.Fi24Tc.KV7 52
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1018 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1012, CFSG.KD.Fi24Tc.Pc.v1013, CFSG.KD.Fi24Tc.Pc.v1014, CFSG.KD.Fi24Tc.Pc.v1015, CFSG.KD.Fi24Tc.Pc.v1016, CFSG.KD.Fi24Tc.Pc.v1017]
theorem CFSG.KD.Fi24Tc.Pc.p1016 : Nat.beq (runC AR SD 1012 (ckL CFSG.KD.Fi24Tc.Pc.l1018) 2 1016 CFSG.KD.Fi24Tc.Pc.l1016) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f149 : Nat.beq (runC AR SD 1012 (finC AR SD (nat_lit 149) 1012 1020) 2 1018 CFSG.KD.Fi24Tc.Pc.l1018) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk149 : chk (nat_lit 149) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 149) (lo := 1012) (hi := 1020) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1014) CFSG.KD.Fi24Tc.Pc.p1012 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1016) CFSG.KD.Fi24Tc.Pc.p1014 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1018) CFSG.KD.Fi24Tc.Pc.p1016 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f149

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1020 : Nat := CFSG.KD.Fi24Tc.KV7 53
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1021 : Nat := CFSG.KD.Fi24Tc.KV7 54
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1022 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1020, CFSG.KD.Fi24Tc.Pc.v1021]
theorem CFSG.KD.Fi24Tc.Pc.p1020 : Nat.beq (runC AR SD 1020 (ckL CFSG.KD.Fi24Tc.Pc.l1022) 2 1020 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1022 : Nat := CFSG.KD.Fi24Tc.KV7 55
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1023 : Nat := CFSG.KD.Fi24Tc.KV7 56
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1024 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1020, CFSG.KD.Fi24Tc.Pc.v1021, CFSG.KD.Fi24Tc.Pc.v1022, CFSG.KD.Fi24Tc.Pc.v1023]
theorem CFSG.KD.Fi24Tc.Pc.p1022 : Nat.beq (runC AR SD 1020 (ckL CFSG.KD.Fi24Tc.Pc.l1024) 2 1022 CFSG.KD.Fi24Tc.Pc.l1022) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1024 : Nat := CFSG.KD.Fi24Tc.KV7 57
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1025 : Nat := CFSG.KD.Fi24Tc.KV7 58
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1026 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1020, CFSG.KD.Fi24Tc.Pc.v1021, CFSG.KD.Fi24Tc.Pc.v1022, CFSG.KD.Fi24Tc.Pc.v1023, CFSG.KD.Fi24Tc.Pc.v1024, CFSG.KD.Fi24Tc.Pc.v1025]
theorem CFSG.KD.Fi24Tc.Pc.p1024 : Nat.beq (runC AR SD 1020 (ckL CFSG.KD.Fi24Tc.Pc.l1026) 2 1024 CFSG.KD.Fi24Tc.Pc.l1024) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f150 : Nat.beq (runC AR SD 1020 (finC AR SD (nat_lit 150) 1020 1028) 2 1026 CFSG.KD.Fi24Tc.Pc.l1026) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk150 : chk (nat_lit 150) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 150) (lo := 1020) (hi := 1028) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1022) CFSG.KD.Fi24Tc.Pc.p1020 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1024) CFSG.KD.Fi24Tc.Pc.p1022 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1026) CFSG.KD.Fi24Tc.Pc.p1024 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f150

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1028 : Nat := CFSG.KD.Fi24Tc.KV7 59
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1029 : Nat := CFSG.KD.Fi24Tc.KV7 60
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1030 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1028, CFSG.KD.Fi24Tc.Pc.v1029]
theorem CFSG.KD.Fi24Tc.Pc.p1028 : Nat.beq (runC AR SD 1028 (ckL CFSG.KD.Fi24Tc.Pc.l1030) 2 1028 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1030 : Nat := CFSG.KD.Fi24Tc.KV7 61
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1031 : Nat := CFSG.KD.Fi24Tc.KV7 62
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1032 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1028, CFSG.KD.Fi24Tc.Pc.v1029, CFSG.KD.Fi24Tc.Pc.v1030, CFSG.KD.Fi24Tc.Pc.v1031]
theorem CFSG.KD.Fi24Tc.Pc.p1030 : Nat.beq (runC AR SD 1028 (ckL CFSG.KD.Fi24Tc.Pc.l1032) 2 1030 CFSG.KD.Fi24Tc.Pc.l1030) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1032 : Nat := CFSG.KD.Fi24Tc.KV7 63
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1033 : Nat := CFSG.KD.Fi24Tc.KV7 64
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1034 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1028, CFSG.KD.Fi24Tc.Pc.v1029, CFSG.KD.Fi24Tc.Pc.v1030, CFSG.KD.Fi24Tc.Pc.v1031, CFSG.KD.Fi24Tc.Pc.v1032, CFSG.KD.Fi24Tc.Pc.v1033]
theorem CFSG.KD.Fi24Tc.Pc.p1032 : Nat.beq (runC AR SD 1028 (ckL CFSG.KD.Fi24Tc.Pc.l1034) 2 1032 CFSG.KD.Fi24Tc.Pc.l1032) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f151 : Nat.beq (runC AR SD 1028 (finC AR SD (nat_lit 151) 1028 1036) 2 1034 CFSG.KD.Fi24Tc.Pc.l1034) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk151 : chk (nat_lit 151) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 151) (lo := 1028) (hi := 1036) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1030) CFSG.KD.Fi24Tc.Pc.p1028 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1032) CFSG.KD.Fi24Tc.Pc.p1030 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1034) CFSG.KD.Fi24Tc.Pc.p1032 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f151

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1036 : Nat := CFSG.KD.Fi24Tc.KV7 65
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1037 : Nat := CFSG.KD.Fi24Tc.KV7 66
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1038 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1036, CFSG.KD.Fi24Tc.Pc.v1037]
theorem CFSG.KD.Fi24Tc.Pc.p1036 : Nat.beq (runC AR SD 1036 (ckL CFSG.KD.Fi24Tc.Pc.l1038) 2 1036 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1038 : Nat := CFSG.KD.Fi24Tc.KV7 67
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1039 : Nat := CFSG.KD.Fi24Tc.KV7 68
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1040 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1036, CFSG.KD.Fi24Tc.Pc.v1037, CFSG.KD.Fi24Tc.Pc.v1038, CFSG.KD.Fi24Tc.Pc.v1039]
theorem CFSG.KD.Fi24Tc.Pc.p1038 : Nat.beq (runC AR SD 1036 (ckL CFSG.KD.Fi24Tc.Pc.l1040) 2 1038 CFSG.KD.Fi24Tc.Pc.l1038) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1040 : Nat := CFSG.KD.Fi24Tc.KV7 69
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1041 : Nat := CFSG.KD.Fi24Tc.KV7 70
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1042 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1036, CFSG.KD.Fi24Tc.Pc.v1037, CFSG.KD.Fi24Tc.Pc.v1038, CFSG.KD.Fi24Tc.Pc.v1039, CFSG.KD.Fi24Tc.Pc.v1040, CFSG.KD.Fi24Tc.Pc.v1041]
theorem CFSG.KD.Fi24Tc.Pc.p1040 : Nat.beq (runC AR SD 1036 (ckL CFSG.KD.Fi24Tc.Pc.l1042) 2 1040 CFSG.KD.Fi24Tc.Pc.l1040) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f152 : Nat.beq (runC AR SD 1036 (finC AR SD (nat_lit 152) 1036 1044) 2 1042 CFSG.KD.Fi24Tc.Pc.l1042) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk152 : chk (nat_lit 152) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 152) (lo := 1036) (hi := 1044) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1038) CFSG.KD.Fi24Tc.Pc.p1036 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1040) CFSG.KD.Fi24Tc.Pc.p1038 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1042) CFSG.KD.Fi24Tc.Pc.p1040 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f152

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1044 : Nat := CFSG.KD.Fi24Tc.KV7 71
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1045 : Nat := CFSG.KD.Fi24Tc.KV7 72
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1046 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1044, CFSG.KD.Fi24Tc.Pc.v1045]
theorem CFSG.KD.Fi24Tc.Pc.p1044 : Nat.beq (runC AR SD 1044 (ckL CFSG.KD.Fi24Tc.Pc.l1046) 2 1044 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1046 : Nat := CFSG.KD.Fi24Tc.KV7 73
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1047 : Nat := CFSG.KD.Fi24Tc.KV7 74
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1048 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1044, CFSG.KD.Fi24Tc.Pc.v1045, CFSG.KD.Fi24Tc.Pc.v1046, CFSG.KD.Fi24Tc.Pc.v1047]
theorem CFSG.KD.Fi24Tc.Pc.p1046 : Nat.beq (runC AR SD 1044 (ckL CFSG.KD.Fi24Tc.Pc.l1048) 2 1046 CFSG.KD.Fi24Tc.Pc.l1046) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1048 : Nat := CFSG.KD.Fi24Tc.KV7 75
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1049 : Nat := CFSG.KD.Fi24Tc.KV7 76
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1050 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1044, CFSG.KD.Fi24Tc.Pc.v1045, CFSG.KD.Fi24Tc.Pc.v1046, CFSG.KD.Fi24Tc.Pc.v1047, CFSG.KD.Fi24Tc.Pc.v1048, CFSG.KD.Fi24Tc.Pc.v1049]
theorem CFSG.KD.Fi24Tc.Pc.p1048 : Nat.beq (runC AR SD 1044 (ckL CFSG.KD.Fi24Tc.Pc.l1050) 2 1048 CFSG.KD.Fi24Tc.Pc.l1048) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f153 : Nat.beq (runC AR SD 1044 (finC AR SD (nat_lit 153) 1044 1052) 2 1050 CFSG.KD.Fi24Tc.Pc.l1050) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk153 : chk (nat_lit 153) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 153) (lo := 1044) (hi := 1052) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1046) CFSG.KD.Fi24Tc.Pc.p1044 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1048) CFSG.KD.Fi24Tc.Pc.p1046 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1050) CFSG.KD.Fi24Tc.Pc.p1048 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f153

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1052 : Nat := CFSG.KD.Fi24Tc.KV7 77
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1053 : Nat := CFSG.KD.Fi24Tc.KV7 78
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1054 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1052, CFSG.KD.Fi24Tc.Pc.v1053]
theorem CFSG.KD.Fi24Tc.Pc.p1052 : Nat.beq (runC AR SD 1052 (ckL CFSG.KD.Fi24Tc.Pc.l1054) 2 1052 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1054 : Nat := CFSG.KD.Fi24Tc.KV7 79
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1055 : Nat := CFSG.KD.Fi24Tc.KV7 80
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1056 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1052, CFSG.KD.Fi24Tc.Pc.v1053, CFSG.KD.Fi24Tc.Pc.v1054, CFSG.KD.Fi24Tc.Pc.v1055]
theorem CFSG.KD.Fi24Tc.Pc.p1054 : Nat.beq (runC AR SD 1052 (ckL CFSG.KD.Fi24Tc.Pc.l1056) 2 1054 CFSG.KD.Fi24Tc.Pc.l1054) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1056 : Nat := CFSG.KD.Fi24Tc.KV7 81
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1057 : Nat := CFSG.KD.Fi24Tc.KV7 82
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1058 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1052, CFSG.KD.Fi24Tc.Pc.v1053, CFSG.KD.Fi24Tc.Pc.v1054, CFSG.KD.Fi24Tc.Pc.v1055, CFSG.KD.Fi24Tc.Pc.v1056, CFSG.KD.Fi24Tc.Pc.v1057]
theorem CFSG.KD.Fi24Tc.Pc.p1056 : Nat.beq (runC AR SD 1052 (ckL CFSG.KD.Fi24Tc.Pc.l1058) 2 1056 CFSG.KD.Fi24Tc.Pc.l1056) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f154 : Nat.beq (runC AR SD 1052 (finC AR SD (nat_lit 154) 1052 1060) 2 1058 CFSG.KD.Fi24Tc.Pc.l1058) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk154 : chk (nat_lit 154) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 154) (lo := 1052) (hi := 1060) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1054) CFSG.KD.Fi24Tc.Pc.p1052 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1056) CFSG.KD.Fi24Tc.Pc.p1054 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1058) CFSG.KD.Fi24Tc.Pc.p1056 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f154

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1060 : Nat := CFSG.KD.Fi24Tc.KV7 83
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1061 : Nat := CFSG.KD.Fi24Tc.KV7 84
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1062 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1060, CFSG.KD.Fi24Tc.Pc.v1061]
theorem CFSG.KD.Fi24Tc.Pc.p1060 : Nat.beq (runC AR SD 1060 (ckL CFSG.KD.Fi24Tc.Pc.l1062) 2 1060 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1062 : Nat := CFSG.KD.Fi24Tc.KV7 85
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1063 : Nat := CFSG.KD.Fi24Tc.KV7 86
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1064 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1060, CFSG.KD.Fi24Tc.Pc.v1061, CFSG.KD.Fi24Tc.Pc.v1062, CFSG.KD.Fi24Tc.Pc.v1063]
theorem CFSG.KD.Fi24Tc.Pc.p1062 : Nat.beq (runC AR SD 1060 (ckL CFSG.KD.Fi24Tc.Pc.l1064) 2 1062 CFSG.KD.Fi24Tc.Pc.l1062) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1064 : Nat := CFSG.KD.Fi24Tc.KV7 87
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1065 : Nat := CFSG.KD.Fi24Tc.KV7 88
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1066 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1060, CFSG.KD.Fi24Tc.Pc.v1061, CFSG.KD.Fi24Tc.Pc.v1062, CFSG.KD.Fi24Tc.Pc.v1063, CFSG.KD.Fi24Tc.Pc.v1064, CFSG.KD.Fi24Tc.Pc.v1065]
theorem CFSG.KD.Fi24Tc.Pc.p1064 : Nat.beq (runC AR SD 1060 (ckL CFSG.KD.Fi24Tc.Pc.l1066) 2 1064 CFSG.KD.Fi24Tc.Pc.l1064) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f155 : Nat.beq (runC AR SD 1060 (finC AR SD (nat_lit 155) 1060 1068) 2 1066 CFSG.KD.Fi24Tc.Pc.l1066) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk155 : chk (nat_lit 155) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 155) (lo := 1060) (hi := 1068) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1062) CFSG.KD.Fi24Tc.Pc.p1060 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1064) CFSG.KD.Fi24Tc.Pc.p1062 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1066) CFSG.KD.Fi24Tc.Pc.p1064 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f155

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1068 : Nat := CFSG.KD.Fi24Tc.KV7 89
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1069 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1068]
theorem CFSG.KD.Fi24Tc.Pc.p1068 : Nat.beq (runC AR SD 1068 (ckL CFSG.KD.Fi24Tc.Pc.l1069) 1 1068 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1069 : Nat := CFSG.KD.Fi24Tc.KV7 90
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1070 : Nat := CFSG.KD.Fi24Tc.KV7 91
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1071 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1068, CFSG.KD.Fi24Tc.Pc.v1069, CFSG.KD.Fi24Tc.Pc.v1070]
theorem CFSG.KD.Fi24Tc.Pc.p1069 : Nat.beq (runC AR SD 1068 (ckL CFSG.KD.Fi24Tc.Pc.l1071) 2 1069 CFSG.KD.Fi24Tc.Pc.l1069) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1071 : Nat := CFSG.KD.Fi24Tc.KV7 92
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1072 : Nat := CFSG.KD.Fi24Tc.KV7 93
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1073 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1068, CFSG.KD.Fi24Tc.Pc.v1069, CFSG.KD.Fi24Tc.Pc.v1070, CFSG.KD.Fi24Tc.Pc.v1071, CFSG.KD.Fi24Tc.Pc.v1072]
theorem CFSG.KD.Fi24Tc.Pc.p1071 : Nat.beq (runC AR SD 1068 (ckL CFSG.KD.Fi24Tc.Pc.l1073) 2 1071 CFSG.KD.Fi24Tc.Pc.l1071) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f156 : Nat.beq (runC AR SD 1068 (finC AR SD (nat_lit 156) 1068 1075) 2 1073 CFSG.KD.Fi24Tc.Pc.l1073) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk156 : chk (nat_lit 156) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 156) (lo := 1068) (hi := 1075) (m := 7) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 7) (m2 := 6) (j2 := 1069) CFSG.KD.Fi24Tc.Pc.p1068 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1071) CFSG.KD.Fi24Tc.Pc.p1069 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1073) CFSG.KD.Fi24Tc.Pc.p1071 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f156

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1075 : Nat := CFSG.KD.Fi24Tc.KV7 94
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1076 : Nat := CFSG.KD.Fi24Tc.KV7 95
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1077 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1075, CFSG.KD.Fi24Tc.Pc.v1076]
theorem CFSG.KD.Fi24Tc.Pc.p1075 : Nat.beq (runC AR SD 1075 (ckL CFSG.KD.Fi24Tc.Pc.l1077) 2 1075 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1077 : Nat := CFSG.KD.Fi24Tc.KV7 96
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1078 : Nat := CFSG.KD.Fi24Tc.KV7 97
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1079 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1075, CFSG.KD.Fi24Tc.Pc.v1076, CFSG.KD.Fi24Tc.Pc.v1077, CFSG.KD.Fi24Tc.Pc.v1078]
theorem CFSG.KD.Fi24Tc.Pc.p1077 : Nat.beq (runC AR SD 1075 (ckL CFSG.KD.Fi24Tc.Pc.l1079) 2 1077 CFSG.KD.Fi24Tc.Pc.l1077) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1079 : Nat := CFSG.KD.Fi24Tc.KV7 98
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1080 : Nat := CFSG.KD.Fi24Tc.KV7 99
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1081 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1075, CFSG.KD.Fi24Tc.Pc.v1076, CFSG.KD.Fi24Tc.Pc.v1077, CFSG.KD.Fi24Tc.Pc.v1078, CFSG.KD.Fi24Tc.Pc.v1079, CFSG.KD.Fi24Tc.Pc.v1080]
theorem CFSG.KD.Fi24Tc.Pc.p1079 : Nat.beq (runC AR SD 1075 (ckL CFSG.KD.Fi24Tc.Pc.l1081) 2 1079 CFSG.KD.Fi24Tc.Pc.l1079) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f157 : Nat.beq (runC AR SD 1075 (finC AR SD (nat_lit 157) 1075 1083) 2 1081 CFSG.KD.Fi24Tc.Pc.l1081) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk157 : chk (nat_lit 157) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 157) (lo := 1075) (hi := 1083) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1077) CFSG.KD.Fi24Tc.Pc.p1075 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1079) CFSG.KD.Fi24Tc.Pc.p1077 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1081) CFSG.KD.Fi24Tc.Pc.p1079 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f157

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1083 : Nat := CFSG.KD.Fi24Tc.KV7 100
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1084 : Nat := CFSG.KD.Fi24Tc.KV7 101
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1085 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1083, CFSG.KD.Fi24Tc.Pc.v1084]
theorem CFSG.KD.Fi24Tc.Pc.p1083 : Nat.beq (runC AR SD 1083 (ckL CFSG.KD.Fi24Tc.Pc.l1085) 2 1083 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1085 : Nat := CFSG.KD.Fi24Tc.KV7 102
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1086 : Nat := CFSG.KD.Fi24Tc.KV7 103
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1087 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1083, CFSG.KD.Fi24Tc.Pc.v1084, CFSG.KD.Fi24Tc.Pc.v1085, CFSG.KD.Fi24Tc.Pc.v1086]
theorem CFSG.KD.Fi24Tc.Pc.p1085 : Nat.beq (runC AR SD 1083 (ckL CFSG.KD.Fi24Tc.Pc.l1087) 2 1085 CFSG.KD.Fi24Tc.Pc.l1085) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1087 : Nat := CFSG.KD.Fi24Tc.KV7 104
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1088 : Nat := CFSG.KD.Fi24Tc.KV7 105
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1089 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1083, CFSG.KD.Fi24Tc.Pc.v1084, CFSG.KD.Fi24Tc.Pc.v1085, CFSG.KD.Fi24Tc.Pc.v1086, CFSG.KD.Fi24Tc.Pc.v1087, CFSG.KD.Fi24Tc.Pc.v1088]
theorem CFSG.KD.Fi24Tc.Pc.p1087 : Nat.beq (runC AR SD 1083 (ckL CFSG.KD.Fi24Tc.Pc.l1089) 2 1087 CFSG.KD.Fi24Tc.Pc.l1087) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f158 : Nat.beq (runC AR SD 1083 (finC AR SD (nat_lit 158) 1083 1091) 2 1089 CFSG.KD.Fi24Tc.Pc.l1089) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk158 : chk (nat_lit 158) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 158) (lo := 1083) (hi := 1091) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1085) CFSG.KD.Fi24Tc.Pc.p1083 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1087) CFSG.KD.Fi24Tc.Pc.p1085 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1089) CFSG.KD.Fi24Tc.Pc.p1087 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f158

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1091 : Nat := CFSG.KD.Fi24Tc.KV7 106
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1092 : Nat := CFSG.KD.Fi24Tc.KV7 107
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1093 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1091, CFSG.KD.Fi24Tc.Pc.v1092]
theorem CFSG.KD.Fi24Tc.Pc.p1091 : Nat.beq (runC AR SD 1091 (ckL CFSG.KD.Fi24Tc.Pc.l1093) 2 1091 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1093 : Nat := CFSG.KD.Fi24Tc.KV7 108
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1094 : Nat := CFSG.KD.Fi24Tc.KV7 109
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1095 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1091, CFSG.KD.Fi24Tc.Pc.v1092, CFSG.KD.Fi24Tc.Pc.v1093, CFSG.KD.Fi24Tc.Pc.v1094]
theorem CFSG.KD.Fi24Tc.Pc.p1093 : Nat.beq (runC AR SD 1091 (ckL CFSG.KD.Fi24Tc.Pc.l1095) 2 1093 CFSG.KD.Fi24Tc.Pc.l1093) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1095 : Nat := CFSG.KD.Fi24Tc.KV7 110
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v1096 : Nat := CFSG.KD.Fi24Tc.KV7 111
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l1097 : List Nat := [CFSG.KD.Fi24Tc.Pc.v1091, CFSG.KD.Fi24Tc.Pc.v1092, CFSG.KD.Fi24Tc.Pc.v1093, CFSG.KD.Fi24Tc.Pc.v1094, CFSG.KD.Fi24Tc.Pc.v1095, CFSG.KD.Fi24Tc.Pc.v1096]
theorem CFSG.KD.Fi24Tc.Pc.p1095 : Nat.beq (runC AR SD 1091 (ckL CFSG.KD.Fi24Tc.Pc.l1097) 2 1095 CFSG.KD.Fi24Tc.Pc.l1095) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f159 : Nat.beq (runC AR SD 1091 (finC AR SD (nat_lit 159) 1091 1099) 2 1097 CFSG.KD.Fi24Tc.Pc.l1097) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk159 : chk (nat_lit 159) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 159) (lo := 1091) (hi := 1099) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 1093) CFSG.KD.Fi24Tc.Pc.p1091 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 1095) CFSG.KD.Fi24Tc.Pc.p1093 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 1097) CFSG.KD.Fi24Tc.Pc.p1095 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f159

end
