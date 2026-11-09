module

public import Certificates.Kernel.Sporadic.Fi24Cp.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Cp KV1 "Certificates/Kernel/Sporadic/Fi24Cp/data/v1.bin" 152491 4 20128812 3605451959754281298

public section

open CFSG.KD.Fi24Cp CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v128 : Nat := CFSG.KD.Fi24Cp.KV1 0
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v129 : Nat := CFSG.KD.Fi24Cp.KV1 1
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l130 : List Nat := [CFSG.KD.Fi24Cp.Pc.v128, CFSG.KD.Fi24Cp.Pc.v129]
theorem CFSG.KD.Fi24Cp.Pc.p128 : Nat.beq (runC AR SD 128 (ckL CFSG.KD.Fi24Cp.Pc.l130) 2 128 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v130 : Nat := CFSG.KD.Fi24Cp.KV1 2
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v131 : Nat := CFSG.KD.Fi24Cp.KV1 3
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l132 : List Nat := [CFSG.KD.Fi24Cp.Pc.v128, CFSG.KD.Fi24Cp.Pc.v129, CFSG.KD.Fi24Cp.Pc.v130, CFSG.KD.Fi24Cp.Pc.v131]
theorem CFSG.KD.Fi24Cp.Pc.p130 : Nat.beq (runC AR SD 128 (ckL CFSG.KD.Fi24Cp.Pc.l132) 2 130 CFSG.KD.Fi24Cp.Pc.l130) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v132 : Nat := CFSG.KD.Fi24Cp.KV1 4
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v133 : Nat := CFSG.KD.Fi24Cp.KV1 5
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l134 : List Nat := [CFSG.KD.Fi24Cp.Pc.v128, CFSG.KD.Fi24Cp.Pc.v129, CFSG.KD.Fi24Cp.Pc.v130, CFSG.KD.Fi24Cp.Pc.v131, CFSG.KD.Fi24Cp.Pc.v132, CFSG.KD.Fi24Cp.Pc.v133]
theorem CFSG.KD.Fi24Cp.Pc.p132 : Nat.beq (runC AR SD 128 (ckL CFSG.KD.Fi24Cp.Pc.l134) 2 132 CFSG.KD.Fi24Cp.Pc.l132) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v134 : Nat := CFSG.KD.Fi24Cp.KV1 6
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v135 : Nat := CFSG.KD.Fi24Cp.KV1 7
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l136 : List Nat := [CFSG.KD.Fi24Cp.Pc.v128, CFSG.KD.Fi24Cp.Pc.v129, CFSG.KD.Fi24Cp.Pc.v130, CFSG.KD.Fi24Cp.Pc.v131, CFSG.KD.Fi24Cp.Pc.v132, CFSG.KD.Fi24Cp.Pc.v133, CFSG.KD.Fi24Cp.Pc.v134, CFSG.KD.Fi24Cp.Pc.v135]
theorem CFSG.KD.Fi24Cp.Pc.p134 : Nat.beq (runC AR SD 128 (ckL CFSG.KD.Fi24Cp.Pc.l136) 2 134 CFSG.KD.Fi24Cp.Pc.l134) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v136 : Nat := CFSG.KD.Fi24Cp.KV1 8
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l137 : List Nat := [CFSG.KD.Fi24Cp.Pc.v128, CFSG.KD.Fi24Cp.Pc.v129, CFSG.KD.Fi24Cp.Pc.v130, CFSG.KD.Fi24Cp.Pc.v131, CFSG.KD.Fi24Cp.Pc.v132, CFSG.KD.Fi24Cp.Pc.v133, CFSG.KD.Fi24Cp.Pc.v134, CFSG.KD.Fi24Cp.Pc.v135, CFSG.KD.Fi24Cp.Pc.v136]
theorem CFSG.KD.Fi24Cp.Pc.p136 : Nat.beq (runC AR SD 128 (ckL CFSG.KD.Fi24Cp.Pc.l137) 1 136 CFSG.KD.Fi24Cp.Pc.l136) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a137_3 : Nat := CFSG.KD.Fi24Cp.KV1 9
theorem CFSG.KD.Fi24Cp.Pc.q137_3 : Nat.beq (powTop AR.mul (getV AR SD 128 CFSG.KD.Fi24Cp.Pc.l137 (SD.na.getD 137 0)) (SD.nk.getD 137 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a137_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a137_1 : Nat := CFSG.KD.Fi24Cp.KV1 10
theorem CFSG.KD.Fi24Cp.Pc.q137_1 : Nat.beq (powTop AR.mul (getV AR SD 128 CFSG.KD.Fi24Cp.Pc.l137 (SD.na.getD 137 0)) (SD.nk.getD 137 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a137_1) 2 CFSG.KD.Fi24Cp.Pc.a137_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v137 : Nat := CFSG.KD.Fi24Cp.KV1 11
theorem CFSG.KD.Fi24Cp.Pc.r137 : Nat.beq (powR AR.mul AR.one (getV AR SD 128 CFSG.KD.Fi24Cp.Pc.l137 (SD.na.getD 137 0)) (SD.nk.getD 137 1) 1 CFSG.KD.Fi24Cp.Pc.a137_1 true) CFSG.KD.Fi24Cp.Pc.v137 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v138 : Nat := CFSG.KD.Fi24Cp.KV1 12
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l138 : List Nat := [CFSG.KD.Fi24Cp.Pc.v128, CFSG.KD.Fi24Cp.Pc.v129, CFSG.KD.Fi24Cp.Pc.v130, CFSG.KD.Fi24Cp.Pc.v131, CFSG.KD.Fi24Cp.Pc.v132, CFSG.KD.Fi24Cp.Pc.v133, CFSG.KD.Fi24Cp.Pc.v134, CFSG.KD.Fi24Cp.Pc.v135, CFSG.KD.Fi24Cp.Pc.v136, CFSG.KD.Fi24Cp.Pc.v137]
theorem CFSG.KD.Fi24Cp.Pc.f10 : Nat.beq (runC AR SD 128 (finC AR SD (nat_lit 10) 128 139) 1 138 CFSG.KD.Fi24Cp.Pc.l138) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk10 : chk (nat_lit 10) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 10) (lo := 128) (hi := 139) (m := 11) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 11) (m2 := 9) (j2 := 130) CFSG.KD.Fi24Cp.Pc.p128 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 132) CFSG.KD.Fi24Cp.Pc.p130 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 134) CFSG.KD.Fi24Cp.Pc.p132 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 136) CFSG.KD.Fi24Cp.Pc.p134 rfl rfl).trans ((runC_seq (m := 3) (m2 := 2) (j2 := 137) CFSG.KD.Fi24Cp.Pc.p136 rfl rfl).trans (runC_node (m := 2) (m2 := 1) (j2 := 138) (Lr := CFSG.KD.Fi24Cp.Pc.l138) ((nodeV_pow (R := AR) (D := SD) (lo := 128) (L := CFSG.KD.Fi24Cp.Pc.l137) (j := 137) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 128 CFSG.KD.Fi24Cp.Pc.l137 (SD.na.getD 137 0)) (SD.nk.getD 137 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q137_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q137_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r137))))) (by quickRfl) rfl rfl rfl)))))))).trans CFSG.KD.Fi24Cp.Pc.f10

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v139 : Nat := CFSG.KD.Fi24Cp.KV1 13
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v140 : Nat := CFSG.KD.Fi24Cp.KV1 14
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l141 : List Nat := [CFSG.KD.Fi24Cp.Pc.v139, CFSG.KD.Fi24Cp.Pc.v140]
theorem CFSG.KD.Fi24Cp.Pc.p139 : Nat.beq (runC AR SD 139 (ckL CFSG.KD.Fi24Cp.Pc.l141) 2 139 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v141 : Nat := CFSG.KD.Fi24Cp.KV1 15
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v142 : Nat := CFSG.KD.Fi24Cp.KV1 16
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l143 : List Nat := [CFSG.KD.Fi24Cp.Pc.v139, CFSG.KD.Fi24Cp.Pc.v140, CFSG.KD.Fi24Cp.Pc.v141, CFSG.KD.Fi24Cp.Pc.v142]
theorem CFSG.KD.Fi24Cp.Pc.p141 : Nat.beq (runC AR SD 139 (ckL CFSG.KD.Fi24Cp.Pc.l143) 2 141 CFSG.KD.Fi24Cp.Pc.l141) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v143 : Nat := CFSG.KD.Fi24Cp.KV1 17
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v144 : Nat := CFSG.KD.Fi24Cp.KV1 18
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l145 : List Nat := [CFSG.KD.Fi24Cp.Pc.v139, CFSG.KD.Fi24Cp.Pc.v140, CFSG.KD.Fi24Cp.Pc.v141, CFSG.KD.Fi24Cp.Pc.v142, CFSG.KD.Fi24Cp.Pc.v143, CFSG.KD.Fi24Cp.Pc.v144]
theorem CFSG.KD.Fi24Cp.Pc.p143 : Nat.beq (runC AR SD 139 (ckL CFSG.KD.Fi24Cp.Pc.l145) 2 143 CFSG.KD.Fi24Cp.Pc.l143) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v145 : Nat := CFSG.KD.Fi24Cp.KV1 19
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l146 : List Nat := [CFSG.KD.Fi24Cp.Pc.v139, CFSG.KD.Fi24Cp.Pc.v140, CFSG.KD.Fi24Cp.Pc.v141, CFSG.KD.Fi24Cp.Pc.v142, CFSG.KD.Fi24Cp.Pc.v143, CFSG.KD.Fi24Cp.Pc.v144, CFSG.KD.Fi24Cp.Pc.v145]
theorem CFSG.KD.Fi24Cp.Pc.p145 : Nat.beq (runC AR SD 139 (ckL CFSG.KD.Fi24Cp.Pc.l146) 1 145 CFSG.KD.Fi24Cp.Pc.l145) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a146_2 : Nat := CFSG.KD.Fi24Cp.KV1 20
theorem CFSG.KD.Fi24Cp.Pc.q146_2 : Nat.beq (powTop AR.mul (getV AR SD 139 CFSG.KD.Fi24Cp.Pc.l146 (SD.na.getD 146 0)) (SD.nk.getD 146 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a146_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a146_1 : Nat := CFSG.KD.Fi24Cp.KV1 21
theorem CFSG.KD.Fi24Cp.Pc.q146_1 : Nat.beq (powTop AR.mul (getV AR SD 139 CFSG.KD.Fi24Cp.Pc.l146 (SD.na.getD 146 0)) (SD.nk.getD 146 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a146_1) 1 CFSG.KD.Fi24Cp.Pc.a146_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v146 : Nat := CFSG.KD.Fi24Cp.KV1 22
theorem CFSG.KD.Fi24Cp.Pc.r146 : Nat.beq (powR AR.mul AR.one (getV AR SD 139 CFSG.KD.Fi24Cp.Pc.l146 (SD.na.getD 146 0)) (SD.nk.getD 146 1) 1 CFSG.KD.Fi24Cp.Pc.a146_1 true) CFSG.KD.Fi24Cp.Pc.v146 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v147 : Nat := CFSG.KD.Fi24Cp.KV1 23
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v148 : Nat := CFSG.KD.Fi24Cp.KV1 24
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l147 : List Nat := [CFSG.KD.Fi24Cp.Pc.v139, CFSG.KD.Fi24Cp.Pc.v140, CFSG.KD.Fi24Cp.Pc.v141, CFSG.KD.Fi24Cp.Pc.v142, CFSG.KD.Fi24Cp.Pc.v143, CFSG.KD.Fi24Cp.Pc.v144, CFSG.KD.Fi24Cp.Pc.v145, CFSG.KD.Fi24Cp.Pc.v146]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l149 : List Nat := [CFSG.KD.Fi24Cp.Pc.v139, CFSG.KD.Fi24Cp.Pc.v140, CFSG.KD.Fi24Cp.Pc.v141, CFSG.KD.Fi24Cp.Pc.v142, CFSG.KD.Fi24Cp.Pc.v143, CFSG.KD.Fi24Cp.Pc.v144, CFSG.KD.Fi24Cp.Pc.v145, CFSG.KD.Fi24Cp.Pc.v146, CFSG.KD.Fi24Cp.Pc.v147, CFSG.KD.Fi24Cp.Pc.v148]
theorem CFSG.KD.Fi24Cp.Pc.p147 : Nat.beq (runC AR SD 139 (ckL CFSG.KD.Fi24Cp.Pc.l149) 2 147 CFSG.KD.Fi24Cp.Pc.l147) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v149 : Nat := CFSG.KD.Fi24Cp.KV1 25
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v150 : Nat := CFSG.KD.Fi24Cp.KV1 26
theorem CFSG.KD.Fi24Cp.Pc.f11 : Nat.beq (runC AR SD 139 (finC AR SD (nat_lit 11) 139 151) 2 149 CFSG.KD.Fi24Cp.Pc.l149) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk11 : chk (nat_lit 11) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 11) (lo := 139) (hi := 151) (m := 12) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 12) (m2 := 10) (j2 := 141) CFSG.KD.Fi24Cp.Pc.p139 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 143) CFSG.KD.Fi24Cp.Pc.p141 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 145) CFSG.KD.Fi24Cp.Pc.p143 rfl rfl).trans ((runC_seq (m := 6) (m2 := 5) (j2 := 146) CFSG.KD.Fi24Cp.Pc.p145 rfl rfl).trans ((runC_node (m := 5) (m2 := 4) (j2 := 147) (Lr := CFSG.KD.Fi24Cp.Pc.l147) ((nodeV_pow (R := AR) (D := SD) (lo := 139) (L := CFSG.KD.Fi24Cp.Pc.l146) (j := 146) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 139 CFSG.KD.Fi24Cp.Pc.l146 (SD.na.getD 146 0)) (SD.nk.getD 146 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q146_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q146_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r146))))) (by quickRfl) rfl rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 149) CFSG.KD.Fi24Cp.Pc.p147 rfl rfl)))))))).trans CFSG.KD.Fi24Cp.Pc.f11

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v151 : Nat := CFSG.KD.Fi24Cp.KV1 27
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v152 : Nat := CFSG.KD.Fi24Cp.KV1 28
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l153 : List Nat := [CFSG.KD.Fi24Cp.Pc.v151, CFSG.KD.Fi24Cp.Pc.v152]
theorem CFSG.KD.Fi24Cp.Pc.p151 : Nat.beq (runC AR SD 151 (ckL CFSG.KD.Fi24Cp.Pc.l153) 2 151 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a153_3 : Nat := CFSG.KD.Fi24Cp.KV1 29
theorem CFSG.KD.Fi24Cp.Pc.q153_3 : Nat.beq (powTop AR.mul (getV AR SD 151 CFSG.KD.Fi24Cp.Pc.l153 (SD.na.getD 153 0)) (SD.nk.getD 153 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a153_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a153_1 : Nat := CFSG.KD.Fi24Cp.KV1 30
theorem CFSG.KD.Fi24Cp.Pc.q153_1 : Nat.beq (powTop AR.mul (getV AR SD 151 CFSG.KD.Fi24Cp.Pc.l153 (SD.na.getD 153 0)) (SD.nk.getD 153 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a153_1) 2 CFSG.KD.Fi24Cp.Pc.a153_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v153 : Nat := CFSG.KD.Fi24Cp.KV1 31
theorem CFSG.KD.Fi24Cp.Pc.r153 : Nat.beq (powR AR.mul AR.one (getV AR SD 151 CFSG.KD.Fi24Cp.Pc.l153 (SD.na.getD 153 0)) (SD.nk.getD 153 1) 1 CFSG.KD.Fi24Cp.Pc.a153_1 true) CFSG.KD.Fi24Cp.Pc.v153 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v154 : Nat := CFSG.KD.Fi24Cp.KV1 32
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v155 : Nat := CFSG.KD.Fi24Cp.KV1 33
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l154 : List Nat := [CFSG.KD.Fi24Cp.Pc.v151, CFSG.KD.Fi24Cp.Pc.v152, CFSG.KD.Fi24Cp.Pc.v153]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l156 : List Nat := [CFSG.KD.Fi24Cp.Pc.v151, CFSG.KD.Fi24Cp.Pc.v152, CFSG.KD.Fi24Cp.Pc.v153, CFSG.KD.Fi24Cp.Pc.v154, CFSG.KD.Fi24Cp.Pc.v155]
theorem CFSG.KD.Fi24Cp.Pc.p154 : Nat.beq (runC AR SD 151 (ckL CFSG.KD.Fi24Cp.Pc.l156) 2 154 CFSG.KD.Fi24Cp.Pc.l154) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v156 : Nat := CFSG.KD.Fi24Cp.KV1 34
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v157 : Nat := CFSG.KD.Fi24Cp.KV1 35
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l158 : List Nat := [CFSG.KD.Fi24Cp.Pc.v151, CFSG.KD.Fi24Cp.Pc.v152, CFSG.KD.Fi24Cp.Pc.v153, CFSG.KD.Fi24Cp.Pc.v154, CFSG.KD.Fi24Cp.Pc.v155, CFSG.KD.Fi24Cp.Pc.v156, CFSG.KD.Fi24Cp.Pc.v157]
theorem CFSG.KD.Fi24Cp.Pc.p156 : Nat.beq (runC AR SD 151 (ckL CFSG.KD.Fi24Cp.Pc.l158) 2 156 CFSG.KD.Fi24Cp.Pc.l156) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v158 : Nat := CFSG.KD.Fi24Cp.KV1 36
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v159 : Nat := CFSG.KD.Fi24Cp.KV1 37
theorem CFSG.KD.Fi24Cp.Pc.f12 : Nat.beq (runC AR SD 151 (finC AR SD (nat_lit 12) 151 160) 2 158 CFSG.KD.Fi24Cp.Pc.l158) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk12 : chk (nat_lit 12) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 12) (lo := 151) (hi := 160) (m := 9) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 9) (m2 := 7) (j2 := 153) CFSG.KD.Fi24Cp.Pc.p151 rfl rfl).trans ((runC_node (m := 7) (m2 := 6) (j2 := 154) (Lr := CFSG.KD.Fi24Cp.Pc.l154) ((nodeV_pow (R := AR) (D := SD) (lo := 151) (L := CFSG.KD.Fi24Cp.Pc.l153) (j := 153) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 151 CFSG.KD.Fi24Cp.Pc.l153 (SD.na.getD 153 0)) (SD.nk.getD 153 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q153_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q153_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r153))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 156) CFSG.KD.Fi24Cp.Pc.p154 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 158) CFSG.KD.Fi24Cp.Pc.p156 rfl rfl)))))).trans CFSG.KD.Fi24Cp.Pc.f12

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a160_3 : Nat := CFSG.KD.Fi24Cp.KV1 38
theorem CFSG.KD.Fi24Cp.Pc.q160_3 : Nat.beq (powTop AR.mul (getV AR SD 160 [] (SD.na.getD 160 0)) (SD.nk.getD 160 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a160_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a160_2 : Nat := CFSG.KD.Fi24Cp.KV1 39
theorem CFSG.KD.Fi24Cp.Pc.q160_2 : Nat.beq (powTop AR.mul (getV AR SD 160 [] (SD.na.getD 160 0)) (SD.nk.getD 160 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a160_2) 1 CFSG.KD.Fi24Cp.Pc.a160_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a160_1 : Nat := CFSG.KD.Fi24Cp.KV1 40
theorem CFSG.KD.Fi24Cp.Pc.q160_1 : Nat.beq (powTop AR.mul (getV AR SD 160 [] (SD.na.getD 160 0)) (SD.nk.getD 160 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a160_1) 1 CFSG.KD.Fi24Cp.Pc.a160_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v160 : Nat := CFSG.KD.Fi24Cp.KV1 41
theorem CFSG.KD.Fi24Cp.Pc.r160 : Nat.beq (powR AR.mul AR.one (getV AR SD 160 [] (SD.na.getD 160 0)) (SD.nk.getD 160 1) 1 CFSG.KD.Fi24Cp.Pc.a160_1 true) CFSG.KD.Fi24Cp.Pc.v160 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v161 : Nat := CFSG.KD.Fi24Cp.KV1 42
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v162 : Nat := CFSG.KD.Fi24Cp.KV1 43
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l161 : List Nat := [CFSG.KD.Fi24Cp.Pc.v160]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l163 : List Nat := [CFSG.KD.Fi24Cp.Pc.v160, CFSG.KD.Fi24Cp.Pc.v161, CFSG.KD.Fi24Cp.Pc.v162]
theorem CFSG.KD.Fi24Cp.Pc.p161 : Nat.beq (runC AR SD 160 (ckL CFSG.KD.Fi24Cp.Pc.l163) 2 161 CFSG.KD.Fi24Cp.Pc.l161) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v163 : Nat := CFSG.KD.Fi24Cp.KV1 44
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v164 : Nat := CFSG.KD.Fi24Cp.KV1 45
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l165 : List Nat := [CFSG.KD.Fi24Cp.Pc.v160, CFSG.KD.Fi24Cp.Pc.v161, CFSG.KD.Fi24Cp.Pc.v162, CFSG.KD.Fi24Cp.Pc.v163, CFSG.KD.Fi24Cp.Pc.v164]
theorem CFSG.KD.Fi24Cp.Pc.p163 : Nat.beq (runC AR SD 160 (ckL CFSG.KD.Fi24Cp.Pc.l165) 2 163 CFSG.KD.Fi24Cp.Pc.l163) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v165 : Nat := CFSG.KD.Fi24Cp.KV1 46
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l166 : List Nat := [CFSG.KD.Fi24Cp.Pc.v160, CFSG.KD.Fi24Cp.Pc.v161, CFSG.KD.Fi24Cp.Pc.v162, CFSG.KD.Fi24Cp.Pc.v163, CFSG.KD.Fi24Cp.Pc.v164, CFSG.KD.Fi24Cp.Pc.v165]
theorem CFSG.KD.Fi24Cp.Pc.p165 : Nat.beq (runC AR SD 160 (ckL CFSG.KD.Fi24Cp.Pc.l166) 1 165 CFSG.KD.Fi24Cp.Pc.l165) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a166_1 : Nat := CFSG.KD.Fi24Cp.KV1 47
theorem CFSG.KD.Fi24Cp.Pc.q166_1 : Nat.beq (powTop AR.mul (getV AR SD 160 CFSG.KD.Fi24Cp.Pc.l166 (SD.na.getD 166 0)) (SD.nk.getD 166 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a166_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v166 : Nat := CFSG.KD.Fi24Cp.KV1 48
theorem CFSG.KD.Fi24Cp.Pc.r166 : Nat.beq (powR AR.mul AR.one (getV AR SD 160 CFSG.KD.Fi24Cp.Pc.l166 (SD.na.getD 166 0)) (SD.nk.getD 166 1) 1 CFSG.KD.Fi24Cp.Pc.a166_1 true) CFSG.KD.Fi24Cp.Pc.v166 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l167 : List Nat := [CFSG.KD.Fi24Cp.Pc.v160, CFSG.KD.Fi24Cp.Pc.v161, CFSG.KD.Fi24Cp.Pc.v162, CFSG.KD.Fi24Cp.Pc.v163, CFSG.KD.Fi24Cp.Pc.v164, CFSG.KD.Fi24Cp.Pc.v165, CFSG.KD.Fi24Cp.Pc.v166]
theorem CFSG.KD.Fi24Cp.Pc.f13 : Nat.beq (runC AR SD 160 (finC AR SD (nat_lit 13) 160 167) 0 167 CFSG.KD.Fi24Cp.Pc.l167) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk13 : chk (nat_lit 13) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 13) (lo := 160) (hi := 167) (m := 7) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 7) (m2 := 6) (j2 := 161) (Lr := CFSG.KD.Fi24Cp.Pc.l161) ((nodeV_pow (R := AR) (D := SD) (lo := 160) (L := []) (j := 160) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 160 [] (SD.na.getD 160 0)) (SD.nk.getD 160 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q160_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q160_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q160_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r160)))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 163) CFSG.KD.Fi24Cp.Pc.p161 rfl rfl).trans ((runC_seq (m := 4) (m2 := 2) (j2 := 165) CFSG.KD.Fi24Cp.Pc.p163 rfl rfl).trans ((runC_seq (m := 2) (m2 := 1) (j2 := 166) CFSG.KD.Fi24Cp.Pc.p165 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 167) (Lr := CFSG.KD.Fi24Cp.Pc.l167) ((nodeV_pow (R := AR) (D := SD) (lo := 160) (L := CFSG.KD.Fi24Cp.Pc.l166) (j := 166) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 160 CFSG.KD.Fi24Cp.Pc.l166 (SD.na.getD 166 0)) (SD.nk.getD 166 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q166_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r166)))) (by quickRfl) rfl rfl rfl))))))).trans CFSG.KD.Fi24Cp.Pc.f13

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v167 : Nat := CFSG.KD.Fi24Cp.KV1 49
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v168 : Nat := CFSG.KD.Fi24Cp.KV1 50
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l169 : List Nat := [CFSG.KD.Fi24Cp.Pc.v167, CFSG.KD.Fi24Cp.Pc.v168]
theorem CFSG.KD.Fi24Cp.Pc.p167 : Nat.beq (runC AR SD 167 (ckL CFSG.KD.Fi24Cp.Pc.l169) 2 167 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v169 : Nat := CFSG.KD.Fi24Cp.KV1 51
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v170 : Nat := CFSG.KD.Fi24Cp.KV1 52
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l171 : List Nat := [CFSG.KD.Fi24Cp.Pc.v167, CFSG.KD.Fi24Cp.Pc.v168, CFSG.KD.Fi24Cp.Pc.v169, CFSG.KD.Fi24Cp.Pc.v170]
theorem CFSG.KD.Fi24Cp.Pc.p169 : Nat.beq (runC AR SD 167 (ckL CFSG.KD.Fi24Cp.Pc.l171) 2 169 CFSG.KD.Fi24Cp.Pc.l169) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v171 : Nat := CFSG.KD.Fi24Cp.KV1 53
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v172 : Nat := CFSG.KD.Fi24Cp.KV1 54
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l173 : List Nat := [CFSG.KD.Fi24Cp.Pc.v167, CFSG.KD.Fi24Cp.Pc.v168, CFSG.KD.Fi24Cp.Pc.v169, CFSG.KD.Fi24Cp.Pc.v170, CFSG.KD.Fi24Cp.Pc.v171, CFSG.KD.Fi24Cp.Pc.v172]
theorem CFSG.KD.Fi24Cp.Pc.p171 : Nat.beq (runC AR SD 167 (ckL CFSG.KD.Fi24Cp.Pc.l173) 2 171 CFSG.KD.Fi24Cp.Pc.l171) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v173 : Nat := CFSG.KD.Fi24Cp.KV1 55
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v174 : Nat := CFSG.KD.Fi24Cp.KV1 56
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l175 : List Nat := [CFSG.KD.Fi24Cp.Pc.v167, CFSG.KD.Fi24Cp.Pc.v168, CFSG.KD.Fi24Cp.Pc.v169, CFSG.KD.Fi24Cp.Pc.v170, CFSG.KD.Fi24Cp.Pc.v171, CFSG.KD.Fi24Cp.Pc.v172, CFSG.KD.Fi24Cp.Pc.v173, CFSG.KD.Fi24Cp.Pc.v174]
theorem CFSG.KD.Fi24Cp.Pc.p173 : Nat.beq (runC AR SD 167 (ckL CFSG.KD.Fi24Cp.Pc.l175) 2 173 CFSG.KD.Fi24Cp.Pc.l173) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v175 : Nat := CFSG.KD.Fi24Cp.KV1 57
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v176 : Nat := CFSG.KD.Fi24Cp.KV1 58
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l177 : List Nat := [CFSG.KD.Fi24Cp.Pc.v167, CFSG.KD.Fi24Cp.Pc.v168, CFSG.KD.Fi24Cp.Pc.v169, CFSG.KD.Fi24Cp.Pc.v170, CFSG.KD.Fi24Cp.Pc.v171, CFSG.KD.Fi24Cp.Pc.v172, CFSG.KD.Fi24Cp.Pc.v173, CFSG.KD.Fi24Cp.Pc.v174, CFSG.KD.Fi24Cp.Pc.v175, CFSG.KD.Fi24Cp.Pc.v176]
theorem CFSG.KD.Fi24Cp.Pc.p175 : Nat.beq (runC AR SD 167 (ckL CFSG.KD.Fi24Cp.Pc.l177) 2 175 CFSG.KD.Fi24Cp.Pc.l175) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v177 : Nat := CFSG.KD.Fi24Cp.KV1 59
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v178 : Nat := CFSG.KD.Fi24Cp.KV1 60
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l179 : List Nat := [CFSG.KD.Fi24Cp.Pc.v167, CFSG.KD.Fi24Cp.Pc.v168, CFSG.KD.Fi24Cp.Pc.v169, CFSG.KD.Fi24Cp.Pc.v170, CFSG.KD.Fi24Cp.Pc.v171, CFSG.KD.Fi24Cp.Pc.v172, CFSG.KD.Fi24Cp.Pc.v173, CFSG.KD.Fi24Cp.Pc.v174, CFSG.KD.Fi24Cp.Pc.v175, CFSG.KD.Fi24Cp.Pc.v176, CFSG.KD.Fi24Cp.Pc.v177, CFSG.KD.Fi24Cp.Pc.v178]
theorem CFSG.KD.Fi24Cp.Pc.p177 : Nat.beq (runC AR SD 167 (ckL CFSG.KD.Fi24Cp.Pc.l179) 2 177 CFSG.KD.Fi24Cp.Pc.l177) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v179 : Nat := CFSG.KD.Fi24Cp.KV1 61
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v180 : Nat := CFSG.KD.Fi24Cp.KV1 62
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l181 : List Nat := [CFSG.KD.Fi24Cp.Pc.v167, CFSG.KD.Fi24Cp.Pc.v168, CFSG.KD.Fi24Cp.Pc.v169, CFSG.KD.Fi24Cp.Pc.v170, CFSG.KD.Fi24Cp.Pc.v171, CFSG.KD.Fi24Cp.Pc.v172, CFSG.KD.Fi24Cp.Pc.v173, CFSG.KD.Fi24Cp.Pc.v174, CFSG.KD.Fi24Cp.Pc.v175, CFSG.KD.Fi24Cp.Pc.v176, CFSG.KD.Fi24Cp.Pc.v177, CFSG.KD.Fi24Cp.Pc.v178, CFSG.KD.Fi24Cp.Pc.v179, CFSG.KD.Fi24Cp.Pc.v180]
theorem CFSG.KD.Fi24Cp.Pc.p179 : Nat.beq (runC AR SD 167 (ckL CFSG.KD.Fi24Cp.Pc.l181) 2 179 CFSG.KD.Fi24Cp.Pc.l179) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v181 : Nat := CFSG.KD.Fi24Cp.KV1 63
theorem CFSG.KD.Fi24Cp.Pc.f14 : Nat.beq (runC AR SD 167 (finC AR SD (nat_lit 14) 167 182) 1 181 CFSG.KD.Fi24Cp.Pc.l181) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk14 : chk (nat_lit 14) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 14) (lo := 167) (hi := 182) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 169) CFSG.KD.Fi24Cp.Pc.p167 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 171) CFSG.KD.Fi24Cp.Pc.p169 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 173) CFSG.KD.Fi24Cp.Pc.p171 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 175) CFSG.KD.Fi24Cp.Pc.p173 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 177) CFSG.KD.Fi24Cp.Pc.p175 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 179) CFSG.KD.Fi24Cp.Pc.p177 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 181) CFSG.KD.Fi24Cp.Pc.p179 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f14

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v182 : Nat := CFSG.KD.Fi24Cp.KV1 64
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v183 : Nat := CFSG.KD.Fi24Cp.KV1 65
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l184 : List Nat := [CFSG.KD.Fi24Cp.Pc.v182, CFSG.KD.Fi24Cp.Pc.v183]
theorem CFSG.KD.Fi24Cp.Pc.p182 : Nat.beq (runC AR SD 182 (ckL CFSG.KD.Fi24Cp.Pc.l184) 2 182 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v184 : Nat := CFSG.KD.Fi24Cp.KV1 66
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l185 : List Nat := [CFSG.KD.Fi24Cp.Pc.v182, CFSG.KD.Fi24Cp.Pc.v183, CFSG.KD.Fi24Cp.Pc.v184]
theorem CFSG.KD.Fi24Cp.Pc.p184 : Nat.beq (runC AR SD 182 (ckL CFSG.KD.Fi24Cp.Pc.l185) 1 184 CFSG.KD.Fi24Cp.Pc.l184) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a185_3 : Nat := CFSG.KD.Fi24Cp.KV1 67
theorem CFSG.KD.Fi24Cp.Pc.q185_3 : Nat.beq (powTop AR.mul (getV AR SD 182 CFSG.KD.Fi24Cp.Pc.l185 (SD.na.getD 185 0)) (SD.nk.getD 185 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a185_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a185_2 : Nat := CFSG.KD.Fi24Cp.KV1 68
theorem CFSG.KD.Fi24Cp.Pc.q185_2 : Nat.beq (powTop AR.mul (getV AR SD 182 CFSG.KD.Fi24Cp.Pc.l185 (SD.na.getD 185 0)) (SD.nk.getD 185 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a185_2) 1 CFSG.KD.Fi24Cp.Pc.a185_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a185_1 : Nat := CFSG.KD.Fi24Cp.KV1 69
theorem CFSG.KD.Fi24Cp.Pc.q185_1 : Nat.beq (powTop AR.mul (getV AR SD 182 CFSG.KD.Fi24Cp.Pc.l185 (SD.na.getD 185 0)) (SD.nk.getD 185 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a185_1) 1 CFSG.KD.Fi24Cp.Pc.a185_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v185 : Nat := CFSG.KD.Fi24Cp.KV1 70
theorem CFSG.KD.Fi24Cp.Pc.r185 : Nat.beq (powR AR.mul AR.one (getV AR SD 182 CFSG.KD.Fi24Cp.Pc.l185 (SD.na.getD 185 0)) (SD.nk.getD 185 1) 1 CFSG.KD.Fi24Cp.Pc.a185_1 true) CFSG.KD.Fi24Cp.Pc.v185 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v186 : Nat := CFSG.KD.Fi24Cp.KV1 71
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v187 : Nat := CFSG.KD.Fi24Cp.KV1 72
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l186 : List Nat := [CFSG.KD.Fi24Cp.Pc.v182, CFSG.KD.Fi24Cp.Pc.v183, CFSG.KD.Fi24Cp.Pc.v184, CFSG.KD.Fi24Cp.Pc.v185]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l188 : List Nat := [CFSG.KD.Fi24Cp.Pc.v182, CFSG.KD.Fi24Cp.Pc.v183, CFSG.KD.Fi24Cp.Pc.v184, CFSG.KD.Fi24Cp.Pc.v185, CFSG.KD.Fi24Cp.Pc.v186, CFSG.KD.Fi24Cp.Pc.v187]
theorem CFSG.KD.Fi24Cp.Pc.p186 : Nat.beq (runC AR SD 182 (ckL CFSG.KD.Fi24Cp.Pc.l188) 2 186 CFSG.KD.Fi24Cp.Pc.l186) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v188 : Nat := CFSG.KD.Fi24Cp.KV1 73
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v189 : Nat := CFSG.KD.Fi24Cp.KV1 74
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l190 : List Nat := [CFSG.KD.Fi24Cp.Pc.v182, CFSG.KD.Fi24Cp.Pc.v183, CFSG.KD.Fi24Cp.Pc.v184, CFSG.KD.Fi24Cp.Pc.v185, CFSG.KD.Fi24Cp.Pc.v186, CFSG.KD.Fi24Cp.Pc.v187, CFSG.KD.Fi24Cp.Pc.v188, CFSG.KD.Fi24Cp.Pc.v189]
theorem CFSG.KD.Fi24Cp.Pc.p188 : Nat.beq (runC AR SD 182 (ckL CFSG.KD.Fi24Cp.Pc.l190) 2 188 CFSG.KD.Fi24Cp.Pc.l188) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v190 : Nat := CFSG.KD.Fi24Cp.KV1 75
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v191 : Nat := CFSG.KD.Fi24Cp.KV1 76
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l192 : List Nat := [CFSG.KD.Fi24Cp.Pc.v182, CFSG.KD.Fi24Cp.Pc.v183, CFSG.KD.Fi24Cp.Pc.v184, CFSG.KD.Fi24Cp.Pc.v185, CFSG.KD.Fi24Cp.Pc.v186, CFSG.KD.Fi24Cp.Pc.v187, CFSG.KD.Fi24Cp.Pc.v188, CFSG.KD.Fi24Cp.Pc.v189, CFSG.KD.Fi24Cp.Pc.v190, CFSG.KD.Fi24Cp.Pc.v191]
theorem CFSG.KD.Fi24Cp.Pc.p190 : Nat.beq (runC AR SD 182 (ckL CFSG.KD.Fi24Cp.Pc.l192) 2 190 CFSG.KD.Fi24Cp.Pc.l190) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v192 : Nat := CFSG.KD.Fi24Cp.KV1 77
theorem CFSG.KD.Fi24Cp.Pc.f15 : Nat.beq (runC AR SD 182 (finC AR SD (nat_lit 15) 182 193) 1 192 CFSG.KD.Fi24Cp.Pc.l192) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk15 : chk (nat_lit 15) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 15) (lo := 182) (hi := 193) (m := 11) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 11) (m2 := 9) (j2 := 184) CFSG.KD.Fi24Cp.Pc.p182 rfl rfl).trans ((runC_seq (m := 9) (m2 := 8) (j2 := 185) CFSG.KD.Fi24Cp.Pc.p184 rfl rfl).trans ((runC_node (m := 8) (m2 := 7) (j2 := 186) (Lr := CFSG.KD.Fi24Cp.Pc.l186) ((nodeV_pow (R := AR) (D := SD) (lo := 182) (L := CFSG.KD.Fi24Cp.Pc.l185) (j := 185) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 182 CFSG.KD.Fi24Cp.Pc.l185 (SD.na.getD 185 0)) (SD.nk.getD 185 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q185_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q185_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q185_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r185)))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 188) CFSG.KD.Fi24Cp.Pc.p186 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 190) CFSG.KD.Fi24Cp.Pc.p188 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 192) CFSG.KD.Fi24Cp.Pc.p190 rfl rfl)))))))).trans CFSG.KD.Fi24Cp.Pc.f15

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v193 : Nat := CFSG.KD.Fi24Cp.KV1 78
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v194 : Nat := CFSG.KD.Fi24Cp.KV1 79
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l195 : List Nat := [CFSG.KD.Fi24Cp.Pc.v193, CFSG.KD.Fi24Cp.Pc.v194]
theorem CFSG.KD.Fi24Cp.Pc.p193 : Nat.beq (runC AR SD 193 (ckL CFSG.KD.Fi24Cp.Pc.l195) 2 193 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v195 : Nat := CFSG.KD.Fi24Cp.KV1 80
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v196 : Nat := CFSG.KD.Fi24Cp.KV1 81
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l197 : List Nat := [CFSG.KD.Fi24Cp.Pc.v193, CFSG.KD.Fi24Cp.Pc.v194, CFSG.KD.Fi24Cp.Pc.v195, CFSG.KD.Fi24Cp.Pc.v196]
theorem CFSG.KD.Fi24Cp.Pc.p195 : Nat.beq (runC AR SD 193 (ckL CFSG.KD.Fi24Cp.Pc.l197) 2 195 CFSG.KD.Fi24Cp.Pc.l195) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v197 : Nat := CFSG.KD.Fi24Cp.KV1 82
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v198 : Nat := CFSG.KD.Fi24Cp.KV1 83
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l199 : List Nat := [CFSG.KD.Fi24Cp.Pc.v193, CFSG.KD.Fi24Cp.Pc.v194, CFSG.KD.Fi24Cp.Pc.v195, CFSG.KD.Fi24Cp.Pc.v196, CFSG.KD.Fi24Cp.Pc.v197, CFSG.KD.Fi24Cp.Pc.v198]
theorem CFSG.KD.Fi24Cp.Pc.p197 : Nat.beq (runC AR SD 193 (ckL CFSG.KD.Fi24Cp.Pc.l199) 2 197 CFSG.KD.Fi24Cp.Pc.l197) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v199 : Nat := CFSG.KD.Fi24Cp.KV1 84
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v200 : Nat := CFSG.KD.Fi24Cp.KV1 85
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l201 : List Nat := [CFSG.KD.Fi24Cp.Pc.v193, CFSG.KD.Fi24Cp.Pc.v194, CFSG.KD.Fi24Cp.Pc.v195, CFSG.KD.Fi24Cp.Pc.v196, CFSG.KD.Fi24Cp.Pc.v197, CFSG.KD.Fi24Cp.Pc.v198, CFSG.KD.Fi24Cp.Pc.v199, CFSG.KD.Fi24Cp.Pc.v200]
theorem CFSG.KD.Fi24Cp.Pc.p199 : Nat.beq (runC AR SD 193 (ckL CFSG.KD.Fi24Cp.Pc.l201) 2 199 CFSG.KD.Fi24Cp.Pc.l199) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v201 : Nat := CFSG.KD.Fi24Cp.KV1 86
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l202 : List Nat := [CFSG.KD.Fi24Cp.Pc.v193, CFSG.KD.Fi24Cp.Pc.v194, CFSG.KD.Fi24Cp.Pc.v195, CFSG.KD.Fi24Cp.Pc.v196, CFSG.KD.Fi24Cp.Pc.v197, CFSG.KD.Fi24Cp.Pc.v198, CFSG.KD.Fi24Cp.Pc.v199, CFSG.KD.Fi24Cp.Pc.v200, CFSG.KD.Fi24Cp.Pc.v201]
theorem CFSG.KD.Fi24Cp.Pc.p201 : Nat.beq (runC AR SD 193 (ckL CFSG.KD.Fi24Cp.Pc.l202) 1 201 CFSG.KD.Fi24Cp.Pc.l201) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a202_3 : Nat := CFSG.KD.Fi24Cp.KV1 87
theorem CFSG.KD.Fi24Cp.Pc.q202_3 : Nat.beq (powTop AR.mul (getV AR SD 193 CFSG.KD.Fi24Cp.Pc.l202 (SD.na.getD 202 0)) (SD.nk.getD 202 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a202_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a202_2 : Nat := CFSG.KD.Fi24Cp.KV1 88
theorem CFSG.KD.Fi24Cp.Pc.q202_2 : Nat.beq (powTop AR.mul (getV AR SD 193 CFSG.KD.Fi24Cp.Pc.l202 (SD.na.getD 202 0)) (SD.nk.getD 202 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a202_2) 1 CFSG.KD.Fi24Cp.Pc.a202_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a202_1 : Nat := CFSG.KD.Fi24Cp.KV1 89
theorem CFSG.KD.Fi24Cp.Pc.q202_1 : Nat.beq (powTop AR.mul (getV AR SD 193 CFSG.KD.Fi24Cp.Pc.l202 (SD.na.getD 202 0)) (SD.nk.getD 202 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a202_1) 1 CFSG.KD.Fi24Cp.Pc.a202_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v202 : Nat := CFSG.KD.Fi24Cp.KV1 90
theorem CFSG.KD.Fi24Cp.Pc.r202 : Nat.beq (powR AR.mul AR.one (getV AR SD 193 CFSG.KD.Fi24Cp.Pc.l202 (SD.na.getD 202 0)) (SD.nk.getD 202 1) 1 CFSG.KD.Fi24Cp.Pc.a202_1 true) CFSG.KD.Fi24Cp.Pc.v202 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l203 : List Nat := [CFSG.KD.Fi24Cp.Pc.v193, CFSG.KD.Fi24Cp.Pc.v194, CFSG.KD.Fi24Cp.Pc.v195, CFSG.KD.Fi24Cp.Pc.v196, CFSG.KD.Fi24Cp.Pc.v197, CFSG.KD.Fi24Cp.Pc.v198, CFSG.KD.Fi24Cp.Pc.v199, CFSG.KD.Fi24Cp.Pc.v200, CFSG.KD.Fi24Cp.Pc.v201, CFSG.KD.Fi24Cp.Pc.v202]
theorem CFSG.KD.Fi24Cp.Pc.f16 : Nat.beq (runC AR SD 193 (finC AR SD (nat_lit 16) 193 203) 0 203 CFSG.KD.Fi24Cp.Pc.l203) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk16 : chk (nat_lit 16) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 16) (lo := 193) (hi := 203) (m := 10) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 10) (m2 := 8) (j2 := 195) CFSG.KD.Fi24Cp.Pc.p193 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 197) CFSG.KD.Fi24Cp.Pc.p195 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 199) CFSG.KD.Fi24Cp.Pc.p197 rfl rfl).trans ((runC_seq (m := 4) (m2 := 2) (j2 := 201) CFSG.KD.Fi24Cp.Pc.p199 rfl rfl).trans ((runC_seq (m := 2) (m2 := 1) (j2 := 202) CFSG.KD.Fi24Cp.Pc.p201 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 203) (Lr := CFSG.KD.Fi24Cp.Pc.l203) ((nodeV_pow (R := AR) (D := SD) (lo := 193) (L := CFSG.KD.Fi24Cp.Pc.l202) (j := 202) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 193 CFSG.KD.Fi24Cp.Pc.l202 (SD.na.getD 202 0)) (SD.nk.getD 202 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q202_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q202_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q202_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r202)))))) (by quickRfl) rfl rfl rfl)))))))).trans CFSG.KD.Fi24Cp.Pc.f16

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v203 : Nat := CFSG.KD.Fi24Cp.KV1 91
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v204 : Nat := CFSG.KD.Fi24Cp.KV1 92
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l205 : List Nat := [CFSG.KD.Fi24Cp.Pc.v203, CFSG.KD.Fi24Cp.Pc.v204]
theorem CFSG.KD.Fi24Cp.Pc.p203 : Nat.beq (runC AR SD 203 (ckL CFSG.KD.Fi24Cp.Pc.l205) 2 203 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v205 : Nat := CFSG.KD.Fi24Cp.KV1 93
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v206 : Nat := CFSG.KD.Fi24Cp.KV1 94
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l207 : List Nat := [CFSG.KD.Fi24Cp.Pc.v203, CFSG.KD.Fi24Cp.Pc.v204, CFSG.KD.Fi24Cp.Pc.v205, CFSG.KD.Fi24Cp.Pc.v206]
theorem CFSG.KD.Fi24Cp.Pc.p205 : Nat.beq (runC AR SD 203 (ckL CFSG.KD.Fi24Cp.Pc.l207) 2 205 CFSG.KD.Fi24Cp.Pc.l205) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v207 : Nat := CFSG.KD.Fi24Cp.KV1 95
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v208 : Nat := CFSG.KD.Fi24Cp.KV1 96
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l209 : List Nat := [CFSG.KD.Fi24Cp.Pc.v203, CFSG.KD.Fi24Cp.Pc.v204, CFSG.KD.Fi24Cp.Pc.v205, CFSG.KD.Fi24Cp.Pc.v206, CFSG.KD.Fi24Cp.Pc.v207, CFSG.KD.Fi24Cp.Pc.v208]
theorem CFSG.KD.Fi24Cp.Pc.p207 : Nat.beq (runC AR SD 203 (ckL CFSG.KD.Fi24Cp.Pc.l209) 2 207 CFSG.KD.Fi24Cp.Pc.l207) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v209 : Nat := CFSG.KD.Fi24Cp.KV1 97
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v210 : Nat := CFSG.KD.Fi24Cp.KV1 98
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l211 : List Nat := [CFSG.KD.Fi24Cp.Pc.v203, CFSG.KD.Fi24Cp.Pc.v204, CFSG.KD.Fi24Cp.Pc.v205, CFSG.KD.Fi24Cp.Pc.v206, CFSG.KD.Fi24Cp.Pc.v207, CFSG.KD.Fi24Cp.Pc.v208, CFSG.KD.Fi24Cp.Pc.v209, CFSG.KD.Fi24Cp.Pc.v210]
theorem CFSG.KD.Fi24Cp.Pc.p209 : Nat.beq (runC AR SD 203 (ckL CFSG.KD.Fi24Cp.Pc.l211) 2 209 CFSG.KD.Fi24Cp.Pc.l209) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v211 : Nat := CFSG.KD.Fi24Cp.KV1 99
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v212 : Nat := CFSG.KD.Fi24Cp.KV1 100
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l213 : List Nat := [CFSG.KD.Fi24Cp.Pc.v203, CFSG.KD.Fi24Cp.Pc.v204, CFSG.KD.Fi24Cp.Pc.v205, CFSG.KD.Fi24Cp.Pc.v206, CFSG.KD.Fi24Cp.Pc.v207, CFSG.KD.Fi24Cp.Pc.v208, CFSG.KD.Fi24Cp.Pc.v209, CFSG.KD.Fi24Cp.Pc.v210, CFSG.KD.Fi24Cp.Pc.v211, CFSG.KD.Fi24Cp.Pc.v212]
theorem CFSG.KD.Fi24Cp.Pc.p211 : Nat.beq (runC AR SD 203 (ckL CFSG.KD.Fi24Cp.Pc.l213) 2 211 CFSG.KD.Fi24Cp.Pc.l211) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v213 : Nat := CFSG.KD.Fi24Cp.KV1 101
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v214 : Nat := CFSG.KD.Fi24Cp.KV1 102
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l215 : List Nat := [CFSG.KD.Fi24Cp.Pc.v203, CFSG.KD.Fi24Cp.Pc.v204, CFSG.KD.Fi24Cp.Pc.v205, CFSG.KD.Fi24Cp.Pc.v206, CFSG.KD.Fi24Cp.Pc.v207, CFSG.KD.Fi24Cp.Pc.v208, CFSG.KD.Fi24Cp.Pc.v209, CFSG.KD.Fi24Cp.Pc.v210, CFSG.KD.Fi24Cp.Pc.v211, CFSG.KD.Fi24Cp.Pc.v212, CFSG.KD.Fi24Cp.Pc.v213, CFSG.KD.Fi24Cp.Pc.v214]
theorem CFSG.KD.Fi24Cp.Pc.p213 : Nat.beq (runC AR SD 203 (ckL CFSG.KD.Fi24Cp.Pc.l215) 2 213 CFSG.KD.Fi24Cp.Pc.l213) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a215_1 : Nat := CFSG.KD.Fi24Cp.KV1 103
theorem CFSG.KD.Fi24Cp.Pc.q215_1 : Nat.beq (powTop AR.mul (getV AR SD 203 CFSG.KD.Fi24Cp.Pc.l215 (SD.na.getD 215 0)) (SD.nk.getD 215 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a215_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v215 : Nat := CFSG.KD.Fi24Cp.KV1 104
theorem CFSG.KD.Fi24Cp.Pc.r215 : Nat.beq (powR AR.mul AR.one (getV AR SD 203 CFSG.KD.Fi24Cp.Pc.l215 (SD.na.getD 215 0)) (SD.nk.getD 215 1) 1 CFSG.KD.Fi24Cp.Pc.a215_1 true) CFSG.KD.Fi24Cp.Pc.v215 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l216 : List Nat := [CFSG.KD.Fi24Cp.Pc.v203, CFSG.KD.Fi24Cp.Pc.v204, CFSG.KD.Fi24Cp.Pc.v205, CFSG.KD.Fi24Cp.Pc.v206, CFSG.KD.Fi24Cp.Pc.v207, CFSG.KD.Fi24Cp.Pc.v208, CFSG.KD.Fi24Cp.Pc.v209, CFSG.KD.Fi24Cp.Pc.v210, CFSG.KD.Fi24Cp.Pc.v211, CFSG.KD.Fi24Cp.Pc.v212, CFSG.KD.Fi24Cp.Pc.v213, CFSG.KD.Fi24Cp.Pc.v214, CFSG.KD.Fi24Cp.Pc.v215]
theorem CFSG.KD.Fi24Cp.Pc.f17 : Nat.beq (runC AR SD 203 (finC AR SD (nat_lit 17) 203 216) 0 216 CFSG.KD.Fi24Cp.Pc.l216) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk17 : chk (nat_lit 17) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 17) (lo := 203) (hi := 216) (m := 13) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 13) (m2 := 11) (j2 := 205) CFSG.KD.Fi24Cp.Pc.p203 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 207) CFSG.KD.Fi24Cp.Pc.p205 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 209) CFSG.KD.Fi24Cp.Pc.p207 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 211) CFSG.KD.Fi24Cp.Pc.p209 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 213) CFSG.KD.Fi24Cp.Pc.p211 rfl rfl).trans ((runC_seq (m := 3) (m2 := 1) (j2 := 215) CFSG.KD.Fi24Cp.Pc.p213 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 216) (Lr := CFSG.KD.Fi24Cp.Pc.l216) ((nodeV_pow (R := AR) (D := SD) (lo := 203) (L := CFSG.KD.Fi24Cp.Pc.l215) (j := 215) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 203 CFSG.KD.Fi24Cp.Pc.l215 (SD.na.getD 215 0)) (SD.nk.getD 215 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q215_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r215)))) (by quickRfl) rfl rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f17

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v216 : Nat := CFSG.KD.Fi24Cp.KV1 105
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l217 : List Nat := [CFSG.KD.Fi24Cp.Pc.v216]
theorem CFSG.KD.Fi24Cp.Pc.p216 : Nat.beq (runC AR SD 216 (ckL CFSG.KD.Fi24Cp.Pc.l217) 1 216 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a217_3 : Nat := CFSG.KD.Fi24Cp.KV1 106
theorem CFSG.KD.Fi24Cp.Pc.q217_3 : Nat.beq (powTop AR.mul (getV AR SD 216 CFSG.KD.Fi24Cp.Pc.l217 (SD.na.getD 217 0)) (SD.nk.getD 217 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a217_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a217_2 : Nat := CFSG.KD.Fi24Cp.KV1 107
theorem CFSG.KD.Fi24Cp.Pc.q217_2 : Nat.beq (powTop AR.mul (getV AR SD 216 CFSG.KD.Fi24Cp.Pc.l217 (SD.na.getD 217 0)) (SD.nk.getD 217 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a217_2) 1 CFSG.KD.Fi24Cp.Pc.a217_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a217_1 : Nat := CFSG.KD.Fi24Cp.KV1 108
theorem CFSG.KD.Fi24Cp.Pc.q217_1 : Nat.beq (powTop AR.mul (getV AR SD 216 CFSG.KD.Fi24Cp.Pc.l217 (SD.na.getD 217 0)) (SD.nk.getD 217 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a217_1) 1 CFSG.KD.Fi24Cp.Pc.a217_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v217 : Nat := CFSG.KD.Fi24Cp.KV1 109
theorem CFSG.KD.Fi24Cp.Pc.r217 : Nat.beq (powR AR.mul AR.one (getV AR SD 216 CFSG.KD.Fi24Cp.Pc.l217 (SD.na.getD 217 0)) (SD.nk.getD 217 1) 1 CFSG.KD.Fi24Cp.Pc.a217_1 true) CFSG.KD.Fi24Cp.Pc.v217 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v218 : Nat := CFSG.KD.Fi24Cp.KV1 110
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v219 : Nat := CFSG.KD.Fi24Cp.KV1 111
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l218 : List Nat := [CFSG.KD.Fi24Cp.Pc.v216, CFSG.KD.Fi24Cp.Pc.v217]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l220 : List Nat := [CFSG.KD.Fi24Cp.Pc.v216, CFSG.KD.Fi24Cp.Pc.v217, CFSG.KD.Fi24Cp.Pc.v218, CFSG.KD.Fi24Cp.Pc.v219]
theorem CFSG.KD.Fi24Cp.Pc.p218 : Nat.beq (runC AR SD 216 (ckL CFSG.KD.Fi24Cp.Pc.l220) 2 218 CFSG.KD.Fi24Cp.Pc.l218) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v220 : Nat := CFSG.KD.Fi24Cp.KV1 112
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l221 : List Nat := [CFSG.KD.Fi24Cp.Pc.v216, CFSG.KD.Fi24Cp.Pc.v217, CFSG.KD.Fi24Cp.Pc.v218, CFSG.KD.Fi24Cp.Pc.v219, CFSG.KD.Fi24Cp.Pc.v220]
theorem CFSG.KD.Fi24Cp.Pc.p220 : Nat.beq (runC AR SD 216 (ckL CFSG.KD.Fi24Cp.Pc.l221) 1 220 CFSG.KD.Fi24Cp.Pc.l220) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a221_1 : Nat := CFSG.KD.Fi24Cp.KV1 113
theorem CFSG.KD.Fi24Cp.Pc.q221_1 : Nat.beq (powTop AR.mul (getV AR SD 216 CFSG.KD.Fi24Cp.Pc.l221 (SD.na.getD 221 0)) (SD.nk.getD 221 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a221_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v221 : Nat := CFSG.KD.Fi24Cp.KV1 114
theorem CFSG.KD.Fi24Cp.Pc.r221 : Nat.beq (powR AR.mul AR.one (getV AR SD 216 CFSG.KD.Fi24Cp.Pc.l221 (SD.na.getD 221 0)) (SD.nk.getD 221 1) 1 CFSG.KD.Fi24Cp.Pc.a221_1 true) CFSG.KD.Fi24Cp.Pc.v221 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v222 : Nat := CFSG.KD.Fi24Cp.KV1 115
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v223 : Nat := CFSG.KD.Fi24Cp.KV1 116
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l222 : List Nat := [CFSG.KD.Fi24Cp.Pc.v216, CFSG.KD.Fi24Cp.Pc.v217, CFSG.KD.Fi24Cp.Pc.v218, CFSG.KD.Fi24Cp.Pc.v219, CFSG.KD.Fi24Cp.Pc.v220, CFSG.KD.Fi24Cp.Pc.v221]
theorem CFSG.KD.Fi24Cp.Pc.f18 : Nat.beq (runC AR SD 216 (finC AR SD (nat_lit 18) 216 224) 2 222 CFSG.KD.Fi24Cp.Pc.l222) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk18 : chk (nat_lit 18) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 18) (lo := 216) (hi := 224) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 7) (j2 := 217) CFSG.KD.Fi24Cp.Pc.p216 rfl rfl).trans ((runC_node (m := 7) (m2 := 6) (j2 := 218) (Lr := CFSG.KD.Fi24Cp.Pc.l218) ((nodeV_pow (R := AR) (D := SD) (lo := 216) (L := CFSG.KD.Fi24Cp.Pc.l217) (j := 217) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 216 CFSG.KD.Fi24Cp.Pc.l217 (SD.na.getD 217 0)) (SD.nk.getD 217 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q217_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q217_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q217_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r217)))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 220) CFSG.KD.Fi24Cp.Pc.p218 rfl rfl).trans ((runC_seq (m := 4) (m2 := 3) (j2 := 221) CFSG.KD.Fi24Cp.Pc.p220 rfl rfl).trans (runC_node (m := 3) (m2 := 2) (j2 := 222) (Lr := CFSG.KD.Fi24Cp.Pc.l222) ((nodeV_pow (R := AR) (D := SD) (lo := 216) (L := CFSG.KD.Fi24Cp.Pc.l221) (j := 221) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 216 CFSG.KD.Fi24Cp.Pc.l221 (SD.na.getD 221 0)) (SD.nk.getD 221 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q221_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r221)))) (by quickRfl) rfl rfl rfl))))))).trans CFSG.KD.Fi24Cp.Pc.f18

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a224_1 : Nat := CFSG.KD.Fi24Cp.KV1 117
theorem CFSG.KD.Fi24Cp.Pc.q224_1 : Nat.beq (powTop AR.mul (getV AR SD 224 [] (SD.na.getD 224 0)) (SD.nk.getD 224 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a224_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v224 : Nat := CFSG.KD.Fi24Cp.KV1 118
theorem CFSG.KD.Fi24Cp.Pc.r224 : Nat.beq (powR AR.mul AR.one (getV AR SD 224 [] (SD.na.getD 224 0)) (SD.nk.getD 224 1) 1 CFSG.KD.Fi24Cp.Pc.a224_1 true) CFSG.KD.Fi24Cp.Pc.v224 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v225 : Nat := CFSG.KD.Fi24Cp.KV1 119
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v226 : Nat := CFSG.KD.Fi24Cp.KV1 120
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l225 : List Nat := [CFSG.KD.Fi24Cp.Pc.v224]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l227 : List Nat := [CFSG.KD.Fi24Cp.Pc.v224, CFSG.KD.Fi24Cp.Pc.v225, CFSG.KD.Fi24Cp.Pc.v226]
theorem CFSG.KD.Fi24Cp.Pc.p225 : Nat.beq (runC AR SD 224 (ckL CFSG.KD.Fi24Cp.Pc.l227) 2 225 CFSG.KD.Fi24Cp.Pc.l225) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v227 : Nat := CFSG.KD.Fi24Cp.KV1 121
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v228 : Nat := CFSG.KD.Fi24Cp.KV1 122
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l229 : List Nat := [CFSG.KD.Fi24Cp.Pc.v224, CFSG.KD.Fi24Cp.Pc.v225, CFSG.KD.Fi24Cp.Pc.v226, CFSG.KD.Fi24Cp.Pc.v227, CFSG.KD.Fi24Cp.Pc.v228]
theorem CFSG.KD.Fi24Cp.Pc.p227 : Nat.beq (runC AR SD 224 (ckL CFSG.KD.Fi24Cp.Pc.l229) 2 227 CFSG.KD.Fi24Cp.Pc.l227) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v229 : Nat := CFSG.KD.Fi24Cp.KV1 123
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v230 : Nat := CFSG.KD.Fi24Cp.KV1 124
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l231 : List Nat := [CFSG.KD.Fi24Cp.Pc.v224, CFSG.KD.Fi24Cp.Pc.v225, CFSG.KD.Fi24Cp.Pc.v226, CFSG.KD.Fi24Cp.Pc.v227, CFSG.KD.Fi24Cp.Pc.v228, CFSG.KD.Fi24Cp.Pc.v229, CFSG.KD.Fi24Cp.Pc.v230]
theorem CFSG.KD.Fi24Cp.Pc.p229 : Nat.beq (runC AR SD 224 (ckL CFSG.KD.Fi24Cp.Pc.l231) 2 229 CFSG.KD.Fi24Cp.Pc.l229) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v231 : Nat := CFSG.KD.Fi24Cp.KV1 125
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v232 : Nat := CFSG.KD.Fi24Cp.KV1 126
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l233 : List Nat := [CFSG.KD.Fi24Cp.Pc.v224, CFSG.KD.Fi24Cp.Pc.v225, CFSG.KD.Fi24Cp.Pc.v226, CFSG.KD.Fi24Cp.Pc.v227, CFSG.KD.Fi24Cp.Pc.v228, CFSG.KD.Fi24Cp.Pc.v229, CFSG.KD.Fi24Cp.Pc.v230, CFSG.KD.Fi24Cp.Pc.v231, CFSG.KD.Fi24Cp.Pc.v232]
theorem CFSG.KD.Fi24Cp.Pc.p231 : Nat.beq (runC AR SD 224 (ckL CFSG.KD.Fi24Cp.Pc.l233) 2 231 CFSG.KD.Fi24Cp.Pc.l231) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v233 : Nat := CFSG.KD.Fi24Cp.KV1 127
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v234 : Nat := CFSG.KD.Fi24Cp.KV1 128
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l235 : List Nat := [CFSG.KD.Fi24Cp.Pc.v224, CFSG.KD.Fi24Cp.Pc.v225, CFSG.KD.Fi24Cp.Pc.v226, CFSG.KD.Fi24Cp.Pc.v227, CFSG.KD.Fi24Cp.Pc.v228, CFSG.KD.Fi24Cp.Pc.v229, CFSG.KD.Fi24Cp.Pc.v230, CFSG.KD.Fi24Cp.Pc.v231, CFSG.KD.Fi24Cp.Pc.v232, CFSG.KD.Fi24Cp.Pc.v233, CFSG.KD.Fi24Cp.Pc.v234]
theorem CFSG.KD.Fi24Cp.Pc.p233 : Nat.beq (runC AR SD 224 (ckL CFSG.KD.Fi24Cp.Pc.l235) 2 233 CFSG.KD.Fi24Cp.Pc.l233) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v235 : Nat := CFSG.KD.Fi24Cp.KV1 129
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v236 : Nat := CFSG.KD.Fi24Cp.KV1 130
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l237 : List Nat := [CFSG.KD.Fi24Cp.Pc.v224, CFSG.KD.Fi24Cp.Pc.v225, CFSG.KD.Fi24Cp.Pc.v226, CFSG.KD.Fi24Cp.Pc.v227, CFSG.KD.Fi24Cp.Pc.v228, CFSG.KD.Fi24Cp.Pc.v229, CFSG.KD.Fi24Cp.Pc.v230, CFSG.KD.Fi24Cp.Pc.v231, CFSG.KD.Fi24Cp.Pc.v232, CFSG.KD.Fi24Cp.Pc.v233, CFSG.KD.Fi24Cp.Pc.v234, CFSG.KD.Fi24Cp.Pc.v235, CFSG.KD.Fi24Cp.Pc.v236]
theorem CFSG.KD.Fi24Cp.Pc.p235 : Nat.beq (runC AR SD 224 (ckL CFSG.KD.Fi24Cp.Pc.l237) 2 235 CFSG.KD.Fi24Cp.Pc.l235) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v237 : Nat := CFSG.KD.Fi24Cp.KV1 131
theorem CFSG.KD.Fi24Cp.Pc.f19 : Nat.beq (runC AR SD 224 (finC AR SD (nat_lit 19) 224 238) 1 237 CFSG.KD.Fi24Cp.Pc.l237) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk19 : chk (nat_lit 19) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 19) (lo := 224) (hi := 238) (m := 14) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 14) (m2 := 13) (j2 := 225) (Lr := CFSG.KD.Fi24Cp.Pc.l225) ((nodeV_pow (R := AR) (D := SD) (lo := 224) (L := []) (j := 224) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 224 [] (SD.na.getD 224 0)) (SD.nk.getD 224 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q224_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r224)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 227) CFSG.KD.Fi24Cp.Pc.p225 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 229) CFSG.KD.Fi24Cp.Pc.p227 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 231) CFSG.KD.Fi24Cp.Pc.p229 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 233) CFSG.KD.Fi24Cp.Pc.p231 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 235) CFSG.KD.Fi24Cp.Pc.p233 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 237) CFSG.KD.Fi24Cp.Pc.p235 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f19

end
