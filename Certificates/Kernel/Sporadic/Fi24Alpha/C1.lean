module

public import Certificates.Kernel.Sporadic.Fi24Alpha.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Alpha KV1 "Certificates/Kernel/Sporadic/Fi24Alpha/data/v1.bin" 152491 4 19823830 17900675682382878402

public section

open CFSG.KD.Fi24Alpha CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v128 : Nat := CFSG.KD.Fi24Alpha.KV1 0
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v129 : Nat := CFSG.KD.Fi24Alpha.KV1 1
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l130 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v128, CFSG.KD.Fi24Alpha.Pc.v129]
theorem CFSG.KD.Fi24Alpha.Pc.p128 : Nat.beq (runC AR SD 128 (ckL CFSG.KD.Fi24Alpha.Pc.l130) 2 128 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v130 : Nat := CFSG.KD.Fi24Alpha.KV1 2
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v131 : Nat := CFSG.KD.Fi24Alpha.KV1 3
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l132 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v128, CFSG.KD.Fi24Alpha.Pc.v129, CFSG.KD.Fi24Alpha.Pc.v130, CFSG.KD.Fi24Alpha.Pc.v131]
theorem CFSG.KD.Fi24Alpha.Pc.p130 : Nat.beq (runC AR SD 128 (ckL CFSG.KD.Fi24Alpha.Pc.l132) 2 130 CFSG.KD.Fi24Alpha.Pc.l130) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a132_4 : Nat := CFSG.KD.Fi24Alpha.KV1 4
theorem CFSG.KD.Fi24Alpha.Pc.q132_4 : Nat.beq (powTop AR.mul (getV AR SD 128 CFSG.KD.Fi24Alpha.Pc.l132 (SD.na.getD 132 0)) (SD.nk.getD 132 1) 4 (ckP CFSG.KD.Fi24Alpha.Pc.a132_4) 12 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a132_3 : Nat := CFSG.KD.Fi24Alpha.KV1 5
theorem CFSG.KD.Fi24Alpha.Pc.q132_3 : Nat.beq (powTop AR.mul (getV AR SD 128 CFSG.KD.Fi24Alpha.Pc.l132 (SD.na.getD 132 0)) (SD.nk.getD 132 1) 3 (ckP CFSG.KD.Fi24Alpha.Pc.a132_3) 1 CFSG.KD.Fi24Alpha.Pc.a132_4 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a132_1 : Nat := CFSG.KD.Fi24Alpha.KV1 6
theorem CFSG.KD.Fi24Alpha.Pc.q132_1 : Nat.beq (powTop AR.mul (getV AR SD 128 CFSG.KD.Fi24Alpha.Pc.l132 (SD.na.getD 132 0)) (SD.nk.getD 132 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a132_1) 2 CFSG.KD.Fi24Alpha.Pc.a132_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v132 : Nat := CFSG.KD.Fi24Alpha.KV1 7
theorem CFSG.KD.Fi24Alpha.Pc.r132 : Nat.beq (powR AR.mul AR.one (getV AR SD 128 CFSG.KD.Fi24Alpha.Pc.l132 (SD.na.getD 132 0)) (SD.nk.getD 132 1) 1 CFSG.KD.Fi24Alpha.Pc.a132_1 true) CFSG.KD.Fi24Alpha.Pc.v132 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v133 : Nat := CFSG.KD.Fi24Alpha.KV1 8
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v134 : Nat := CFSG.KD.Fi24Alpha.KV1 9
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l133 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v128, CFSG.KD.Fi24Alpha.Pc.v129, CFSG.KD.Fi24Alpha.Pc.v130, CFSG.KD.Fi24Alpha.Pc.v131, CFSG.KD.Fi24Alpha.Pc.v132]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l135 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v128, CFSG.KD.Fi24Alpha.Pc.v129, CFSG.KD.Fi24Alpha.Pc.v130, CFSG.KD.Fi24Alpha.Pc.v131, CFSG.KD.Fi24Alpha.Pc.v132, CFSG.KD.Fi24Alpha.Pc.v133, CFSG.KD.Fi24Alpha.Pc.v134]
theorem CFSG.KD.Fi24Alpha.Pc.p133 : Nat.beq (runC AR SD 128 (ckL CFSG.KD.Fi24Alpha.Pc.l135) 2 133 CFSG.KD.Fi24Alpha.Pc.l133) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v135 : Nat := CFSG.KD.Fi24Alpha.KV1 10
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v136 : Nat := CFSG.KD.Fi24Alpha.KV1 11
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l137 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v128, CFSG.KD.Fi24Alpha.Pc.v129, CFSG.KD.Fi24Alpha.Pc.v130, CFSG.KD.Fi24Alpha.Pc.v131, CFSG.KD.Fi24Alpha.Pc.v132, CFSG.KD.Fi24Alpha.Pc.v133, CFSG.KD.Fi24Alpha.Pc.v134, CFSG.KD.Fi24Alpha.Pc.v135, CFSG.KD.Fi24Alpha.Pc.v136]
theorem CFSG.KD.Fi24Alpha.Pc.p135 : Nat.beq (runC AR SD 128 (ckL CFSG.KD.Fi24Alpha.Pc.l137) 2 135 CFSG.KD.Fi24Alpha.Pc.l135) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v137 : Nat := CFSG.KD.Fi24Alpha.KV1 12
theorem CFSG.KD.Fi24Alpha.Pc.f10 : Nat.beq (runC AR SD 128 (finC AR SD (nat_lit 10) 128 138) 1 137 CFSG.KD.Fi24Alpha.Pc.l137) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk10 : chk (nat_lit 10) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 10) (lo := 128) (hi := 138) (m := 10) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 10) (m2 := 8) (j2 := 130) CFSG.KD.Fi24Alpha.Pc.p128 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 132) CFSG.KD.Fi24Alpha.Pc.p130 rfl rfl).trans ((runC_node (m := 6) (m2 := 5) (j2 := 133) (Lr := CFSG.KD.Fi24Alpha.Pc.l133) ((nodeV_pow (R := AR) (D := SD) (lo := 128) (L := CFSG.KD.Fi24Alpha.Pc.l132) (j := 132) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 128 CFSG.KD.Fi24Alpha.Pc.l132 (SD.na.getD 132 0)) (SD.nk.getD 132 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q132_4 rfl).trans ((powR_seq (n := 4) CFSG.KD.Fi24Alpha.Pc.q132_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Alpha.Pc.q132_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r132)))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 135) CFSG.KD.Fi24Alpha.Pc.p133 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 137) CFSG.KD.Fi24Alpha.Pc.p135 rfl rfl))))))).trans CFSG.KD.Fi24Alpha.Pc.f10

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v138 : Nat := CFSG.KD.Fi24Alpha.KV1 13
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v139 : Nat := CFSG.KD.Fi24Alpha.KV1 14
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l140 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v138, CFSG.KD.Fi24Alpha.Pc.v139]
theorem CFSG.KD.Fi24Alpha.Pc.p138 : Nat.beq (runC AR SD 138 (ckL CFSG.KD.Fi24Alpha.Pc.l140) 2 138 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v140 : Nat := CFSG.KD.Fi24Alpha.KV1 15
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v141 : Nat := CFSG.KD.Fi24Alpha.KV1 16
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l142 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v138, CFSG.KD.Fi24Alpha.Pc.v139, CFSG.KD.Fi24Alpha.Pc.v140, CFSG.KD.Fi24Alpha.Pc.v141]
theorem CFSG.KD.Fi24Alpha.Pc.p140 : Nat.beq (runC AR SD 138 (ckL CFSG.KD.Fi24Alpha.Pc.l142) 2 140 CFSG.KD.Fi24Alpha.Pc.l140) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v142 : Nat := CFSG.KD.Fi24Alpha.KV1 17
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v143 : Nat := CFSG.KD.Fi24Alpha.KV1 18
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l144 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v138, CFSG.KD.Fi24Alpha.Pc.v139, CFSG.KD.Fi24Alpha.Pc.v140, CFSG.KD.Fi24Alpha.Pc.v141, CFSG.KD.Fi24Alpha.Pc.v142, CFSG.KD.Fi24Alpha.Pc.v143]
theorem CFSG.KD.Fi24Alpha.Pc.p142 : Nat.beq (runC AR SD 138 (ckL CFSG.KD.Fi24Alpha.Pc.l144) 2 142 CFSG.KD.Fi24Alpha.Pc.l142) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v144 : Nat := CFSG.KD.Fi24Alpha.KV1 19
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v145 : Nat := CFSG.KD.Fi24Alpha.KV1 20
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l146 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v138, CFSG.KD.Fi24Alpha.Pc.v139, CFSG.KD.Fi24Alpha.Pc.v140, CFSG.KD.Fi24Alpha.Pc.v141, CFSG.KD.Fi24Alpha.Pc.v142, CFSG.KD.Fi24Alpha.Pc.v143, CFSG.KD.Fi24Alpha.Pc.v144, CFSG.KD.Fi24Alpha.Pc.v145]
theorem CFSG.KD.Fi24Alpha.Pc.p144 : Nat.beq (runC AR SD 138 (ckL CFSG.KD.Fi24Alpha.Pc.l146) 2 144 CFSG.KD.Fi24Alpha.Pc.l144) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v146 : Nat := CFSG.KD.Fi24Alpha.KV1 21
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v147 : Nat := CFSG.KD.Fi24Alpha.KV1 22
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l148 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v138, CFSG.KD.Fi24Alpha.Pc.v139, CFSG.KD.Fi24Alpha.Pc.v140, CFSG.KD.Fi24Alpha.Pc.v141, CFSG.KD.Fi24Alpha.Pc.v142, CFSG.KD.Fi24Alpha.Pc.v143, CFSG.KD.Fi24Alpha.Pc.v144, CFSG.KD.Fi24Alpha.Pc.v145, CFSG.KD.Fi24Alpha.Pc.v146, CFSG.KD.Fi24Alpha.Pc.v147]
theorem CFSG.KD.Fi24Alpha.Pc.p146 : Nat.beq (runC AR SD 138 (ckL CFSG.KD.Fi24Alpha.Pc.l148) 2 146 CFSG.KD.Fi24Alpha.Pc.l146) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v148 : Nat := CFSG.KD.Fi24Alpha.KV1 23
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v149 : Nat := CFSG.KD.Fi24Alpha.KV1 24
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l150 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v138, CFSG.KD.Fi24Alpha.Pc.v139, CFSG.KD.Fi24Alpha.Pc.v140, CFSG.KD.Fi24Alpha.Pc.v141, CFSG.KD.Fi24Alpha.Pc.v142, CFSG.KD.Fi24Alpha.Pc.v143, CFSG.KD.Fi24Alpha.Pc.v144, CFSG.KD.Fi24Alpha.Pc.v145, CFSG.KD.Fi24Alpha.Pc.v146, CFSG.KD.Fi24Alpha.Pc.v147, CFSG.KD.Fi24Alpha.Pc.v148, CFSG.KD.Fi24Alpha.Pc.v149]
theorem CFSG.KD.Fi24Alpha.Pc.p148 : Nat.beq (runC AR SD 138 (ckL CFSG.KD.Fi24Alpha.Pc.l150) 2 148 CFSG.KD.Fi24Alpha.Pc.l148) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v150 : Nat := CFSG.KD.Fi24Alpha.KV1 25
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v151 : Nat := CFSG.KD.Fi24Alpha.KV1 26
theorem CFSG.KD.Fi24Alpha.Pc.f11 : Nat.beq (runC AR SD 138 (finC AR SD (nat_lit 11) 138 152) 2 150 CFSG.KD.Fi24Alpha.Pc.l150) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk11 : chk (nat_lit 11) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 11) (lo := 138) (hi := 152) (m := 14) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 14) (m2 := 12) (j2 := 140) CFSG.KD.Fi24Alpha.Pc.p138 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 142) CFSG.KD.Fi24Alpha.Pc.p140 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 144) CFSG.KD.Fi24Alpha.Pc.p142 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 146) CFSG.KD.Fi24Alpha.Pc.p144 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 148) CFSG.KD.Fi24Alpha.Pc.p146 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 150) CFSG.KD.Fi24Alpha.Pc.p148 rfl rfl)))))))).trans CFSG.KD.Fi24Alpha.Pc.f11

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a152_4 : Nat := CFSG.KD.Fi24Alpha.KV1 27
theorem CFSG.KD.Fi24Alpha.Pc.q152_4 : Nat.beq (powTop AR.mul (getV AR SD 152 [] (SD.na.getD 152 0)) (SD.nk.getD 152 1) 4 (ckP CFSG.KD.Fi24Alpha.Pc.a152_4) 12 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a152_3 : Nat := CFSG.KD.Fi24Alpha.KV1 28
theorem CFSG.KD.Fi24Alpha.Pc.q152_3 : Nat.beq (powTop AR.mul (getV AR SD 152 [] (SD.na.getD 152 0)) (SD.nk.getD 152 1) 3 (ckP CFSG.KD.Fi24Alpha.Pc.a152_3) 1 CFSG.KD.Fi24Alpha.Pc.a152_4 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a152_1 : Nat := CFSG.KD.Fi24Alpha.KV1 29
theorem CFSG.KD.Fi24Alpha.Pc.q152_1 : Nat.beq (powTop AR.mul (getV AR SD 152 [] (SD.na.getD 152 0)) (SD.nk.getD 152 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a152_1) 2 CFSG.KD.Fi24Alpha.Pc.a152_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v152 : Nat := CFSG.KD.Fi24Alpha.KV1 30
theorem CFSG.KD.Fi24Alpha.Pc.r152 : Nat.beq (powR AR.mul AR.one (getV AR SD 152 [] (SD.na.getD 152 0)) (SD.nk.getD 152 1) 1 CFSG.KD.Fi24Alpha.Pc.a152_1 true) CFSG.KD.Fi24Alpha.Pc.v152 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v153 : Nat := CFSG.KD.Fi24Alpha.KV1 31
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v154 : Nat := CFSG.KD.Fi24Alpha.KV1 32
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l153 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v152]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l155 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v152, CFSG.KD.Fi24Alpha.Pc.v153, CFSG.KD.Fi24Alpha.Pc.v154]
theorem CFSG.KD.Fi24Alpha.Pc.p153 : Nat.beq (runC AR SD 152 (ckL CFSG.KD.Fi24Alpha.Pc.l155) 2 153 CFSG.KD.Fi24Alpha.Pc.l153) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v155 : Nat := CFSG.KD.Fi24Alpha.KV1 33
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v156 : Nat := CFSG.KD.Fi24Alpha.KV1 34
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l157 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v152, CFSG.KD.Fi24Alpha.Pc.v153, CFSG.KD.Fi24Alpha.Pc.v154, CFSG.KD.Fi24Alpha.Pc.v155, CFSG.KD.Fi24Alpha.Pc.v156]
theorem CFSG.KD.Fi24Alpha.Pc.p155 : Nat.beq (runC AR SD 152 (ckL CFSG.KD.Fi24Alpha.Pc.l157) 2 155 CFSG.KD.Fi24Alpha.Pc.l155) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v157 : Nat := CFSG.KD.Fi24Alpha.KV1 35
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v158 : Nat := CFSG.KD.Fi24Alpha.KV1 36
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l159 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v152, CFSG.KD.Fi24Alpha.Pc.v153, CFSG.KD.Fi24Alpha.Pc.v154, CFSG.KD.Fi24Alpha.Pc.v155, CFSG.KD.Fi24Alpha.Pc.v156, CFSG.KD.Fi24Alpha.Pc.v157, CFSG.KD.Fi24Alpha.Pc.v158]
theorem CFSG.KD.Fi24Alpha.Pc.p157 : Nat.beq (runC AR SD 152 (ckL CFSG.KD.Fi24Alpha.Pc.l159) 2 157 CFSG.KD.Fi24Alpha.Pc.l157) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a159_1 : Nat := CFSG.KD.Fi24Alpha.KV1 37
theorem CFSG.KD.Fi24Alpha.Pc.q159_1 : Nat.beq (powTop AR.mul (getV AR SD 152 CFSG.KD.Fi24Alpha.Pc.l159 (SD.na.getD 159 0)) (SD.nk.getD 159 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a159_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v159 : Nat := CFSG.KD.Fi24Alpha.KV1 38
theorem CFSG.KD.Fi24Alpha.Pc.r159 : Nat.beq (powR AR.mul AR.one (getV AR SD 152 CFSG.KD.Fi24Alpha.Pc.l159 (SD.na.getD 159 0)) (SD.nk.getD 159 1) 1 CFSG.KD.Fi24Alpha.Pc.a159_1 true) CFSG.KD.Fi24Alpha.Pc.v159 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l160 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v152, CFSG.KD.Fi24Alpha.Pc.v153, CFSG.KD.Fi24Alpha.Pc.v154, CFSG.KD.Fi24Alpha.Pc.v155, CFSG.KD.Fi24Alpha.Pc.v156, CFSG.KD.Fi24Alpha.Pc.v157, CFSG.KD.Fi24Alpha.Pc.v158, CFSG.KD.Fi24Alpha.Pc.v159]
theorem CFSG.KD.Fi24Alpha.Pc.f12 : Nat.beq (runC AR SD 152 (finC AR SD (nat_lit 12) 152 160) 0 160 CFSG.KD.Fi24Alpha.Pc.l160) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk12 : chk (nat_lit 12) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 12) (lo := 152) (hi := 160) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 8) (m2 := 7) (j2 := 153) (Lr := CFSG.KD.Fi24Alpha.Pc.l153) ((nodeV_pow (R := AR) (D := SD) (lo := 152) (L := []) (j := 152) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 152 [] (SD.na.getD 152 0)) (SD.nk.getD 152 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q152_4 rfl).trans ((powR_seq (n := 4) CFSG.KD.Fi24Alpha.Pc.q152_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Alpha.Pc.q152_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r152)))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 155) CFSG.KD.Fi24Alpha.Pc.p153 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 157) CFSG.KD.Fi24Alpha.Pc.p155 rfl rfl).trans ((runC_seq (m := 3) (m2 := 1) (j2 := 159) CFSG.KD.Fi24Alpha.Pc.p157 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 160) (Lr := CFSG.KD.Fi24Alpha.Pc.l160) ((nodeV_pow (R := AR) (D := SD) (lo := 152) (L := CFSG.KD.Fi24Alpha.Pc.l159) (j := 159) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 152 CFSG.KD.Fi24Alpha.Pc.l159 (SD.na.getD 159 0)) (SD.nk.getD 159 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q159_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r159)))) (by quickRfl) rfl rfl rfl))))))).trans CFSG.KD.Fi24Alpha.Pc.f12

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v160 : Nat := CFSG.KD.Fi24Alpha.KV1 39
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v161 : Nat := CFSG.KD.Fi24Alpha.KV1 40
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l162 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v160, CFSG.KD.Fi24Alpha.Pc.v161]
theorem CFSG.KD.Fi24Alpha.Pc.p160 : Nat.beq (runC AR SD 160 (ckL CFSG.KD.Fi24Alpha.Pc.l162) 2 160 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v162 : Nat := CFSG.KD.Fi24Alpha.KV1 41
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v163 : Nat := CFSG.KD.Fi24Alpha.KV1 42
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l164 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v160, CFSG.KD.Fi24Alpha.Pc.v161, CFSG.KD.Fi24Alpha.Pc.v162, CFSG.KD.Fi24Alpha.Pc.v163]
theorem CFSG.KD.Fi24Alpha.Pc.p162 : Nat.beq (runC AR SD 160 (ckL CFSG.KD.Fi24Alpha.Pc.l164) 2 162 CFSG.KD.Fi24Alpha.Pc.l162) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v164 : Nat := CFSG.KD.Fi24Alpha.KV1 43
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v165 : Nat := CFSG.KD.Fi24Alpha.KV1 44
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l166 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v160, CFSG.KD.Fi24Alpha.Pc.v161, CFSG.KD.Fi24Alpha.Pc.v162, CFSG.KD.Fi24Alpha.Pc.v163, CFSG.KD.Fi24Alpha.Pc.v164, CFSG.KD.Fi24Alpha.Pc.v165]
theorem CFSG.KD.Fi24Alpha.Pc.p164 : Nat.beq (runC AR SD 160 (ckL CFSG.KD.Fi24Alpha.Pc.l166) 2 164 CFSG.KD.Fi24Alpha.Pc.l164) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a166_2 : Nat := CFSG.KD.Fi24Alpha.KV1 45
theorem CFSG.KD.Fi24Alpha.Pc.q166_2 : Nat.beq (powTop AR.mul (getV AR SD 160 CFSG.KD.Fi24Alpha.Pc.l166 (SD.na.getD 166 0)) (SD.nk.getD 166 1) 2 (ckP CFSG.KD.Fi24Alpha.Pc.a166_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a166_1 : Nat := CFSG.KD.Fi24Alpha.KV1 46
theorem CFSG.KD.Fi24Alpha.Pc.q166_1 : Nat.beq (powTop AR.mul (getV AR SD 160 CFSG.KD.Fi24Alpha.Pc.l166 (SD.na.getD 166 0)) (SD.nk.getD 166 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a166_1) 1 CFSG.KD.Fi24Alpha.Pc.a166_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v166 : Nat := CFSG.KD.Fi24Alpha.KV1 47
theorem CFSG.KD.Fi24Alpha.Pc.r166 : Nat.beq (powR AR.mul AR.one (getV AR SD 160 CFSG.KD.Fi24Alpha.Pc.l166 (SD.na.getD 166 0)) (SD.nk.getD 166 1) 1 CFSG.KD.Fi24Alpha.Pc.a166_1 true) CFSG.KD.Fi24Alpha.Pc.v166 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v167 : Nat := CFSG.KD.Fi24Alpha.KV1 48
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v168 : Nat := CFSG.KD.Fi24Alpha.KV1 49
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l167 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v160, CFSG.KD.Fi24Alpha.Pc.v161, CFSG.KD.Fi24Alpha.Pc.v162, CFSG.KD.Fi24Alpha.Pc.v163, CFSG.KD.Fi24Alpha.Pc.v164, CFSG.KD.Fi24Alpha.Pc.v165, CFSG.KD.Fi24Alpha.Pc.v166]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l169 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v160, CFSG.KD.Fi24Alpha.Pc.v161, CFSG.KD.Fi24Alpha.Pc.v162, CFSG.KD.Fi24Alpha.Pc.v163, CFSG.KD.Fi24Alpha.Pc.v164, CFSG.KD.Fi24Alpha.Pc.v165, CFSG.KD.Fi24Alpha.Pc.v166, CFSG.KD.Fi24Alpha.Pc.v167, CFSG.KD.Fi24Alpha.Pc.v168]
theorem CFSG.KD.Fi24Alpha.Pc.p167 : Nat.beq (runC AR SD 160 (ckL CFSG.KD.Fi24Alpha.Pc.l169) 2 167 CFSG.KD.Fi24Alpha.Pc.l167) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v169 : Nat := CFSG.KD.Fi24Alpha.KV1 50
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v170 : Nat := CFSG.KD.Fi24Alpha.KV1 51
theorem CFSG.KD.Fi24Alpha.Pc.f13 : Nat.beq (runC AR SD 160 (finC AR SD (nat_lit 13) 160 171) 2 169 CFSG.KD.Fi24Alpha.Pc.l169) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk13 : chk (nat_lit 13) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 13) (lo := 160) (hi := 171) (m := 11) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 11) (m2 := 9) (j2 := 162) CFSG.KD.Fi24Alpha.Pc.p160 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 164) CFSG.KD.Fi24Alpha.Pc.p162 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 166) CFSG.KD.Fi24Alpha.Pc.p164 rfl rfl).trans ((runC_node (m := 5) (m2 := 4) (j2 := 167) (Lr := CFSG.KD.Fi24Alpha.Pc.l167) ((nodeV_pow (R := AR) (D := SD) (lo := 160) (L := CFSG.KD.Fi24Alpha.Pc.l166) (j := 166) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 160 CFSG.KD.Fi24Alpha.Pc.l166 (SD.na.getD 166 0)) (SD.nk.getD 166 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q166_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Alpha.Pc.q166_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r166))))) (by quickRfl) rfl rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 169) CFSG.KD.Fi24Alpha.Pc.p167 rfl rfl))))))).trans CFSG.KD.Fi24Alpha.Pc.f13

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a171_3 : Nat := CFSG.KD.Fi24Alpha.KV1 52
theorem CFSG.KD.Fi24Alpha.Pc.q171_3 : Nat.beq (powTop AR.mul (getV AR SD 171 [] (SD.na.getD 171 0)) (SD.nk.getD 171 1) 3 (ckP CFSG.KD.Fi24Alpha.Pc.a171_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a171_2 : Nat := CFSG.KD.Fi24Alpha.KV1 53
theorem CFSG.KD.Fi24Alpha.Pc.q171_2 : Nat.beq (powTop AR.mul (getV AR SD 171 [] (SD.na.getD 171 0)) (SD.nk.getD 171 1) 2 (ckP CFSG.KD.Fi24Alpha.Pc.a171_2) 1 CFSG.KD.Fi24Alpha.Pc.a171_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a171_1 : Nat := CFSG.KD.Fi24Alpha.KV1 54
theorem CFSG.KD.Fi24Alpha.Pc.q171_1 : Nat.beq (powTop AR.mul (getV AR SD 171 [] (SD.na.getD 171 0)) (SD.nk.getD 171 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a171_1) 1 CFSG.KD.Fi24Alpha.Pc.a171_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v171 : Nat := CFSG.KD.Fi24Alpha.KV1 55
theorem CFSG.KD.Fi24Alpha.Pc.r171 : Nat.beq (powR AR.mul AR.one (getV AR SD 171 [] (SD.na.getD 171 0)) (SD.nk.getD 171 1) 1 CFSG.KD.Fi24Alpha.Pc.a171_1 true) CFSG.KD.Fi24Alpha.Pc.v171 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v172 : Nat := CFSG.KD.Fi24Alpha.KV1 56
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v173 : Nat := CFSG.KD.Fi24Alpha.KV1 57
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l172 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v171]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l174 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v171, CFSG.KD.Fi24Alpha.Pc.v172, CFSG.KD.Fi24Alpha.Pc.v173]
theorem CFSG.KD.Fi24Alpha.Pc.p172 : Nat.beq (runC AR SD 171 (ckL CFSG.KD.Fi24Alpha.Pc.l174) 2 172 CFSG.KD.Fi24Alpha.Pc.l172) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v174 : Nat := CFSG.KD.Fi24Alpha.KV1 58
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v175 : Nat := CFSG.KD.Fi24Alpha.KV1 59
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l176 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v171, CFSG.KD.Fi24Alpha.Pc.v172, CFSG.KD.Fi24Alpha.Pc.v173, CFSG.KD.Fi24Alpha.Pc.v174, CFSG.KD.Fi24Alpha.Pc.v175]
theorem CFSG.KD.Fi24Alpha.Pc.p174 : Nat.beq (runC AR SD 171 (ckL CFSG.KD.Fi24Alpha.Pc.l176) 2 174 CFSG.KD.Fi24Alpha.Pc.l174) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v176 : Nat := CFSG.KD.Fi24Alpha.KV1 60
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v177 : Nat := CFSG.KD.Fi24Alpha.KV1 61
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l178 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v171, CFSG.KD.Fi24Alpha.Pc.v172, CFSG.KD.Fi24Alpha.Pc.v173, CFSG.KD.Fi24Alpha.Pc.v174, CFSG.KD.Fi24Alpha.Pc.v175, CFSG.KD.Fi24Alpha.Pc.v176, CFSG.KD.Fi24Alpha.Pc.v177]
theorem CFSG.KD.Fi24Alpha.Pc.p176 : Nat.beq (runC AR SD 171 (ckL CFSG.KD.Fi24Alpha.Pc.l178) 2 176 CFSG.KD.Fi24Alpha.Pc.l176) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v178 : Nat := CFSG.KD.Fi24Alpha.KV1 62
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v179 : Nat := CFSG.KD.Fi24Alpha.KV1 63
theorem CFSG.KD.Fi24Alpha.Pc.f14 : Nat.beq (runC AR SD 171 (finC AR SD (nat_lit 14) 171 180) 2 178 CFSG.KD.Fi24Alpha.Pc.l178) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk14 : chk (nat_lit 14) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 14) (lo := 171) (hi := 180) (m := 9) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 9) (m2 := 8) (j2 := 172) (Lr := CFSG.KD.Fi24Alpha.Pc.l172) ((nodeV_pow (R := AR) (D := SD) (lo := 171) (L := []) (j := 171) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 171 [] (SD.na.getD 171 0)) (SD.nk.getD 171 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q171_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Alpha.Pc.q171_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Alpha.Pc.q171_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r171)))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 174) CFSG.KD.Fi24Alpha.Pc.p172 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 176) CFSG.KD.Fi24Alpha.Pc.p174 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 178) CFSG.KD.Fi24Alpha.Pc.p176 rfl rfl)))))).trans CFSG.KD.Fi24Alpha.Pc.f14

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v180 : Nat := CFSG.KD.Fi24Alpha.KV1 64
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v181 : Nat := CFSG.KD.Fi24Alpha.KV1 65
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l182 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v180, CFSG.KD.Fi24Alpha.Pc.v181]
theorem CFSG.KD.Fi24Alpha.Pc.p180 : Nat.beq (runC AR SD 180 (ckL CFSG.KD.Fi24Alpha.Pc.l182) 2 180 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v182 : Nat := CFSG.KD.Fi24Alpha.KV1 66
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v183 : Nat := CFSG.KD.Fi24Alpha.KV1 67
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l184 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v180, CFSG.KD.Fi24Alpha.Pc.v181, CFSG.KD.Fi24Alpha.Pc.v182, CFSG.KD.Fi24Alpha.Pc.v183]
theorem CFSG.KD.Fi24Alpha.Pc.p182 : Nat.beq (runC AR SD 180 (ckL CFSG.KD.Fi24Alpha.Pc.l184) 2 182 CFSG.KD.Fi24Alpha.Pc.l182) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v184 : Nat := CFSG.KD.Fi24Alpha.KV1 68
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v185 : Nat := CFSG.KD.Fi24Alpha.KV1 69
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l186 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v180, CFSG.KD.Fi24Alpha.Pc.v181, CFSG.KD.Fi24Alpha.Pc.v182, CFSG.KD.Fi24Alpha.Pc.v183, CFSG.KD.Fi24Alpha.Pc.v184, CFSG.KD.Fi24Alpha.Pc.v185]
theorem CFSG.KD.Fi24Alpha.Pc.p184 : Nat.beq (runC AR SD 180 (ckL CFSG.KD.Fi24Alpha.Pc.l186) 2 184 CFSG.KD.Fi24Alpha.Pc.l184) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a186_2 : Nat := CFSG.KD.Fi24Alpha.KV1 70
theorem CFSG.KD.Fi24Alpha.Pc.q186_2 : Nat.beq (powTop AR.mul (getV AR SD 180 CFSG.KD.Fi24Alpha.Pc.l186 (SD.na.getD 186 0)) (SD.nk.getD 186 1) 2 (ckP CFSG.KD.Fi24Alpha.Pc.a186_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a186_1 : Nat := CFSG.KD.Fi24Alpha.KV1 71
theorem CFSG.KD.Fi24Alpha.Pc.q186_1 : Nat.beq (powTop AR.mul (getV AR SD 180 CFSG.KD.Fi24Alpha.Pc.l186 (SD.na.getD 186 0)) (SD.nk.getD 186 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a186_1) 1 CFSG.KD.Fi24Alpha.Pc.a186_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v186 : Nat := CFSG.KD.Fi24Alpha.KV1 72
theorem CFSG.KD.Fi24Alpha.Pc.r186 : Nat.beq (powR AR.mul AR.one (getV AR SD 180 CFSG.KD.Fi24Alpha.Pc.l186 (SD.na.getD 186 0)) (SD.nk.getD 186 1) 1 CFSG.KD.Fi24Alpha.Pc.a186_1 true) CFSG.KD.Fi24Alpha.Pc.v186 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v187 : Nat := CFSG.KD.Fi24Alpha.KV1 73
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v188 : Nat := CFSG.KD.Fi24Alpha.KV1 74
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l187 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v180, CFSG.KD.Fi24Alpha.Pc.v181, CFSG.KD.Fi24Alpha.Pc.v182, CFSG.KD.Fi24Alpha.Pc.v183, CFSG.KD.Fi24Alpha.Pc.v184, CFSG.KD.Fi24Alpha.Pc.v185, CFSG.KD.Fi24Alpha.Pc.v186]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l189 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v180, CFSG.KD.Fi24Alpha.Pc.v181, CFSG.KD.Fi24Alpha.Pc.v182, CFSG.KD.Fi24Alpha.Pc.v183, CFSG.KD.Fi24Alpha.Pc.v184, CFSG.KD.Fi24Alpha.Pc.v185, CFSG.KD.Fi24Alpha.Pc.v186, CFSG.KD.Fi24Alpha.Pc.v187, CFSG.KD.Fi24Alpha.Pc.v188]
theorem CFSG.KD.Fi24Alpha.Pc.p187 : Nat.beq (runC AR SD 180 (ckL CFSG.KD.Fi24Alpha.Pc.l189) 2 187 CFSG.KD.Fi24Alpha.Pc.l187) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v189 : Nat := CFSG.KD.Fi24Alpha.KV1 75
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v190 : Nat := CFSG.KD.Fi24Alpha.KV1 76
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l191 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v180, CFSG.KD.Fi24Alpha.Pc.v181, CFSG.KD.Fi24Alpha.Pc.v182, CFSG.KD.Fi24Alpha.Pc.v183, CFSG.KD.Fi24Alpha.Pc.v184, CFSG.KD.Fi24Alpha.Pc.v185, CFSG.KD.Fi24Alpha.Pc.v186, CFSG.KD.Fi24Alpha.Pc.v187, CFSG.KD.Fi24Alpha.Pc.v188, CFSG.KD.Fi24Alpha.Pc.v189, CFSG.KD.Fi24Alpha.Pc.v190]
theorem CFSG.KD.Fi24Alpha.Pc.p189 : Nat.beq (runC AR SD 180 (ckL CFSG.KD.Fi24Alpha.Pc.l191) 2 189 CFSG.KD.Fi24Alpha.Pc.l189) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v191 : Nat := CFSG.KD.Fi24Alpha.KV1 77
theorem CFSG.KD.Fi24Alpha.Pc.f15 : Nat.beq (runC AR SD 180 (finC AR SD (nat_lit 15) 180 192) 1 191 CFSG.KD.Fi24Alpha.Pc.l191) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk15 : chk (nat_lit 15) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 15) (lo := 180) (hi := 192) (m := 12) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 12) (m2 := 10) (j2 := 182) CFSG.KD.Fi24Alpha.Pc.p180 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 184) CFSG.KD.Fi24Alpha.Pc.p182 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 186) CFSG.KD.Fi24Alpha.Pc.p184 rfl rfl).trans ((runC_node (m := 6) (m2 := 5) (j2 := 187) (Lr := CFSG.KD.Fi24Alpha.Pc.l187) ((nodeV_pow (R := AR) (D := SD) (lo := 180) (L := CFSG.KD.Fi24Alpha.Pc.l186) (j := 186) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 180 CFSG.KD.Fi24Alpha.Pc.l186 (SD.na.getD 186 0)) (SD.nk.getD 186 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q186_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Alpha.Pc.q186_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r186))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 189) CFSG.KD.Fi24Alpha.Pc.p187 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 191) CFSG.KD.Fi24Alpha.Pc.p189 rfl rfl)))))))).trans CFSG.KD.Fi24Alpha.Pc.f15

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v192 : Nat := CFSG.KD.Fi24Alpha.KV1 78
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v193 : Nat := CFSG.KD.Fi24Alpha.KV1 79
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l194 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v192, CFSG.KD.Fi24Alpha.Pc.v193]
theorem CFSG.KD.Fi24Alpha.Pc.p192 : Nat.beq (runC AR SD 192 (ckL CFSG.KD.Fi24Alpha.Pc.l194) 2 192 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v194 : Nat := CFSG.KD.Fi24Alpha.KV1 80
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v195 : Nat := CFSG.KD.Fi24Alpha.KV1 81
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l196 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v192, CFSG.KD.Fi24Alpha.Pc.v193, CFSG.KD.Fi24Alpha.Pc.v194, CFSG.KD.Fi24Alpha.Pc.v195]
theorem CFSG.KD.Fi24Alpha.Pc.p194 : Nat.beq (runC AR SD 192 (ckL CFSG.KD.Fi24Alpha.Pc.l196) 2 194 CFSG.KD.Fi24Alpha.Pc.l194) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v196 : Nat := CFSG.KD.Fi24Alpha.KV1 82
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v197 : Nat := CFSG.KD.Fi24Alpha.KV1 83
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l198 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v192, CFSG.KD.Fi24Alpha.Pc.v193, CFSG.KD.Fi24Alpha.Pc.v194, CFSG.KD.Fi24Alpha.Pc.v195, CFSG.KD.Fi24Alpha.Pc.v196, CFSG.KD.Fi24Alpha.Pc.v197]
theorem CFSG.KD.Fi24Alpha.Pc.p196 : Nat.beq (runC AR SD 192 (ckL CFSG.KD.Fi24Alpha.Pc.l198) 2 196 CFSG.KD.Fi24Alpha.Pc.l196) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v198 : Nat := CFSG.KD.Fi24Alpha.KV1 84
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v199 : Nat := CFSG.KD.Fi24Alpha.KV1 85
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l200 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v192, CFSG.KD.Fi24Alpha.Pc.v193, CFSG.KD.Fi24Alpha.Pc.v194, CFSG.KD.Fi24Alpha.Pc.v195, CFSG.KD.Fi24Alpha.Pc.v196, CFSG.KD.Fi24Alpha.Pc.v197, CFSG.KD.Fi24Alpha.Pc.v198, CFSG.KD.Fi24Alpha.Pc.v199]
theorem CFSG.KD.Fi24Alpha.Pc.p198 : Nat.beq (runC AR SD 192 (ckL CFSG.KD.Fi24Alpha.Pc.l200) 2 198 CFSG.KD.Fi24Alpha.Pc.l198) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v200 : Nat := CFSG.KD.Fi24Alpha.KV1 86
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v201 : Nat := CFSG.KD.Fi24Alpha.KV1 87
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l202 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v192, CFSG.KD.Fi24Alpha.Pc.v193, CFSG.KD.Fi24Alpha.Pc.v194, CFSG.KD.Fi24Alpha.Pc.v195, CFSG.KD.Fi24Alpha.Pc.v196, CFSG.KD.Fi24Alpha.Pc.v197, CFSG.KD.Fi24Alpha.Pc.v198, CFSG.KD.Fi24Alpha.Pc.v199, CFSG.KD.Fi24Alpha.Pc.v200, CFSG.KD.Fi24Alpha.Pc.v201]
theorem CFSG.KD.Fi24Alpha.Pc.p200 : Nat.beq (runC AR SD 192 (ckL CFSG.KD.Fi24Alpha.Pc.l202) 2 200 CFSG.KD.Fi24Alpha.Pc.l200) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v202 : Nat := CFSG.KD.Fi24Alpha.KV1 88
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v203 : Nat := CFSG.KD.Fi24Alpha.KV1 89
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l204 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v192, CFSG.KD.Fi24Alpha.Pc.v193, CFSG.KD.Fi24Alpha.Pc.v194, CFSG.KD.Fi24Alpha.Pc.v195, CFSG.KD.Fi24Alpha.Pc.v196, CFSG.KD.Fi24Alpha.Pc.v197, CFSG.KD.Fi24Alpha.Pc.v198, CFSG.KD.Fi24Alpha.Pc.v199, CFSG.KD.Fi24Alpha.Pc.v200, CFSG.KD.Fi24Alpha.Pc.v201, CFSG.KD.Fi24Alpha.Pc.v202, CFSG.KD.Fi24Alpha.Pc.v203]
theorem CFSG.KD.Fi24Alpha.Pc.p202 : Nat.beq (runC AR SD 192 (ckL CFSG.KD.Fi24Alpha.Pc.l204) 2 202 CFSG.KD.Fi24Alpha.Pc.l202) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v204 : Nat := CFSG.KD.Fi24Alpha.KV1 90
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v205 : Nat := CFSG.KD.Fi24Alpha.KV1 91
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l206 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v192, CFSG.KD.Fi24Alpha.Pc.v193, CFSG.KD.Fi24Alpha.Pc.v194, CFSG.KD.Fi24Alpha.Pc.v195, CFSG.KD.Fi24Alpha.Pc.v196, CFSG.KD.Fi24Alpha.Pc.v197, CFSG.KD.Fi24Alpha.Pc.v198, CFSG.KD.Fi24Alpha.Pc.v199, CFSG.KD.Fi24Alpha.Pc.v200, CFSG.KD.Fi24Alpha.Pc.v201, CFSG.KD.Fi24Alpha.Pc.v202, CFSG.KD.Fi24Alpha.Pc.v203, CFSG.KD.Fi24Alpha.Pc.v204, CFSG.KD.Fi24Alpha.Pc.v205]
theorem CFSG.KD.Fi24Alpha.Pc.p204 : Nat.beq (runC AR SD 192 (ckL CFSG.KD.Fi24Alpha.Pc.l206) 2 204 CFSG.KD.Fi24Alpha.Pc.l204) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v206 : Nat := CFSG.KD.Fi24Alpha.KV1 92
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v207 : Nat := CFSG.KD.Fi24Alpha.KV1 93
theorem CFSG.KD.Fi24Alpha.Pc.f16 : Nat.beq (runC AR SD 192 (finC AR SD (nat_lit 16) 192 208) 2 206 CFSG.KD.Fi24Alpha.Pc.l206) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk16 : chk (nat_lit 16) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 16) (lo := 192) (hi := 208) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 194) CFSG.KD.Fi24Alpha.Pc.p192 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 196) CFSG.KD.Fi24Alpha.Pc.p194 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 198) CFSG.KD.Fi24Alpha.Pc.p196 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 200) CFSG.KD.Fi24Alpha.Pc.p198 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 202) CFSG.KD.Fi24Alpha.Pc.p200 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 204) CFSG.KD.Fi24Alpha.Pc.p202 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 206) CFSG.KD.Fi24Alpha.Pc.p204 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f16

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v208 : Nat := CFSG.KD.Fi24Alpha.KV1 94
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l209 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v208]
theorem CFSG.KD.Fi24Alpha.Pc.p208 : Nat.beq (runC AR SD 208 (ckL CFSG.KD.Fi24Alpha.Pc.l209) 1 208 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a209_2 : Nat := CFSG.KD.Fi24Alpha.KV1 95
theorem CFSG.KD.Fi24Alpha.Pc.q209_2 : Nat.beq (powTop AR.mul (getV AR SD 208 CFSG.KD.Fi24Alpha.Pc.l209 (SD.na.getD 209 0)) (SD.nk.getD 209 1) 2 (ckP CFSG.KD.Fi24Alpha.Pc.a209_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a209_1 : Nat := CFSG.KD.Fi24Alpha.KV1 96
theorem CFSG.KD.Fi24Alpha.Pc.q209_1 : Nat.beq (powTop AR.mul (getV AR SD 208 CFSG.KD.Fi24Alpha.Pc.l209 (SD.na.getD 209 0)) (SD.nk.getD 209 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a209_1) 1 CFSG.KD.Fi24Alpha.Pc.a209_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v209 : Nat := CFSG.KD.Fi24Alpha.KV1 97
theorem CFSG.KD.Fi24Alpha.Pc.r209 : Nat.beq (powR AR.mul AR.one (getV AR SD 208 CFSG.KD.Fi24Alpha.Pc.l209 (SD.na.getD 209 0)) (SD.nk.getD 209 1) 1 CFSG.KD.Fi24Alpha.Pc.a209_1 true) CFSG.KD.Fi24Alpha.Pc.v209 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v210 : Nat := CFSG.KD.Fi24Alpha.KV1 98
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v211 : Nat := CFSG.KD.Fi24Alpha.KV1 99
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l210 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v208, CFSG.KD.Fi24Alpha.Pc.v209]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l212 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v208, CFSG.KD.Fi24Alpha.Pc.v209, CFSG.KD.Fi24Alpha.Pc.v210, CFSG.KD.Fi24Alpha.Pc.v211]
theorem CFSG.KD.Fi24Alpha.Pc.p210 : Nat.beq (runC AR SD 208 (ckL CFSG.KD.Fi24Alpha.Pc.l212) 2 210 CFSG.KD.Fi24Alpha.Pc.l210) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v212 : Nat := CFSG.KD.Fi24Alpha.KV1 100
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l213 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v208, CFSG.KD.Fi24Alpha.Pc.v209, CFSG.KD.Fi24Alpha.Pc.v210, CFSG.KD.Fi24Alpha.Pc.v211, CFSG.KD.Fi24Alpha.Pc.v212]
theorem CFSG.KD.Fi24Alpha.Pc.p212 : Nat.beq (runC AR SD 208 (ckL CFSG.KD.Fi24Alpha.Pc.l213) 1 212 CFSG.KD.Fi24Alpha.Pc.l212) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a213_2 : Nat := CFSG.KD.Fi24Alpha.KV1 101
theorem CFSG.KD.Fi24Alpha.Pc.q213_2 : Nat.beq (powTop AR.mul (getV AR SD 208 CFSG.KD.Fi24Alpha.Pc.l213 (SD.na.getD 213 0)) (SD.nk.getD 213 1) 2 (ckP CFSG.KD.Fi24Alpha.Pc.a213_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a213_1 : Nat := CFSG.KD.Fi24Alpha.KV1 102
theorem CFSG.KD.Fi24Alpha.Pc.q213_1 : Nat.beq (powTop AR.mul (getV AR SD 208 CFSG.KD.Fi24Alpha.Pc.l213 (SD.na.getD 213 0)) (SD.nk.getD 213 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a213_1) 1 CFSG.KD.Fi24Alpha.Pc.a213_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v213 : Nat := CFSG.KD.Fi24Alpha.KV1 103
theorem CFSG.KD.Fi24Alpha.Pc.r213 : Nat.beq (powR AR.mul AR.one (getV AR SD 208 CFSG.KD.Fi24Alpha.Pc.l213 (SD.na.getD 213 0)) (SD.nk.getD 213 1) 1 CFSG.KD.Fi24Alpha.Pc.a213_1 true) CFSG.KD.Fi24Alpha.Pc.v213 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v214 : Nat := CFSG.KD.Fi24Alpha.KV1 104
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v215 : Nat := CFSG.KD.Fi24Alpha.KV1 105
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l214 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v208, CFSG.KD.Fi24Alpha.Pc.v209, CFSG.KD.Fi24Alpha.Pc.v210, CFSG.KD.Fi24Alpha.Pc.v211, CFSG.KD.Fi24Alpha.Pc.v212, CFSG.KD.Fi24Alpha.Pc.v213]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l216 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v208, CFSG.KD.Fi24Alpha.Pc.v209, CFSG.KD.Fi24Alpha.Pc.v210, CFSG.KD.Fi24Alpha.Pc.v211, CFSG.KD.Fi24Alpha.Pc.v212, CFSG.KD.Fi24Alpha.Pc.v213, CFSG.KD.Fi24Alpha.Pc.v214, CFSG.KD.Fi24Alpha.Pc.v215]
theorem CFSG.KD.Fi24Alpha.Pc.p214 : Nat.beq (runC AR SD 208 (ckL CFSG.KD.Fi24Alpha.Pc.l216) 2 214 CFSG.KD.Fi24Alpha.Pc.l214) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v216 : Nat := CFSG.KD.Fi24Alpha.KV1 106
theorem CFSG.KD.Fi24Alpha.Pc.f17 : Nat.beq (runC AR SD 208 (finC AR SD (nat_lit 17) 208 217) 1 216 CFSG.KD.Fi24Alpha.Pc.l216) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk17 : chk (nat_lit 17) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 17) (lo := 208) (hi := 217) (m := 9) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 9) (m2 := 8) (j2 := 209) CFSG.KD.Fi24Alpha.Pc.p208 rfl rfl).trans ((runC_node (m := 8) (m2 := 7) (j2 := 210) (Lr := CFSG.KD.Fi24Alpha.Pc.l210) ((nodeV_pow (R := AR) (D := SD) (lo := 208) (L := CFSG.KD.Fi24Alpha.Pc.l209) (j := 209) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 208 CFSG.KD.Fi24Alpha.Pc.l209 (SD.na.getD 209 0)) (SD.nk.getD 209 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q209_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Alpha.Pc.q209_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r209))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 212) CFSG.KD.Fi24Alpha.Pc.p210 rfl rfl).trans ((runC_seq (m := 5) (m2 := 4) (j2 := 213) CFSG.KD.Fi24Alpha.Pc.p212 rfl rfl).trans ((runC_node (m := 4) (m2 := 3) (j2 := 214) (Lr := CFSG.KD.Fi24Alpha.Pc.l214) ((nodeV_pow (R := AR) (D := SD) (lo := 208) (L := CFSG.KD.Fi24Alpha.Pc.l213) (j := 213) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 208 CFSG.KD.Fi24Alpha.Pc.l213 (SD.na.getD 213 0)) (SD.nk.getD 213 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q213_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Alpha.Pc.q213_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r213))))) (by quickRfl) rfl rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 216) CFSG.KD.Fi24Alpha.Pc.p214 rfl rfl)))))))).trans CFSG.KD.Fi24Alpha.Pc.f17

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a217_2 : Nat := CFSG.KD.Fi24Alpha.KV1 107
theorem CFSG.KD.Fi24Alpha.Pc.q217_2 : Nat.beq (powTop AR.mul (getV AR SD 217 [] (SD.na.getD 217 0)) (SD.nk.getD 217 1) 2 (ckP CFSG.KD.Fi24Alpha.Pc.a217_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a217_1 : Nat := CFSG.KD.Fi24Alpha.KV1 108
theorem CFSG.KD.Fi24Alpha.Pc.q217_1 : Nat.beq (powTop AR.mul (getV AR SD 217 [] (SD.na.getD 217 0)) (SD.nk.getD 217 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a217_1) 1 CFSG.KD.Fi24Alpha.Pc.a217_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v217 : Nat := CFSG.KD.Fi24Alpha.KV1 109
theorem CFSG.KD.Fi24Alpha.Pc.r217 : Nat.beq (powR AR.mul AR.one (getV AR SD 217 [] (SD.na.getD 217 0)) (SD.nk.getD 217 1) 1 CFSG.KD.Fi24Alpha.Pc.a217_1 true) CFSG.KD.Fi24Alpha.Pc.v217 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v218 : Nat := CFSG.KD.Fi24Alpha.KV1 110
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l218 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v217]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l219 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v217, CFSG.KD.Fi24Alpha.Pc.v218]
theorem CFSG.KD.Fi24Alpha.Pc.p218 : Nat.beq (runC AR SD 217 (ckL CFSG.KD.Fi24Alpha.Pc.l219) 1 218 CFSG.KD.Fi24Alpha.Pc.l218) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a219_2 : Nat := CFSG.KD.Fi24Alpha.KV1 111
theorem CFSG.KD.Fi24Alpha.Pc.q219_2 : Nat.beq (powTop AR.mul (getV AR SD 217 CFSG.KD.Fi24Alpha.Pc.l219 (SD.na.getD 219 0)) (SD.nk.getD 219 1) 2 (ckP CFSG.KD.Fi24Alpha.Pc.a219_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a219_1 : Nat := CFSG.KD.Fi24Alpha.KV1 112
theorem CFSG.KD.Fi24Alpha.Pc.q219_1 : Nat.beq (powTop AR.mul (getV AR SD 217 CFSG.KD.Fi24Alpha.Pc.l219 (SD.na.getD 219 0)) (SD.nk.getD 219 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a219_1) 1 CFSG.KD.Fi24Alpha.Pc.a219_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v219 : Nat := CFSG.KD.Fi24Alpha.KV1 113
theorem CFSG.KD.Fi24Alpha.Pc.r219 : Nat.beq (powR AR.mul AR.one (getV AR SD 217 CFSG.KD.Fi24Alpha.Pc.l219 (SD.na.getD 219 0)) (SD.nk.getD 219 1) 1 CFSG.KD.Fi24Alpha.Pc.a219_1 true) CFSG.KD.Fi24Alpha.Pc.v219 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v220 : Nat := CFSG.KD.Fi24Alpha.KV1 114
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v221 : Nat := CFSG.KD.Fi24Alpha.KV1 115
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l220 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v217, CFSG.KD.Fi24Alpha.Pc.v218, CFSG.KD.Fi24Alpha.Pc.v219]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l222 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v217, CFSG.KD.Fi24Alpha.Pc.v218, CFSG.KD.Fi24Alpha.Pc.v219, CFSG.KD.Fi24Alpha.Pc.v220, CFSG.KD.Fi24Alpha.Pc.v221]
theorem CFSG.KD.Fi24Alpha.Pc.p220 : Nat.beq (runC AR SD 217 (ckL CFSG.KD.Fi24Alpha.Pc.l222) 2 220 CFSG.KD.Fi24Alpha.Pc.l220) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v222 : Nat := CFSG.KD.Fi24Alpha.KV1 116
theorem CFSG.KD.Fi24Alpha.Pc.f18 : Nat.beq (runC AR SD 217 (finC AR SD (nat_lit 18) 217 223) 1 222 CFSG.KD.Fi24Alpha.Pc.l222) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk18 : chk (nat_lit 18) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 18) (lo := 217) (hi := 223) (m := 6) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 6) (m2 := 5) (j2 := 218) (Lr := CFSG.KD.Fi24Alpha.Pc.l218) ((nodeV_pow (R := AR) (D := SD) (lo := 217) (L := []) (j := 217) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 217 [] (SD.na.getD 217 0)) (SD.nk.getD 217 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q217_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Alpha.Pc.q217_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r217))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 5) (m2 := 4) (j2 := 219) CFSG.KD.Fi24Alpha.Pc.p218 rfl rfl).trans ((runC_node (m := 4) (m2 := 3) (j2 := 220) (Lr := CFSG.KD.Fi24Alpha.Pc.l220) ((nodeV_pow (R := AR) (D := SD) (lo := 217) (L := CFSG.KD.Fi24Alpha.Pc.l219) (j := 219) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 217 CFSG.KD.Fi24Alpha.Pc.l219 (SD.na.getD 219 0)) (SD.nk.getD 219 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q219_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Alpha.Pc.q219_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r219))))) (by quickRfl) rfl rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 222) CFSG.KD.Fi24Alpha.Pc.p220 rfl rfl)))))).trans CFSG.KD.Fi24Alpha.Pc.f18

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a223_1 : Nat := CFSG.KD.Fi24Alpha.KV1 117
theorem CFSG.KD.Fi24Alpha.Pc.q223_1 : Nat.beq (powTop AR.mul (getV AR SD 223 [] (SD.na.getD 223 0)) (SD.nk.getD 223 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a223_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v223 : Nat := CFSG.KD.Fi24Alpha.KV1 118
theorem CFSG.KD.Fi24Alpha.Pc.r223 : Nat.beq (powR AR.mul AR.one (getV AR SD 223 [] (SD.na.getD 223 0)) (SD.nk.getD 223 1) 1 CFSG.KD.Fi24Alpha.Pc.a223_1 true) CFSG.KD.Fi24Alpha.Pc.v223 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v224 : Nat := CFSG.KD.Fi24Alpha.KV1 119
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l224 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v223]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l225 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v223, CFSG.KD.Fi24Alpha.Pc.v224]
theorem CFSG.KD.Fi24Alpha.Pc.p224 : Nat.beq (runC AR SD 223 (ckL CFSG.KD.Fi24Alpha.Pc.l225) 1 224 CFSG.KD.Fi24Alpha.Pc.l224) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a225_1 : Nat := CFSG.KD.Fi24Alpha.KV1 120
theorem CFSG.KD.Fi24Alpha.Pc.q225_1 : Nat.beq (powTop AR.mul (getV AR SD 223 CFSG.KD.Fi24Alpha.Pc.l225 (SD.na.getD 225 0)) (SD.nk.getD 225 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a225_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v225 : Nat := CFSG.KD.Fi24Alpha.KV1 121
theorem CFSG.KD.Fi24Alpha.Pc.r225 : Nat.beq (powR AR.mul AR.one (getV AR SD 223 CFSG.KD.Fi24Alpha.Pc.l225 (SD.na.getD 225 0)) (SD.nk.getD 225 1) 1 CFSG.KD.Fi24Alpha.Pc.a225_1 true) CFSG.KD.Fi24Alpha.Pc.v225 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v226 : Nat := CFSG.KD.Fi24Alpha.KV1 122
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v227 : Nat := CFSG.KD.Fi24Alpha.KV1 123
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l226 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v223, CFSG.KD.Fi24Alpha.Pc.v224, CFSG.KD.Fi24Alpha.Pc.v225]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l228 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v223, CFSG.KD.Fi24Alpha.Pc.v224, CFSG.KD.Fi24Alpha.Pc.v225, CFSG.KD.Fi24Alpha.Pc.v226, CFSG.KD.Fi24Alpha.Pc.v227]
theorem CFSG.KD.Fi24Alpha.Pc.p226 : Nat.beq (runC AR SD 223 (ckL CFSG.KD.Fi24Alpha.Pc.l228) 2 226 CFSG.KD.Fi24Alpha.Pc.l226) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v228 : Nat := CFSG.KD.Fi24Alpha.KV1 124
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v229 : Nat := CFSG.KD.Fi24Alpha.KV1 125
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l230 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v223, CFSG.KD.Fi24Alpha.Pc.v224, CFSG.KD.Fi24Alpha.Pc.v225, CFSG.KD.Fi24Alpha.Pc.v226, CFSG.KD.Fi24Alpha.Pc.v227, CFSG.KD.Fi24Alpha.Pc.v228, CFSG.KD.Fi24Alpha.Pc.v229]
theorem CFSG.KD.Fi24Alpha.Pc.p228 : Nat.beq (runC AR SD 223 (ckL CFSG.KD.Fi24Alpha.Pc.l230) 2 228 CFSG.KD.Fi24Alpha.Pc.l228) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v230 : Nat := CFSG.KD.Fi24Alpha.KV1 126
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v231 : Nat := CFSG.KD.Fi24Alpha.KV1 127
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l232 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v223, CFSG.KD.Fi24Alpha.Pc.v224, CFSG.KD.Fi24Alpha.Pc.v225, CFSG.KD.Fi24Alpha.Pc.v226, CFSG.KD.Fi24Alpha.Pc.v227, CFSG.KD.Fi24Alpha.Pc.v228, CFSG.KD.Fi24Alpha.Pc.v229, CFSG.KD.Fi24Alpha.Pc.v230, CFSG.KD.Fi24Alpha.Pc.v231]
theorem CFSG.KD.Fi24Alpha.Pc.p230 : Nat.beq (runC AR SD 223 (ckL CFSG.KD.Fi24Alpha.Pc.l232) 2 230 CFSG.KD.Fi24Alpha.Pc.l230) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v232 : Nat := CFSG.KD.Fi24Alpha.KV1 128
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v233 : Nat := CFSG.KD.Fi24Alpha.KV1 129
theorem CFSG.KD.Fi24Alpha.Pc.f19 : Nat.beq (runC AR SD 223 (finC AR SD (nat_lit 19) 223 234) 2 232 CFSG.KD.Fi24Alpha.Pc.l232) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk19 : chk (nat_lit 19) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 19) (lo := 223) (hi := 234) (m := 11) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 11) (m2 := 10) (j2 := 224) (Lr := CFSG.KD.Fi24Alpha.Pc.l224) ((nodeV_pow (R := AR) (D := SD) (lo := 223) (L := []) (j := 223) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 223 [] (SD.na.getD 223 0)) (SD.nk.getD 223 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q223_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r223)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 10) (m2 := 9) (j2 := 225) CFSG.KD.Fi24Alpha.Pc.p224 rfl rfl).trans ((runC_node (m := 9) (m2 := 8) (j2 := 226) (Lr := CFSG.KD.Fi24Alpha.Pc.l226) ((nodeV_pow (R := AR) (D := SD) (lo := 223) (L := CFSG.KD.Fi24Alpha.Pc.l225) (j := 225) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 223 CFSG.KD.Fi24Alpha.Pc.l225 (SD.na.getD 225 0)) (SD.nk.getD 225 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q225_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r225)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 228) CFSG.KD.Fi24Alpha.Pc.p226 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 230) CFSG.KD.Fi24Alpha.Pc.p228 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 232) CFSG.KD.Fi24Alpha.Pc.p230 rfl rfl)))))))).trans CFSG.KD.Fi24Alpha.Pc.f19

end
