module

public import Certificates.Kernel.Sporadic.Fi24Tc.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Tc KV1 "Certificates/Kernel/Sporadic/Fi24Tc/data/v1.bin" 152491 4 14944118 15911503505247956119

public section

open CFSG.KD.Fi24Tc CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v127 : Nat := CFSG.KD.Fi24Tc.KV1 0
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v128 : Nat := CFSG.KD.Fi24Tc.KV1 1
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l129 : List Nat := [CFSG.KD.Fi24Tc.Pc.v127, CFSG.KD.Fi24Tc.Pc.v128]
theorem CFSG.KD.Fi24Tc.Pc.p127 : Nat.beq (runC AR SD 127 (ckL CFSG.KD.Fi24Tc.Pc.l129) 2 127 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v129 : Nat := CFSG.KD.Fi24Tc.KV1 2
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v130 : Nat := CFSG.KD.Fi24Tc.KV1 3
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l131 : List Nat := [CFSG.KD.Fi24Tc.Pc.v127, CFSG.KD.Fi24Tc.Pc.v128, CFSG.KD.Fi24Tc.Pc.v129, CFSG.KD.Fi24Tc.Pc.v130]
theorem CFSG.KD.Fi24Tc.Pc.p129 : Nat.beq (runC AR SD 127 (ckL CFSG.KD.Fi24Tc.Pc.l131) 2 129 CFSG.KD.Fi24Tc.Pc.l129) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v131 : Nat := CFSG.KD.Fi24Tc.KV1 4
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v132 : Nat := CFSG.KD.Fi24Tc.KV1 5
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l133 : List Nat := [CFSG.KD.Fi24Tc.Pc.v127, CFSG.KD.Fi24Tc.Pc.v128, CFSG.KD.Fi24Tc.Pc.v129, CFSG.KD.Fi24Tc.Pc.v130, CFSG.KD.Fi24Tc.Pc.v131, CFSG.KD.Fi24Tc.Pc.v132]
theorem CFSG.KD.Fi24Tc.Pc.p131 : Nat.beq (runC AR SD 127 (ckL CFSG.KD.Fi24Tc.Pc.l133) 2 131 CFSG.KD.Fi24Tc.Pc.l131) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f20 : Nat.beq (runC AR SD 127 (finC AR SD (nat_lit 20) 127 135) 2 133 CFSG.KD.Fi24Tc.Pc.l133) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk20 : chk (nat_lit 20) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 20) (lo := 127) (hi := 135) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 129) CFSG.KD.Fi24Tc.Pc.p127 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 131) CFSG.KD.Fi24Tc.Pc.p129 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 133) CFSG.KD.Fi24Tc.Pc.p131 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f20

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v135 : Nat := CFSG.KD.Fi24Tc.KV1 6
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v136 : Nat := CFSG.KD.Fi24Tc.KV1 7
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l137 : List Nat := [CFSG.KD.Fi24Tc.Pc.v135, CFSG.KD.Fi24Tc.Pc.v136]
theorem CFSG.KD.Fi24Tc.Pc.p135 : Nat.beq (runC AR SD 135 (ckL CFSG.KD.Fi24Tc.Pc.l137) 2 135 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a137_3 : Nat := CFSG.KD.Fi24Tc.KV1 8
theorem CFSG.KD.Fi24Tc.Pc.q137_3 : Nat.beq (powTop AR.mul (getV AR SD 135 CFSG.KD.Fi24Tc.Pc.l137 (SD.na.getD 137 0)) (SD.nk.getD 137 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a137_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a137_1 : Nat := CFSG.KD.Fi24Tc.KV1 9
theorem CFSG.KD.Fi24Tc.Pc.q137_1 : Nat.beq (powTop AR.mul (getV AR SD 135 CFSG.KD.Fi24Tc.Pc.l137 (SD.na.getD 137 0)) (SD.nk.getD 137 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a137_1) 2 CFSG.KD.Fi24Tc.Pc.a137_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v137 : Nat := CFSG.KD.Fi24Tc.KV1 10
theorem CFSG.KD.Fi24Tc.Pc.r137 : Nat.beq (powR AR.mul AR.one (getV AR SD 135 CFSG.KD.Fi24Tc.Pc.l137 (SD.na.getD 137 0)) (SD.nk.getD 137 1) 1 CFSG.KD.Fi24Tc.Pc.a137_1 true) CFSG.KD.Fi24Tc.Pc.v137 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l138 : List Nat := [CFSG.KD.Fi24Tc.Pc.v135, CFSG.KD.Fi24Tc.Pc.v136, CFSG.KD.Fi24Tc.Pc.v137]
theorem CFSG.KD.Fi24Tc.Pc.f21 : Nat.beq (runC AR SD 135 (finC AR SD (nat_lit 21) 135 138) 0 138 CFSG.KD.Fi24Tc.Pc.l138) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk21 : chk (nat_lit 21) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 21) (lo := 135) (hi := 138) (m := 3) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 3) (m2 := 1) (j2 := 137) CFSG.KD.Fi24Tc.Pc.p135 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 138) (Lr := CFSG.KD.Fi24Tc.Pc.l138) ((nodeV_pow (R := AR) (D := SD) (lo := 135) (L := CFSG.KD.Fi24Tc.Pc.l137) (j := 137) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 135 CFSG.KD.Fi24Tc.Pc.l137 (SD.na.getD 137 0)) (SD.nk.getD 137 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q137_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q137_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r137))))) (by quickRfl) rfl rfl rfl)))).trans CFSG.KD.Fi24Tc.Pc.f21

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v138 : Nat := CFSG.KD.Fi24Tc.KV1 11
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v139 : Nat := CFSG.KD.Fi24Tc.KV1 12
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l140 : List Nat := [CFSG.KD.Fi24Tc.Pc.v138, CFSG.KD.Fi24Tc.Pc.v139]
theorem CFSG.KD.Fi24Tc.Pc.p138 : Nat.beq (runC AR SD 138 (ckL CFSG.KD.Fi24Tc.Pc.l140) 2 138 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v140 : Nat := CFSG.KD.Fi24Tc.KV1 13
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v141 : Nat := CFSG.KD.Fi24Tc.KV1 14
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l142 : List Nat := [CFSG.KD.Fi24Tc.Pc.v138, CFSG.KD.Fi24Tc.Pc.v139, CFSG.KD.Fi24Tc.Pc.v140, CFSG.KD.Fi24Tc.Pc.v141]
theorem CFSG.KD.Fi24Tc.Pc.p140 : Nat.beq (runC AR SD 138 (ckL CFSG.KD.Fi24Tc.Pc.l142) 2 140 CFSG.KD.Fi24Tc.Pc.l140) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v142 : Nat := CFSG.KD.Fi24Tc.KV1 15
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v143 : Nat := CFSG.KD.Fi24Tc.KV1 16
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l144 : List Nat := [CFSG.KD.Fi24Tc.Pc.v138, CFSG.KD.Fi24Tc.Pc.v139, CFSG.KD.Fi24Tc.Pc.v140, CFSG.KD.Fi24Tc.Pc.v141, CFSG.KD.Fi24Tc.Pc.v142, CFSG.KD.Fi24Tc.Pc.v143]
theorem CFSG.KD.Fi24Tc.Pc.p142 : Nat.beq (runC AR SD 138 (ckL CFSG.KD.Fi24Tc.Pc.l144) 2 142 CFSG.KD.Fi24Tc.Pc.l142) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f22 : Nat.beq (runC AR SD 138 (finC AR SD (nat_lit 22) 138 146) 2 144 CFSG.KD.Fi24Tc.Pc.l144) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk22 : chk (nat_lit 22) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 22) (lo := 138) (hi := 146) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 140) CFSG.KD.Fi24Tc.Pc.p138 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 142) CFSG.KD.Fi24Tc.Pc.p140 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 144) CFSG.KD.Fi24Tc.Pc.p142 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f22

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a146_2 : Nat := CFSG.KD.Fi24Tc.KV1 17
theorem CFSG.KD.Fi24Tc.Pc.q146_2 : Nat.beq (powTop AR.mul (getV AR SD 146 [] (SD.na.getD 146 0)) (SD.nk.getD 146 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a146_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a146_1 : Nat := CFSG.KD.Fi24Tc.KV1 18
theorem CFSG.KD.Fi24Tc.Pc.q146_1 : Nat.beq (powTop AR.mul (getV AR SD 146 [] (SD.na.getD 146 0)) (SD.nk.getD 146 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a146_1) 1 CFSG.KD.Fi24Tc.Pc.a146_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v146 : Nat := CFSG.KD.Fi24Tc.KV1 19
theorem CFSG.KD.Fi24Tc.Pc.r146 : Nat.beq (powR AR.mul AR.one (getV AR SD 146 [] (SD.na.getD 146 0)) (SD.nk.getD 146 1) 1 CFSG.KD.Fi24Tc.Pc.a146_1 true) CFSG.KD.Fi24Tc.Pc.v146 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l147 : List Nat := [CFSG.KD.Fi24Tc.Pc.v146]
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v147 : Nat := CFSG.KD.Fi24Tc.KV1 20
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v148 : Nat := CFSG.KD.Fi24Tc.KV1 21
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l149 : List Nat := [CFSG.KD.Fi24Tc.Pc.v146, CFSG.KD.Fi24Tc.Pc.v147, CFSG.KD.Fi24Tc.Pc.v148]
theorem CFSG.KD.Fi24Tc.Pc.p147 : Nat.beq (runC AR SD 146 (ckL CFSG.KD.Fi24Tc.Pc.l149) 2 147 CFSG.KD.Fi24Tc.Pc.l147) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f23 : Nat.beq (runC AR SD 146 (finC AR SD (nat_lit 23) 146 150) 1 149 CFSG.KD.Fi24Tc.Pc.l149) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk23 : chk (nat_lit 23) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 23) (lo := 146) (hi := 150) (m := 4) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 4) (m2 := 3) (j2 := 147) (Lr := CFSG.KD.Fi24Tc.Pc.l147) ((nodeV_pow (R := AR) (D := SD) (lo := 146) (L := []) (j := 146) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 146 [] (SD.na.getD 146 0)) (SD.nk.getD 146 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q146_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q146_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r146))))) (by quickRfl) rfl rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 149) CFSG.KD.Fi24Tc.Pc.p147 rfl rfl)))).trans CFSG.KD.Fi24Tc.Pc.f23

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v150 : Nat := CFSG.KD.Fi24Tc.KV1 22
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v151 : Nat := CFSG.KD.Fi24Tc.KV1 23
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l152 : List Nat := [CFSG.KD.Fi24Tc.Pc.v150, CFSG.KD.Fi24Tc.Pc.v151]
theorem CFSG.KD.Fi24Tc.Pc.p150 : Nat.beq (runC AR SD 150 (ckL CFSG.KD.Fi24Tc.Pc.l152) 2 150 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v152 : Nat := CFSG.KD.Fi24Tc.KV1 24
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l153 : List Nat := [CFSG.KD.Fi24Tc.Pc.v150, CFSG.KD.Fi24Tc.Pc.v151, CFSG.KD.Fi24Tc.Pc.v152]
theorem CFSG.KD.Fi24Tc.Pc.p152 : Nat.beq (runC AR SD 150 (ckL CFSG.KD.Fi24Tc.Pc.l153) 1 152 CFSG.KD.Fi24Tc.Pc.l152) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a153_3 : Nat := CFSG.KD.Fi24Tc.KV1 25
theorem CFSG.KD.Fi24Tc.Pc.q153_3 : Nat.beq (powTop AR.mul (getV AR SD 150 CFSG.KD.Fi24Tc.Pc.l153 (SD.na.getD 153 0)) (SD.nk.getD 153 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a153_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a153_1 : Nat := CFSG.KD.Fi24Tc.KV1 26
theorem CFSG.KD.Fi24Tc.Pc.q153_1 : Nat.beq (powTop AR.mul (getV AR SD 150 CFSG.KD.Fi24Tc.Pc.l153 (SD.na.getD 153 0)) (SD.nk.getD 153 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a153_1) 2 CFSG.KD.Fi24Tc.Pc.a153_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v153 : Nat := CFSG.KD.Fi24Tc.KV1 27
theorem CFSG.KD.Fi24Tc.Pc.r153 : Nat.beq (powR AR.mul AR.one (getV AR SD 150 CFSG.KD.Fi24Tc.Pc.l153 (SD.na.getD 153 0)) (SD.nk.getD 153 1) 1 CFSG.KD.Fi24Tc.Pc.a153_1 true) CFSG.KD.Fi24Tc.Pc.v153 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l154 : List Nat := [CFSG.KD.Fi24Tc.Pc.v150, CFSG.KD.Fi24Tc.Pc.v151, CFSG.KD.Fi24Tc.Pc.v152, CFSG.KD.Fi24Tc.Pc.v153]
theorem CFSG.KD.Fi24Tc.Pc.f24 : Nat.beq (runC AR SD 150 (finC AR SD (nat_lit 24) 150 154) 0 154 CFSG.KD.Fi24Tc.Pc.l154) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk24 : chk (nat_lit 24) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 24) (lo := 150) (hi := 154) (m := 4) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 4) (m2 := 2) (j2 := 152) CFSG.KD.Fi24Tc.Pc.p150 rfl rfl).trans ((runC_seq (m := 2) (m2 := 1) (j2 := 153) CFSG.KD.Fi24Tc.Pc.p152 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 154) (Lr := CFSG.KD.Fi24Tc.Pc.l154) ((nodeV_pow (R := AR) (D := SD) (lo := 150) (L := CFSG.KD.Fi24Tc.Pc.l153) (j := 153) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 150 CFSG.KD.Fi24Tc.Pc.l153 (SD.na.getD 153 0)) (SD.nk.getD 153 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q153_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q153_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r153))))) (by quickRfl) rfl rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f24

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v154 : Nat := CFSG.KD.Fi24Tc.KV1 28
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v155 : Nat := CFSG.KD.Fi24Tc.KV1 29
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l156 : List Nat := [CFSG.KD.Fi24Tc.Pc.v154, CFSG.KD.Fi24Tc.Pc.v155]
theorem CFSG.KD.Fi24Tc.Pc.p154 : Nat.beq (runC AR SD 154 (ckL CFSG.KD.Fi24Tc.Pc.l156) 2 154 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v156 : Nat := CFSG.KD.Fi24Tc.KV1 30
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v157 : Nat := CFSG.KD.Fi24Tc.KV1 31
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l158 : List Nat := [CFSG.KD.Fi24Tc.Pc.v154, CFSG.KD.Fi24Tc.Pc.v155, CFSG.KD.Fi24Tc.Pc.v156, CFSG.KD.Fi24Tc.Pc.v157]
theorem CFSG.KD.Fi24Tc.Pc.p156 : Nat.beq (runC AR SD 154 (ckL CFSG.KD.Fi24Tc.Pc.l158) 2 156 CFSG.KD.Fi24Tc.Pc.l156) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f25 : Nat.beq (runC AR SD 154 (finC AR SD (nat_lit 25) 154 160) 2 158 CFSG.KD.Fi24Tc.Pc.l158) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk25 : chk (nat_lit 25) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 25) (lo := 154) (hi := 160) (m := 6) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 6) (m2 := 4) (j2 := 156) CFSG.KD.Fi24Tc.Pc.p154 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 158) CFSG.KD.Fi24Tc.Pc.p156 rfl rfl)))).trans CFSG.KD.Fi24Tc.Pc.f25

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a160_3 : Nat := CFSG.KD.Fi24Tc.KV1 32
theorem CFSG.KD.Fi24Tc.Pc.q160_3 : Nat.beq (powTop AR.mul (getV AR SD 160 [] (SD.na.getD 160 0)) (SD.nk.getD 160 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a160_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a160_2 : Nat := CFSG.KD.Fi24Tc.KV1 33
theorem CFSG.KD.Fi24Tc.Pc.q160_2 : Nat.beq (powTop AR.mul (getV AR SD 160 [] (SD.na.getD 160 0)) (SD.nk.getD 160 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a160_2) 1 CFSG.KD.Fi24Tc.Pc.a160_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a160_1 : Nat := CFSG.KD.Fi24Tc.KV1 34
theorem CFSG.KD.Fi24Tc.Pc.q160_1 : Nat.beq (powTop AR.mul (getV AR SD 160 [] (SD.na.getD 160 0)) (SD.nk.getD 160 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a160_1) 1 CFSG.KD.Fi24Tc.Pc.a160_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v160 : Nat := CFSG.KD.Fi24Tc.KV1 35
theorem CFSG.KD.Fi24Tc.Pc.r160 : Nat.beq (powR AR.mul AR.one (getV AR SD 160 [] (SD.na.getD 160 0)) (SD.nk.getD 160 1) 1 CFSG.KD.Fi24Tc.Pc.a160_1 true) CFSG.KD.Fi24Tc.Pc.v160 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l161 : List Nat := [CFSG.KD.Fi24Tc.Pc.v160]
theorem CFSG.KD.Fi24Tc.Pc.f26 : Nat.beq (runC AR SD 160 (finC AR SD (nat_lit 26) 160 162) 1 161 CFSG.KD.Fi24Tc.Pc.l161) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk26 : chk (nat_lit 26) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 26) (lo := 160) (hi := 162) (m := 2) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 2) (m2 := 1) (j2 := 161) (Lr := CFSG.KD.Fi24Tc.Pc.l161) ((nodeV_pow (R := AR) (D := SD) (lo := 160) (L := []) (j := 160) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 160 [] (SD.na.getD 160 0)) (SD.nk.getD 160 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q160_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q160_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q160_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r160)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f26

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v162 : Nat := CFSG.KD.Fi24Tc.KV1 36
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v163 : Nat := CFSG.KD.Fi24Tc.KV1 37
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l164 : List Nat := [CFSG.KD.Fi24Tc.Pc.v162, CFSG.KD.Fi24Tc.Pc.v163]
theorem CFSG.KD.Fi24Tc.Pc.p162 : Nat.beq (runC AR SD 162 (ckL CFSG.KD.Fi24Tc.Pc.l164) 2 162 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v164 : Nat := CFSG.KD.Fi24Tc.KV1 38
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v165 : Nat := CFSG.KD.Fi24Tc.KV1 39
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l166 : List Nat := [CFSG.KD.Fi24Tc.Pc.v162, CFSG.KD.Fi24Tc.Pc.v163, CFSG.KD.Fi24Tc.Pc.v164, CFSG.KD.Fi24Tc.Pc.v165]
theorem CFSG.KD.Fi24Tc.Pc.p164 : Nat.beq (runC AR SD 162 (ckL CFSG.KD.Fi24Tc.Pc.l166) 2 164 CFSG.KD.Fi24Tc.Pc.l164) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a166_1 : Nat := CFSG.KD.Fi24Tc.KV1 40
theorem CFSG.KD.Fi24Tc.Pc.q166_1 : Nat.beq (powTop AR.mul (getV AR SD 162 CFSG.KD.Fi24Tc.Pc.l166 (SD.na.getD 166 0)) (SD.nk.getD 166 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a166_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v166 : Nat := CFSG.KD.Fi24Tc.KV1 41
theorem CFSG.KD.Fi24Tc.Pc.r166 : Nat.beq (powR AR.mul AR.one (getV AR SD 162 CFSG.KD.Fi24Tc.Pc.l166 (SD.na.getD 166 0)) (SD.nk.getD 166 1) 1 CFSG.KD.Fi24Tc.Pc.a166_1 true) CFSG.KD.Fi24Tc.Pc.v166 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l167 : List Nat := [CFSG.KD.Fi24Tc.Pc.v162, CFSG.KD.Fi24Tc.Pc.v163, CFSG.KD.Fi24Tc.Pc.v164, CFSG.KD.Fi24Tc.Pc.v165, CFSG.KD.Fi24Tc.Pc.v166]
theorem CFSG.KD.Fi24Tc.Pc.f27 : Nat.beq (runC AR SD 162 (finC AR SD (nat_lit 27) 162 167) 0 167 CFSG.KD.Fi24Tc.Pc.l167) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk27 : chk (nat_lit 27) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 27) (lo := 162) (hi := 167) (m := 5) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 5) (m2 := 3) (j2 := 164) CFSG.KD.Fi24Tc.Pc.p162 rfl rfl).trans ((runC_seq (m := 3) (m2 := 1) (j2 := 166) CFSG.KD.Fi24Tc.Pc.p164 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 167) (Lr := CFSG.KD.Fi24Tc.Pc.l167) ((nodeV_pow (R := AR) (D := SD) (lo := 162) (L := CFSG.KD.Fi24Tc.Pc.l166) (j := 166) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 162 CFSG.KD.Fi24Tc.Pc.l166 (SD.na.getD 166 0)) (SD.nk.getD 166 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q166_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r166)))) (by quickRfl) rfl rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f27

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v167 : Nat := CFSG.KD.Fi24Tc.KV1 42
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v168 : Nat := CFSG.KD.Fi24Tc.KV1 43
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l169 : List Nat := [CFSG.KD.Fi24Tc.Pc.v167, CFSG.KD.Fi24Tc.Pc.v168]
theorem CFSG.KD.Fi24Tc.Pc.p167 : Nat.beq (runC AR SD 167 (ckL CFSG.KD.Fi24Tc.Pc.l169) 2 167 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v169 : Nat := CFSG.KD.Fi24Tc.KV1 44
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v170 : Nat := CFSG.KD.Fi24Tc.KV1 45
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l171 : List Nat := [CFSG.KD.Fi24Tc.Pc.v167, CFSG.KD.Fi24Tc.Pc.v168, CFSG.KD.Fi24Tc.Pc.v169, CFSG.KD.Fi24Tc.Pc.v170]
theorem CFSG.KD.Fi24Tc.Pc.p169 : Nat.beq (runC AR SD 167 (ckL CFSG.KD.Fi24Tc.Pc.l171) 2 169 CFSG.KD.Fi24Tc.Pc.l169) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v171 : Nat := CFSG.KD.Fi24Tc.KV1 46
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v172 : Nat := CFSG.KD.Fi24Tc.KV1 47
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l173 : List Nat := [CFSG.KD.Fi24Tc.Pc.v167, CFSG.KD.Fi24Tc.Pc.v168, CFSG.KD.Fi24Tc.Pc.v169, CFSG.KD.Fi24Tc.Pc.v170, CFSG.KD.Fi24Tc.Pc.v171, CFSG.KD.Fi24Tc.Pc.v172]
theorem CFSG.KD.Fi24Tc.Pc.p171 : Nat.beq (runC AR SD 167 (ckL CFSG.KD.Fi24Tc.Pc.l173) 2 171 CFSG.KD.Fi24Tc.Pc.l171) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f28 : Nat.beq (runC AR SD 167 (finC AR SD (nat_lit 28) 167 175) 2 173 CFSG.KD.Fi24Tc.Pc.l173) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk28 : chk (nat_lit 28) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 28) (lo := 167) (hi := 175) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 169) CFSG.KD.Fi24Tc.Pc.p167 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 171) CFSG.KD.Fi24Tc.Pc.p169 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 173) CFSG.KD.Fi24Tc.Pc.p171 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f28

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v175 : Nat := CFSG.KD.Fi24Tc.KV1 48
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v176 : Nat := CFSG.KD.Fi24Tc.KV1 49
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l177 : List Nat := [CFSG.KD.Fi24Tc.Pc.v175, CFSG.KD.Fi24Tc.Pc.v176]
theorem CFSG.KD.Fi24Tc.Pc.p175 : Nat.beq (runC AR SD 175 (ckL CFSG.KD.Fi24Tc.Pc.l177) 2 175 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v177 : Nat := CFSG.KD.Fi24Tc.KV1 50
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v178 : Nat := CFSG.KD.Fi24Tc.KV1 51
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l179 : List Nat := [CFSG.KD.Fi24Tc.Pc.v175, CFSG.KD.Fi24Tc.Pc.v176, CFSG.KD.Fi24Tc.Pc.v177, CFSG.KD.Fi24Tc.Pc.v178]
theorem CFSG.KD.Fi24Tc.Pc.p177 : Nat.beq (runC AR SD 175 (ckL CFSG.KD.Fi24Tc.Pc.l179) 2 177 CFSG.KD.Fi24Tc.Pc.l177) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v179 : Nat := CFSG.KD.Fi24Tc.KV1 52
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v180 : Nat := CFSG.KD.Fi24Tc.KV1 53
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l181 : List Nat := [CFSG.KD.Fi24Tc.Pc.v175, CFSG.KD.Fi24Tc.Pc.v176, CFSG.KD.Fi24Tc.Pc.v177, CFSG.KD.Fi24Tc.Pc.v178, CFSG.KD.Fi24Tc.Pc.v179, CFSG.KD.Fi24Tc.Pc.v180]
theorem CFSG.KD.Fi24Tc.Pc.p179 : Nat.beq (runC AR SD 175 (ckL CFSG.KD.Fi24Tc.Pc.l181) 2 179 CFSG.KD.Fi24Tc.Pc.l179) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f29 : Nat.beq (runC AR SD 175 (finC AR SD (nat_lit 29) 175 182) 1 181 CFSG.KD.Fi24Tc.Pc.l181) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk29 : chk (nat_lit 29) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 29) (lo := 175) (hi := 182) (m := 7) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 7) (m2 := 5) (j2 := 177) CFSG.KD.Fi24Tc.Pc.p175 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 179) CFSG.KD.Fi24Tc.Pc.p177 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 181) CFSG.KD.Fi24Tc.Pc.p179 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f29

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v182 : Nat := CFSG.KD.Fi24Tc.KV1 96
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v183 : Nat := CFSG.KD.Fi24Tc.KV1 97
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l184 : List Nat := [CFSG.KD.Fi24Tc.Pc.v182, CFSG.KD.Fi24Tc.Pc.v183]
theorem CFSG.KD.Fi24Tc.Pc.p182 : Nat.beq (runC AR SD 182 (ckL CFSG.KD.Fi24Tc.Pc.l184) 2 182 []) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f30 : Nat.beq (runC AR SD 182 (finC AR SD (nat_lit 30) 182 185) 1 184 CFSG.KD.Fi24Tc.Pc.l184) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk30 : chk (nat_lit 30) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 30) (lo := 182) (hi := 185) (m := 3) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_seq (m := 3) (m2 := 1) (j2 := 184) CFSG.KD.Fi24Tc.Pc.p182 rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f30

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a185_3 : Nat := CFSG.KD.Fi24Tc.KV1 54
theorem CFSG.KD.Fi24Tc.Pc.q185_3 : Nat.beq (powTop AR.mul (getV AR SD 185 [] (SD.na.getD 185 0)) (SD.nk.getD 185 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a185_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a185_2 : Nat := CFSG.KD.Fi24Tc.KV1 55
theorem CFSG.KD.Fi24Tc.Pc.q185_2 : Nat.beq (powTop AR.mul (getV AR SD 185 [] (SD.na.getD 185 0)) (SD.nk.getD 185 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a185_2) 1 CFSG.KD.Fi24Tc.Pc.a185_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a185_1 : Nat := CFSG.KD.Fi24Tc.KV1 56
theorem CFSG.KD.Fi24Tc.Pc.q185_1 : Nat.beq (powTop AR.mul (getV AR SD 185 [] (SD.na.getD 185 0)) (SD.nk.getD 185 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a185_1) 1 CFSG.KD.Fi24Tc.Pc.a185_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v185 : Nat := CFSG.KD.Fi24Tc.KV1 57
theorem CFSG.KD.Fi24Tc.Pc.r185 : Nat.beq (powR AR.mul AR.one (getV AR SD 185 [] (SD.na.getD 185 0)) (SD.nk.getD 185 1) 1 CFSG.KD.Fi24Tc.Pc.a185_1 true) CFSG.KD.Fi24Tc.Pc.v185 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l186 : List Nat := [CFSG.KD.Fi24Tc.Pc.v185]
theorem CFSG.KD.Fi24Tc.Pc.f31 : Nat.beq (runC AR SD 185 (finC AR SD (nat_lit 31) 185 188) 2 186 CFSG.KD.Fi24Tc.Pc.l186) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk31 : chk (nat_lit 31) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 31) (lo := 185) (hi := 188) (m := 3) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 3) (m2 := 2) (j2 := 186) (Lr := CFSG.KD.Fi24Tc.Pc.l186) ((nodeV_pow (R := AR) (D := SD) (lo := 185) (L := []) (j := 185) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 185 [] (SD.na.getD 185 0)) (SD.nk.getD 185 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q185_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q185_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q185_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r185)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f31

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v188 : Nat := CFSG.KD.Fi24Tc.KV1 58
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v189 : Nat := CFSG.KD.Fi24Tc.KV1 59
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l190 : List Nat := [CFSG.KD.Fi24Tc.Pc.v188, CFSG.KD.Fi24Tc.Pc.v189]
theorem CFSG.KD.Fi24Tc.Pc.p188 : Nat.beq (runC AR SD 188 (ckL CFSG.KD.Fi24Tc.Pc.l190) 2 188 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v190 : Nat := CFSG.KD.Fi24Tc.KV1 60
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v191 : Nat := CFSG.KD.Fi24Tc.KV1 61
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l192 : List Nat := [CFSG.KD.Fi24Tc.Pc.v188, CFSG.KD.Fi24Tc.Pc.v189, CFSG.KD.Fi24Tc.Pc.v190, CFSG.KD.Fi24Tc.Pc.v191]
theorem CFSG.KD.Fi24Tc.Pc.p190 : Nat.beq (runC AR SD 188 (ckL CFSG.KD.Fi24Tc.Pc.l192) 2 190 CFSG.KD.Fi24Tc.Pc.l190) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v192 : Nat := CFSG.KD.Fi24Tc.KV1 62
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v193 : Nat := CFSG.KD.Fi24Tc.KV1 63
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l194 : List Nat := [CFSG.KD.Fi24Tc.Pc.v188, CFSG.KD.Fi24Tc.Pc.v189, CFSG.KD.Fi24Tc.Pc.v190, CFSG.KD.Fi24Tc.Pc.v191, CFSG.KD.Fi24Tc.Pc.v192, CFSG.KD.Fi24Tc.Pc.v193]
theorem CFSG.KD.Fi24Tc.Pc.p192 : Nat.beq (runC AR SD 188 (ckL CFSG.KD.Fi24Tc.Pc.l194) 2 192 CFSG.KD.Fi24Tc.Pc.l192) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f32 : Nat.beq (runC AR SD 188 (finC AR SD (nat_lit 32) 188 196) 2 194 CFSG.KD.Fi24Tc.Pc.l194) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk32 : chk (nat_lit 32) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 32) (lo := 188) (hi := 196) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 190) CFSG.KD.Fi24Tc.Pc.p188 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 192) CFSG.KD.Fi24Tc.Pc.p190 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 194) CFSG.KD.Fi24Tc.Pc.p192 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f32

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v196 : Nat := CFSG.KD.Fi24Tc.KV1 64
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v197 : Nat := CFSG.KD.Fi24Tc.KV1 65
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l198 : List Nat := [CFSG.KD.Fi24Tc.Pc.v196, CFSG.KD.Fi24Tc.Pc.v197]
theorem CFSG.KD.Fi24Tc.Pc.p196 : Nat.beq (runC AR SD 196 (ckL CFSG.KD.Fi24Tc.Pc.l198) 2 196 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v198 : Nat := CFSG.KD.Fi24Tc.KV1 66
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v199 : Nat := CFSG.KD.Fi24Tc.KV1 67
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l200 : List Nat := [CFSG.KD.Fi24Tc.Pc.v196, CFSG.KD.Fi24Tc.Pc.v197, CFSG.KD.Fi24Tc.Pc.v198, CFSG.KD.Fi24Tc.Pc.v199]
theorem CFSG.KD.Fi24Tc.Pc.p198 : Nat.beq (runC AR SD 196 (ckL CFSG.KD.Fi24Tc.Pc.l200) 2 198 CFSG.KD.Fi24Tc.Pc.l198) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f33 : Nat.beq (runC AR SD 196 (finC AR SD (nat_lit 33) 196 202) 2 200 CFSG.KD.Fi24Tc.Pc.l200) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk33 : chk (nat_lit 33) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 33) (lo := 196) (hi := 202) (m := 6) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 6) (m2 := 4) (j2 := 198) CFSG.KD.Fi24Tc.Pc.p196 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 200) CFSG.KD.Fi24Tc.Pc.p198 rfl rfl)))).trans CFSG.KD.Fi24Tc.Pc.f33

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a202_3 : Nat := CFSG.KD.Fi24Tc.KV1 68
theorem CFSG.KD.Fi24Tc.Pc.q202_3 : Nat.beq (powTop AR.mul (getV AR SD 202 [] (SD.na.getD 202 0)) (SD.nk.getD 202 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a202_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a202_2 : Nat := CFSG.KD.Fi24Tc.KV1 69
theorem CFSG.KD.Fi24Tc.Pc.q202_2 : Nat.beq (powTop AR.mul (getV AR SD 202 [] (SD.na.getD 202 0)) (SD.nk.getD 202 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a202_2) 1 CFSG.KD.Fi24Tc.Pc.a202_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a202_1 : Nat := CFSG.KD.Fi24Tc.KV1 70
theorem CFSG.KD.Fi24Tc.Pc.q202_1 : Nat.beq (powTop AR.mul (getV AR SD 202 [] (SD.na.getD 202 0)) (SD.nk.getD 202 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a202_1) 1 CFSG.KD.Fi24Tc.Pc.a202_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v202 : Nat := CFSG.KD.Fi24Tc.KV1 71
theorem CFSG.KD.Fi24Tc.Pc.r202 : Nat.beq (powR AR.mul AR.one (getV AR SD 202 [] (SD.na.getD 202 0)) (SD.nk.getD 202 1) 1 CFSG.KD.Fi24Tc.Pc.a202_1 true) CFSG.KD.Fi24Tc.Pc.v202 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l203 : List Nat := [CFSG.KD.Fi24Tc.Pc.v202]
theorem CFSG.KD.Fi24Tc.Pc.f34 : Nat.beq (runC AR SD 202 (finC AR SD (nat_lit 34) 202 204) 1 203 CFSG.KD.Fi24Tc.Pc.l203) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk34 : chk (nat_lit 34) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 34) (lo := 202) (hi := 204) (m := 2) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 2) (m2 := 1) (j2 := 203) (Lr := CFSG.KD.Fi24Tc.Pc.l203) ((nodeV_pow (R := AR) (D := SD) (lo := 202) (L := []) (j := 202) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 202 [] (SD.na.getD 202 0)) (SD.nk.getD 202 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q202_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q202_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q202_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r202)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f34

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v204 : Nat := CFSG.KD.Fi24Tc.KV1 72
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v205 : Nat := CFSG.KD.Fi24Tc.KV1 73
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l206 : List Nat := [CFSG.KD.Fi24Tc.Pc.v204, CFSG.KD.Fi24Tc.Pc.v205]
theorem CFSG.KD.Fi24Tc.Pc.p204 : Nat.beq (runC AR SD 204 (ckL CFSG.KD.Fi24Tc.Pc.l206) 2 204 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v206 : Nat := CFSG.KD.Fi24Tc.KV1 74
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v207 : Nat := CFSG.KD.Fi24Tc.KV1 75
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l208 : List Nat := [CFSG.KD.Fi24Tc.Pc.v204, CFSG.KD.Fi24Tc.Pc.v205, CFSG.KD.Fi24Tc.Pc.v206, CFSG.KD.Fi24Tc.Pc.v207]
theorem CFSG.KD.Fi24Tc.Pc.p206 : Nat.beq (runC AR SD 204 (ckL CFSG.KD.Fi24Tc.Pc.l208) 2 206 CFSG.KD.Fi24Tc.Pc.l206) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v208 : Nat := CFSG.KD.Fi24Tc.KV1 76
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v209 : Nat := CFSG.KD.Fi24Tc.KV1 77
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l210 : List Nat := [CFSG.KD.Fi24Tc.Pc.v204, CFSG.KD.Fi24Tc.Pc.v205, CFSG.KD.Fi24Tc.Pc.v206, CFSG.KD.Fi24Tc.Pc.v207, CFSG.KD.Fi24Tc.Pc.v208, CFSG.KD.Fi24Tc.Pc.v209]
theorem CFSG.KD.Fi24Tc.Pc.p208 : Nat.beq (runC AR SD 204 (ckL CFSG.KD.Fi24Tc.Pc.l210) 2 208 CFSG.KD.Fi24Tc.Pc.l208) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f35 : Nat.beq (runC AR SD 204 (finC AR SD (nat_lit 35) 204 212) 2 210 CFSG.KD.Fi24Tc.Pc.l210) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk35 : chk (nat_lit 35) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 35) (lo := 204) (hi := 212) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 206) CFSG.KD.Fi24Tc.Pc.p204 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 208) CFSG.KD.Fi24Tc.Pc.p206 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 210) CFSG.KD.Fi24Tc.Pc.p208 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f35

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v212 : Nat := CFSG.KD.Fi24Tc.KV1 78
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v213 : Nat := CFSG.KD.Fi24Tc.KV1 79
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l214 : List Nat := [CFSG.KD.Fi24Tc.Pc.v212, CFSG.KD.Fi24Tc.Pc.v213]
theorem CFSG.KD.Fi24Tc.Pc.p212 : Nat.beq (runC AR SD 212 (ckL CFSG.KD.Fi24Tc.Pc.l214) 2 212 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v214 : Nat := CFSG.KD.Fi24Tc.KV1 80
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l215 : List Nat := [CFSG.KD.Fi24Tc.Pc.v212, CFSG.KD.Fi24Tc.Pc.v213, CFSG.KD.Fi24Tc.Pc.v214]
theorem CFSG.KD.Fi24Tc.Pc.p214 : Nat.beq (runC AR SD 212 (ckL CFSG.KD.Fi24Tc.Pc.l215) 1 214 CFSG.KD.Fi24Tc.Pc.l214) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a215_1 : Nat := CFSG.KD.Fi24Tc.KV1 81
theorem CFSG.KD.Fi24Tc.Pc.q215_1 : Nat.beq (powTop AR.mul (getV AR SD 212 CFSG.KD.Fi24Tc.Pc.l215 (SD.na.getD 215 0)) (SD.nk.getD 215 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a215_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v215 : Nat := CFSG.KD.Fi24Tc.KV1 82
theorem CFSG.KD.Fi24Tc.Pc.r215 : Nat.beq (powR AR.mul AR.one (getV AR SD 212 CFSG.KD.Fi24Tc.Pc.l215 (SD.na.getD 215 0)) (SD.nk.getD 215 1) 1 CFSG.KD.Fi24Tc.Pc.a215_1 true) CFSG.KD.Fi24Tc.Pc.v215 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l216 : List Nat := [CFSG.KD.Fi24Tc.Pc.v212, CFSG.KD.Fi24Tc.Pc.v213, CFSG.KD.Fi24Tc.Pc.v214, CFSG.KD.Fi24Tc.Pc.v215]
theorem CFSG.KD.Fi24Tc.Pc.f36 : Nat.beq (runC AR SD 212 (finC AR SD (nat_lit 36) 212 217) 1 216 CFSG.KD.Fi24Tc.Pc.l216) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk36 : chk (nat_lit 36) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 36) (lo := 212) (hi := 217) (m := 5) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 5) (m2 := 3) (j2 := 214) CFSG.KD.Fi24Tc.Pc.p212 rfl rfl).trans ((runC_seq (m := 3) (m2 := 2) (j2 := 215) CFSG.KD.Fi24Tc.Pc.p214 rfl rfl).trans (runC_node (m := 2) (m2 := 1) (j2 := 216) (Lr := CFSG.KD.Fi24Tc.Pc.l216) ((nodeV_pow (R := AR) (D := SD) (lo := 212) (L := CFSG.KD.Fi24Tc.Pc.l215) (j := 215) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 212 CFSG.KD.Fi24Tc.Pc.l215 (SD.na.getD 215 0)) (SD.nk.getD 215 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q215_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r215)))) (by quickRfl) rfl rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f36

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a217_3 : Nat := CFSG.KD.Fi24Tc.KV1 83
theorem CFSG.KD.Fi24Tc.Pc.q217_3 : Nat.beq (powTop AR.mul (getV AR SD 217 [] (SD.na.getD 217 0)) (SD.nk.getD 217 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a217_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a217_2 : Nat := CFSG.KD.Fi24Tc.KV1 84
theorem CFSG.KD.Fi24Tc.Pc.q217_2 : Nat.beq (powTop AR.mul (getV AR SD 217 [] (SD.na.getD 217 0)) (SD.nk.getD 217 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a217_2) 1 CFSG.KD.Fi24Tc.Pc.a217_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a217_1 : Nat := CFSG.KD.Fi24Tc.KV1 85
theorem CFSG.KD.Fi24Tc.Pc.q217_1 : Nat.beq (powTop AR.mul (getV AR SD 217 [] (SD.na.getD 217 0)) (SD.nk.getD 217 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a217_1) 1 CFSG.KD.Fi24Tc.Pc.a217_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v217 : Nat := CFSG.KD.Fi24Tc.KV1 86
theorem CFSG.KD.Fi24Tc.Pc.r217 : Nat.beq (powR AR.mul AR.one (getV AR SD 217 [] (SD.na.getD 217 0)) (SD.nk.getD 217 1) 1 CFSG.KD.Fi24Tc.Pc.a217_1 true) CFSG.KD.Fi24Tc.Pc.v217 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l218 : List Nat := [CFSG.KD.Fi24Tc.Pc.v217]
theorem CFSG.KD.Fi24Tc.Pc.f37 : Nat.beq (runC AR SD 217 (finC AR SD (nat_lit 37) 217 220) 2 218 CFSG.KD.Fi24Tc.Pc.l218) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk37 : chk (nat_lit 37) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 37) (lo := 217) (hi := 220) (m := 3) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 3) (m2 := 2) (j2 := 218) (Lr := CFSG.KD.Fi24Tc.Pc.l218) ((nodeV_pow (R := AR) (D := SD) (lo := 217) (L := []) (j := 217) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 217 [] (SD.na.getD 217 0)) (SD.nk.getD 217 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q217_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q217_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q217_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r217)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f37

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v220 : Nat := CFSG.KD.Fi24Tc.KV1 87
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l221 : List Nat := [CFSG.KD.Fi24Tc.Pc.v220]
theorem CFSG.KD.Fi24Tc.Pc.p220 : Nat.beq (runC AR SD 220 (ckL CFSG.KD.Fi24Tc.Pc.l221) 1 220 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a221_1 : Nat := CFSG.KD.Fi24Tc.KV1 88
theorem CFSG.KD.Fi24Tc.Pc.q221_1 : Nat.beq (powTop AR.mul (getV AR SD 220 CFSG.KD.Fi24Tc.Pc.l221 (SD.na.getD 221 0)) (SD.nk.getD 221 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a221_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v221 : Nat := CFSG.KD.Fi24Tc.KV1 89
theorem CFSG.KD.Fi24Tc.Pc.r221 : Nat.beq (powR AR.mul AR.one (getV AR SD 220 CFSG.KD.Fi24Tc.Pc.l221 (SD.na.getD 221 0)) (SD.nk.getD 221 1) 1 CFSG.KD.Fi24Tc.Pc.a221_1 true) CFSG.KD.Fi24Tc.Pc.v221 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l222 : List Nat := [CFSG.KD.Fi24Tc.Pc.v220, CFSG.KD.Fi24Tc.Pc.v221]
theorem CFSG.KD.Fi24Tc.Pc.f38 : Nat.beq (runC AR SD 220 (finC AR SD (nat_lit 38) 220 224) 2 222 CFSG.KD.Fi24Tc.Pc.l222) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk38 : chk (nat_lit 38) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 38) (lo := 220) (hi := 224) (m := 4) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 4) (m2 := 3) (j2 := 221) CFSG.KD.Fi24Tc.Pc.p220 rfl rfl).trans (runC_node (m := 3) (m2 := 2) (j2 := 222) (Lr := CFSG.KD.Fi24Tc.Pc.l222) ((nodeV_pow (R := AR) (D := SD) (lo := 220) (L := CFSG.KD.Fi24Tc.Pc.l221) (j := 221) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 220 CFSG.KD.Fi24Tc.Pc.l221 (SD.na.getD 221 0)) (SD.nk.getD 221 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q221_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r221)))) (by quickRfl) rfl rfl rfl)))).trans CFSG.KD.Fi24Tc.Pc.f38

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a224_1 : Nat := CFSG.KD.Fi24Tc.KV1 90
theorem CFSG.KD.Fi24Tc.Pc.q224_1 : Nat.beq (powTop AR.mul (getV AR SD 224 [] (SD.na.getD 224 0)) (SD.nk.getD 224 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a224_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v224 : Nat := CFSG.KD.Fi24Tc.KV1 91
theorem CFSG.KD.Fi24Tc.Pc.r224 : Nat.beq (powR AR.mul AR.one (getV AR SD 224 [] (SD.na.getD 224 0)) (SD.nk.getD 224 1) 1 CFSG.KD.Fi24Tc.Pc.a224_1 true) CFSG.KD.Fi24Tc.Pc.v224 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l225 : List Nat := [CFSG.KD.Fi24Tc.Pc.v224]
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v225 : Nat := CFSG.KD.Fi24Tc.KV1 92
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v226 : Nat := CFSG.KD.Fi24Tc.KV1 93
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l227 : List Nat := [CFSG.KD.Fi24Tc.Pc.v224, CFSG.KD.Fi24Tc.Pc.v225, CFSG.KD.Fi24Tc.Pc.v226]
theorem CFSG.KD.Fi24Tc.Pc.p225 : Nat.beq (runC AR SD 224 (ckL CFSG.KD.Fi24Tc.Pc.l227) 2 225 CFSG.KD.Fi24Tc.Pc.l225) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v227 : Nat := CFSG.KD.Fi24Tc.KV1 94
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v228 : Nat := CFSG.KD.Fi24Tc.KV1 95
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l229 : List Nat := [CFSG.KD.Fi24Tc.Pc.v224, CFSG.KD.Fi24Tc.Pc.v225, CFSG.KD.Fi24Tc.Pc.v226, CFSG.KD.Fi24Tc.Pc.v227, CFSG.KD.Fi24Tc.Pc.v228]
theorem CFSG.KD.Fi24Tc.Pc.p227 : Nat.beq (runC AR SD 224 (ckL CFSG.KD.Fi24Tc.Pc.l229) 2 227 CFSG.KD.Fi24Tc.Pc.l227) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f39 : Nat.beq (runC AR SD 224 (finC AR SD (nat_lit 39) 224 230) 1 229 CFSG.KD.Fi24Tc.Pc.l229) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk39 : chk (nat_lit 39) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 39) (lo := 224) (hi := 230) (m := 6) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 6) (m2 := 5) (j2 := 225) (Lr := CFSG.KD.Fi24Tc.Pc.l225) ((nodeV_pow (R := AR) (D := SD) (lo := 224) (L := []) (j := 224) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 224 [] (SD.na.getD 224 0)) (SD.nk.getD 224 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q224_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r224)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 227) CFSG.KD.Fi24Tc.Pc.p225 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 229) CFSG.KD.Fi24Tc.Pc.p227 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f39

end
