module

public import Certificates.Kernel.Sporadic.Fi24Tc.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Tc KV2 "Certificates/Kernel/Sporadic/Fi24Tc/data/v2.bin" 152491 4 17688956 1752857847348757872

public section

open CFSG.KD.Fi24Tc CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v230 : Nat := CFSG.KD.Fi24Tc.KV2 0
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v231 : Nat := CFSG.KD.Fi24Tc.KV2 1
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l232 : List Nat := [CFSG.KD.Fi24Tc.Pc.v230, CFSG.KD.Fi24Tc.Pc.v231]
theorem CFSG.KD.Fi24Tc.Pc.p230 : Nat.beq (runC AR SD 230 (ckL CFSG.KD.Fi24Tc.Pc.l232) 2 230 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v232 : Nat := CFSG.KD.Fi24Tc.KV2 2
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v233 : Nat := CFSG.KD.Fi24Tc.KV2 3
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l234 : List Nat := [CFSG.KD.Fi24Tc.Pc.v230, CFSG.KD.Fi24Tc.Pc.v231, CFSG.KD.Fi24Tc.Pc.v232, CFSG.KD.Fi24Tc.Pc.v233]
theorem CFSG.KD.Fi24Tc.Pc.p232 : Nat.beq (runC AR SD 230 (ckL CFSG.KD.Fi24Tc.Pc.l234) 2 232 CFSG.KD.Fi24Tc.Pc.l232) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v234 : Nat := CFSG.KD.Fi24Tc.KV2 4
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v235 : Nat := CFSG.KD.Fi24Tc.KV2 5
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l236 : List Nat := [CFSG.KD.Fi24Tc.Pc.v230, CFSG.KD.Fi24Tc.Pc.v231, CFSG.KD.Fi24Tc.Pc.v232, CFSG.KD.Fi24Tc.Pc.v233, CFSG.KD.Fi24Tc.Pc.v234, CFSG.KD.Fi24Tc.Pc.v235]
theorem CFSG.KD.Fi24Tc.Pc.p234 : Nat.beq (runC AR SD 230 (ckL CFSG.KD.Fi24Tc.Pc.l236) 2 234 CFSG.KD.Fi24Tc.Pc.l234) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f40 : Nat.beq (runC AR SD 230 (finC AR SD (nat_lit 40) 230 238) 2 236 CFSG.KD.Fi24Tc.Pc.l236) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk40 : chk (nat_lit 40) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 40) (lo := 230) (hi := 238) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 232) CFSG.KD.Fi24Tc.Pc.p230 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 234) CFSG.KD.Fi24Tc.Pc.p232 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 236) CFSG.KD.Fi24Tc.Pc.p234 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f40

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v238 : Nat := CFSG.KD.Fi24Tc.KV2 6
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v239 : Nat := CFSG.KD.Fi24Tc.KV2 7
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l240 : List Nat := [CFSG.KD.Fi24Tc.Pc.v238, CFSG.KD.Fi24Tc.Pc.v239]
theorem CFSG.KD.Fi24Tc.Pc.p238 : Nat.beq (runC AR SD 238 (ckL CFSG.KD.Fi24Tc.Pc.l240) 2 238 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v240 : Nat := CFSG.KD.Fi24Tc.KV2 8
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v241 : Nat := CFSG.KD.Fi24Tc.KV2 9
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l242 : List Nat := [CFSG.KD.Fi24Tc.Pc.v238, CFSG.KD.Fi24Tc.Pc.v239, CFSG.KD.Fi24Tc.Pc.v240, CFSG.KD.Fi24Tc.Pc.v241]
theorem CFSG.KD.Fi24Tc.Pc.p240 : Nat.beq (runC AR SD 238 (ckL CFSG.KD.Fi24Tc.Pc.l242) 2 240 CFSG.KD.Fi24Tc.Pc.l240) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v242 : Nat := CFSG.KD.Fi24Tc.KV2 10
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v243 : Nat := CFSG.KD.Fi24Tc.KV2 11
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l244 : List Nat := [CFSG.KD.Fi24Tc.Pc.v238, CFSG.KD.Fi24Tc.Pc.v239, CFSG.KD.Fi24Tc.Pc.v240, CFSG.KD.Fi24Tc.Pc.v241, CFSG.KD.Fi24Tc.Pc.v242, CFSG.KD.Fi24Tc.Pc.v243]
theorem CFSG.KD.Fi24Tc.Pc.p242 : Nat.beq (runC AR SD 238 (ckL CFSG.KD.Fi24Tc.Pc.l244) 2 242 CFSG.KD.Fi24Tc.Pc.l242) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f41 : Nat.beq (runC AR SD 238 (finC AR SD (nat_lit 41) 238 245) 1 244 CFSG.KD.Fi24Tc.Pc.l244) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk41 : chk (nat_lit 41) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 41) (lo := 238) (hi := 245) (m := 7) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 7) (m2 := 5) (j2 := 240) CFSG.KD.Fi24Tc.Pc.p238 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 242) CFSG.KD.Fi24Tc.Pc.p240 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 244) CFSG.KD.Fi24Tc.Pc.p242 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f41

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a245_1 : Nat := CFSG.KD.Fi24Tc.KV2 12
theorem CFSG.KD.Fi24Tc.Pc.q245_1 : Nat.beq (powTop AR.mul (getV AR SD 245 [] (SD.na.getD 245 0)) (SD.nk.getD 245 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a245_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v245 : Nat := CFSG.KD.Fi24Tc.KV2 13
theorem CFSG.KD.Fi24Tc.Pc.r245 : Nat.beq (powR AR.mul AR.one (getV AR SD 245 [] (SD.na.getD 245 0)) (SD.nk.getD 245 1) 1 CFSG.KD.Fi24Tc.Pc.a245_1 true) CFSG.KD.Fi24Tc.Pc.v245 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l246 : List Nat := [CFSG.KD.Fi24Tc.Pc.v245]
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v246 : Nat := CFSG.KD.Fi24Tc.KV2 14
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v247 : Nat := CFSG.KD.Fi24Tc.KV2 15
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l248 : List Nat := [CFSG.KD.Fi24Tc.Pc.v245, CFSG.KD.Fi24Tc.Pc.v246, CFSG.KD.Fi24Tc.Pc.v247]
theorem CFSG.KD.Fi24Tc.Pc.p246 : Nat.beq (runC AR SD 245 (ckL CFSG.KD.Fi24Tc.Pc.l248) 2 246 CFSG.KD.Fi24Tc.Pc.l246) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v248 : Nat := CFSG.KD.Fi24Tc.KV2 16
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v249 : Nat := CFSG.KD.Fi24Tc.KV2 17
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l250 : List Nat := [CFSG.KD.Fi24Tc.Pc.v245, CFSG.KD.Fi24Tc.Pc.v246, CFSG.KD.Fi24Tc.Pc.v247, CFSG.KD.Fi24Tc.Pc.v248, CFSG.KD.Fi24Tc.Pc.v249]
theorem CFSG.KD.Fi24Tc.Pc.p248 : Nat.beq (runC AR SD 245 (ckL CFSG.KD.Fi24Tc.Pc.l250) 2 248 CFSG.KD.Fi24Tc.Pc.l248) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f42 : Nat.beq (runC AR SD 245 (finC AR SD (nat_lit 42) 245 251) 1 250 CFSG.KD.Fi24Tc.Pc.l250) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk42 : chk (nat_lit 42) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 42) (lo := 245) (hi := 251) (m := 6) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 6) (m2 := 5) (j2 := 246) (Lr := CFSG.KD.Fi24Tc.Pc.l246) ((nodeV_pow (R := AR) (D := SD) (lo := 245) (L := []) (j := 245) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 245 [] (SD.na.getD 245 0)) (SD.nk.getD 245 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q245_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r245)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 248) CFSG.KD.Fi24Tc.Pc.p246 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 250) CFSG.KD.Fi24Tc.Pc.p248 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f42

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v251 : Nat := CFSG.KD.Fi24Tc.KV2 18
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v252 : Nat := CFSG.KD.Fi24Tc.KV2 19
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l253 : List Nat := [CFSG.KD.Fi24Tc.Pc.v251, CFSG.KD.Fi24Tc.Pc.v252]
theorem CFSG.KD.Fi24Tc.Pc.p251 : Nat.beq (runC AR SD 251 (ckL CFSG.KD.Fi24Tc.Pc.l253) 2 251 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v253 : Nat := CFSG.KD.Fi24Tc.KV2 20
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v254 : Nat := CFSG.KD.Fi24Tc.KV2 21
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l255 : List Nat := [CFSG.KD.Fi24Tc.Pc.v251, CFSG.KD.Fi24Tc.Pc.v252, CFSG.KD.Fi24Tc.Pc.v253, CFSG.KD.Fi24Tc.Pc.v254]
theorem CFSG.KD.Fi24Tc.Pc.p253 : Nat.beq (runC AR SD 251 (ckL CFSG.KD.Fi24Tc.Pc.l255) 2 253 CFSG.KD.Fi24Tc.Pc.l253) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v255 : Nat := CFSG.KD.Fi24Tc.KV2 22
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v256 : Nat := CFSG.KD.Fi24Tc.KV2 23
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l257 : List Nat := [CFSG.KD.Fi24Tc.Pc.v251, CFSG.KD.Fi24Tc.Pc.v252, CFSG.KD.Fi24Tc.Pc.v253, CFSG.KD.Fi24Tc.Pc.v254, CFSG.KD.Fi24Tc.Pc.v255, CFSG.KD.Fi24Tc.Pc.v256]
theorem CFSG.KD.Fi24Tc.Pc.p255 : Nat.beq (runC AR SD 251 (ckL CFSG.KD.Fi24Tc.Pc.l257) 2 255 CFSG.KD.Fi24Tc.Pc.l255) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f43 : Nat.beq (runC AR SD 251 (finC AR SD (nat_lit 43) 251 258) 1 257 CFSG.KD.Fi24Tc.Pc.l257) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk43 : chk (nat_lit 43) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 43) (lo := 251) (hi := 258) (m := 7) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 7) (m2 := 5) (j2 := 253) CFSG.KD.Fi24Tc.Pc.p251 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 255) CFSG.KD.Fi24Tc.Pc.p253 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 257) CFSG.KD.Fi24Tc.Pc.p255 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f43

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v258 : Nat := CFSG.KD.Fi24Tc.KV2 24
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l259 : List Nat := [CFSG.KD.Fi24Tc.Pc.v258]
theorem CFSG.KD.Fi24Tc.Pc.p258 : Nat.beq (runC AR SD 258 (ckL CFSG.KD.Fi24Tc.Pc.l259) 1 258 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v259 : Nat := CFSG.KD.Fi24Tc.KV2 25
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v260 : Nat := CFSG.KD.Fi24Tc.KV2 26
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l261 : List Nat := [CFSG.KD.Fi24Tc.Pc.v258, CFSG.KD.Fi24Tc.Pc.v259, CFSG.KD.Fi24Tc.Pc.v260]
theorem CFSG.KD.Fi24Tc.Pc.p259 : Nat.beq (runC AR SD 258 (ckL CFSG.KD.Fi24Tc.Pc.l261) 2 259 CFSG.KD.Fi24Tc.Pc.l259) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v261 : Nat := CFSG.KD.Fi24Tc.KV2 27
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v262 : Nat := CFSG.KD.Fi24Tc.KV2 28
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l263 : List Nat := [CFSG.KD.Fi24Tc.Pc.v258, CFSG.KD.Fi24Tc.Pc.v259, CFSG.KD.Fi24Tc.Pc.v260, CFSG.KD.Fi24Tc.Pc.v261, CFSG.KD.Fi24Tc.Pc.v262]
theorem CFSG.KD.Fi24Tc.Pc.p261 : Nat.beq (runC AR SD 258 (ckL CFSG.KD.Fi24Tc.Pc.l263) 2 261 CFSG.KD.Fi24Tc.Pc.l261) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f44 : Nat.beq (runC AR SD 258 (finC AR SD (nat_lit 44) 258 264) 1 263 CFSG.KD.Fi24Tc.Pc.l263) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk44 : chk (nat_lit 44) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 44) (lo := 258) (hi := 264) (m := 6) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 6) (m2 := 5) (j2 := 259) CFSG.KD.Fi24Tc.Pc.p258 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 261) CFSG.KD.Fi24Tc.Pc.p259 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 263) CFSG.KD.Fi24Tc.Pc.p261 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f44

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a264_2 : Nat := CFSG.KD.Fi24Tc.KV2 29
theorem CFSG.KD.Fi24Tc.Pc.q264_2 : Nat.beq (powTop AR.mul (getV AR SD 264 [] (SD.na.getD 264 0)) (SD.nk.getD 264 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a264_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a264_1 : Nat := CFSG.KD.Fi24Tc.KV2 30
theorem CFSG.KD.Fi24Tc.Pc.q264_1 : Nat.beq (powTop AR.mul (getV AR SD 264 [] (SD.na.getD 264 0)) (SD.nk.getD 264 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a264_1) 1 CFSG.KD.Fi24Tc.Pc.a264_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v264 : Nat := CFSG.KD.Fi24Tc.KV2 31
theorem CFSG.KD.Fi24Tc.Pc.r264 : Nat.beq (powR AR.mul AR.one (getV AR SD 264 [] (SD.na.getD 264 0)) (SD.nk.getD 264 1) 1 CFSG.KD.Fi24Tc.Pc.a264_1 true) CFSG.KD.Fi24Tc.Pc.v264 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l265 : List Nat := [CFSG.KD.Fi24Tc.Pc.v264]
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v265 : Nat := CFSG.KD.Fi24Tc.KV2 32
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v266 : Nat := CFSG.KD.Fi24Tc.KV2 33
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l267 : List Nat := [CFSG.KD.Fi24Tc.Pc.v264, CFSG.KD.Fi24Tc.Pc.v265, CFSG.KD.Fi24Tc.Pc.v266]
theorem CFSG.KD.Fi24Tc.Pc.p265 : Nat.beq (runC AR SD 264 (ckL CFSG.KD.Fi24Tc.Pc.l267) 2 265 CFSG.KD.Fi24Tc.Pc.l265) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f45 : Nat.beq (runC AR SD 264 (finC AR SD (nat_lit 45) 264 268) 1 267 CFSG.KD.Fi24Tc.Pc.l267) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk45 : chk (nat_lit 45) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 45) (lo := 264) (hi := 268) (m := 4) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 4) (m2 := 3) (j2 := 265) (Lr := CFSG.KD.Fi24Tc.Pc.l265) ((nodeV_pow (R := AR) (D := SD) (lo := 264) (L := []) (j := 264) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 264 [] (SD.na.getD 264 0)) (SD.nk.getD 264 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q264_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q264_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r264))))) (by quickRfl) rfl rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 267) CFSG.KD.Fi24Tc.Pc.p265 rfl rfl)))).trans CFSG.KD.Fi24Tc.Pc.f45

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v268 : Nat := CFSG.KD.Fi24Tc.KV2 34
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v269 : Nat := CFSG.KD.Fi24Tc.KV2 35
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l270 : List Nat := [CFSG.KD.Fi24Tc.Pc.v268, CFSG.KD.Fi24Tc.Pc.v269]
theorem CFSG.KD.Fi24Tc.Pc.p268 : Nat.beq (runC AR SD 268 (ckL CFSG.KD.Fi24Tc.Pc.l270) 2 268 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v270 : Nat := CFSG.KD.Fi24Tc.KV2 36
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v271 : Nat := CFSG.KD.Fi24Tc.KV2 37
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l272 : List Nat := [CFSG.KD.Fi24Tc.Pc.v268, CFSG.KD.Fi24Tc.Pc.v269, CFSG.KD.Fi24Tc.Pc.v270, CFSG.KD.Fi24Tc.Pc.v271]
theorem CFSG.KD.Fi24Tc.Pc.p270 : Nat.beq (runC AR SD 268 (ckL CFSG.KD.Fi24Tc.Pc.l272) 2 270 CFSG.KD.Fi24Tc.Pc.l270) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v272 : Nat := CFSG.KD.Fi24Tc.KV2 38
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v273 : Nat := CFSG.KD.Fi24Tc.KV2 39
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l274 : List Nat := [CFSG.KD.Fi24Tc.Pc.v268, CFSG.KD.Fi24Tc.Pc.v269, CFSG.KD.Fi24Tc.Pc.v270, CFSG.KD.Fi24Tc.Pc.v271, CFSG.KD.Fi24Tc.Pc.v272, CFSG.KD.Fi24Tc.Pc.v273]
theorem CFSG.KD.Fi24Tc.Pc.p272 : Nat.beq (runC AR SD 268 (ckL CFSG.KD.Fi24Tc.Pc.l274) 2 272 CFSG.KD.Fi24Tc.Pc.l272) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f46 : Nat.beq (runC AR SD 268 (finC AR SD (nat_lit 46) 268 276) 2 274 CFSG.KD.Fi24Tc.Pc.l274) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk46 : chk (nat_lit 46) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 46) (lo := 268) (hi := 276) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 270) CFSG.KD.Fi24Tc.Pc.p268 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 272) CFSG.KD.Fi24Tc.Pc.p270 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 274) CFSG.KD.Fi24Tc.Pc.p272 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f46

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v276 : Nat := CFSG.KD.Fi24Tc.KV2 40
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v277 : Nat := CFSG.KD.Fi24Tc.KV2 41
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l278 : List Nat := [CFSG.KD.Fi24Tc.Pc.v276, CFSG.KD.Fi24Tc.Pc.v277]
theorem CFSG.KD.Fi24Tc.Pc.p276 : Nat.beq (runC AR SD 276 (ckL CFSG.KD.Fi24Tc.Pc.l278) 2 276 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v278 : Nat := CFSG.KD.Fi24Tc.KV2 42
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v279 : Nat := CFSG.KD.Fi24Tc.KV2 43
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l280 : List Nat := [CFSG.KD.Fi24Tc.Pc.v276, CFSG.KD.Fi24Tc.Pc.v277, CFSG.KD.Fi24Tc.Pc.v278, CFSG.KD.Fi24Tc.Pc.v279]
theorem CFSG.KD.Fi24Tc.Pc.p278 : Nat.beq (runC AR SD 276 (ckL CFSG.KD.Fi24Tc.Pc.l280) 2 278 CFSG.KD.Fi24Tc.Pc.l278) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v280 : Nat := CFSG.KD.Fi24Tc.KV2 44
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v281 : Nat := CFSG.KD.Fi24Tc.KV2 45
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l282 : List Nat := [CFSG.KD.Fi24Tc.Pc.v276, CFSG.KD.Fi24Tc.Pc.v277, CFSG.KD.Fi24Tc.Pc.v278, CFSG.KD.Fi24Tc.Pc.v279, CFSG.KD.Fi24Tc.Pc.v280, CFSG.KD.Fi24Tc.Pc.v281]
theorem CFSG.KD.Fi24Tc.Pc.p280 : Nat.beq (runC AR SD 276 (ckL CFSG.KD.Fi24Tc.Pc.l282) 2 280 CFSG.KD.Fi24Tc.Pc.l280) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f47 : Nat.beq (runC AR SD 276 (finC AR SD (nat_lit 47) 276 284) 2 282 CFSG.KD.Fi24Tc.Pc.l282) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk47 : chk (nat_lit 47) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 47) (lo := 276) (hi := 284) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 278) CFSG.KD.Fi24Tc.Pc.p276 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 280) CFSG.KD.Fi24Tc.Pc.p278 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 282) CFSG.KD.Fi24Tc.Pc.p280 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f47

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a284_1 : Nat := CFSG.KD.Fi24Tc.KV2 46
theorem CFSG.KD.Fi24Tc.Pc.q284_1 : Nat.beq (powTop AR.mul (getV AR SD 284 [] (SD.na.getD 284 0)) (SD.nk.getD 284 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a284_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v284 : Nat := CFSG.KD.Fi24Tc.KV2 47
theorem CFSG.KD.Fi24Tc.Pc.r284 : Nat.beq (powR AR.mul AR.one (getV AR SD 284 [] (SD.na.getD 284 0)) (SD.nk.getD 284 1) 1 CFSG.KD.Fi24Tc.Pc.a284_1 true) CFSG.KD.Fi24Tc.Pc.v284 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l285 : List Nat := [CFSG.KD.Fi24Tc.Pc.v284]
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v285 : Nat := CFSG.KD.Fi24Tc.KV2 48
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l286 : List Nat := [CFSG.KD.Fi24Tc.Pc.v284, CFSG.KD.Fi24Tc.Pc.v285]
theorem CFSG.KD.Fi24Tc.Pc.p285 : Nat.beq (runC AR SD 284 (ckL CFSG.KD.Fi24Tc.Pc.l286) 1 285 CFSG.KD.Fi24Tc.Pc.l285) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v286 : Nat := CFSG.KD.Fi24Tc.KV2 49
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l287 : List Nat := [CFSG.KD.Fi24Tc.Pc.v284, CFSG.KD.Fi24Tc.Pc.v285, CFSG.KD.Fi24Tc.Pc.v286]
theorem CFSG.KD.Fi24Tc.Pc.p286 : Nat.beq (runC AR SD 284 (ckL CFSG.KD.Fi24Tc.Pc.l287) 1 286 CFSG.KD.Fi24Tc.Pc.l286) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f48 : Nat.beq (runC AR SD 284 (finC AR SD (nat_lit 48) 284 288) 1 287 CFSG.KD.Fi24Tc.Pc.l287) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk48 : chk (nat_lit 48) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 48) (lo := 284) (hi := 288) (m := 4) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 4) (m2 := 3) (j2 := 285) (Lr := CFSG.KD.Fi24Tc.Pc.l285) ((nodeV_pow (R := AR) (D := SD) (lo := 284) (L := []) (j := 284) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 284 [] (SD.na.getD 284 0)) (SD.nk.getD 284 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q284_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r284)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 3) (m2 := 2) (j2 := 286) CFSG.KD.Fi24Tc.Pc.p285 rfl rfl).trans (runC_seq (m := 2) (m2 := 1) (j2 := 287) CFSG.KD.Fi24Tc.Pc.p286 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f48

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v288 : Nat := CFSG.KD.Fi24Tc.KV2 50
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v289 : Nat := CFSG.KD.Fi24Tc.KV2 51
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l290 : List Nat := [CFSG.KD.Fi24Tc.Pc.v288, CFSG.KD.Fi24Tc.Pc.v289]
theorem CFSG.KD.Fi24Tc.Pc.p288 : Nat.beq (runC AR SD 288 (ckL CFSG.KD.Fi24Tc.Pc.l290) 2 288 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v290 : Nat := CFSG.KD.Fi24Tc.KV2 52
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v291 : Nat := CFSG.KD.Fi24Tc.KV2 53
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l292 : List Nat := [CFSG.KD.Fi24Tc.Pc.v288, CFSG.KD.Fi24Tc.Pc.v289, CFSG.KD.Fi24Tc.Pc.v290, CFSG.KD.Fi24Tc.Pc.v291]
theorem CFSG.KD.Fi24Tc.Pc.p290 : Nat.beq (runC AR SD 288 (ckL CFSG.KD.Fi24Tc.Pc.l292) 2 290 CFSG.KD.Fi24Tc.Pc.l290) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v292 : Nat := CFSG.KD.Fi24Tc.KV2 54
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v293 : Nat := CFSG.KD.Fi24Tc.KV2 55
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l294 : List Nat := [CFSG.KD.Fi24Tc.Pc.v288, CFSG.KD.Fi24Tc.Pc.v289, CFSG.KD.Fi24Tc.Pc.v290, CFSG.KD.Fi24Tc.Pc.v291, CFSG.KD.Fi24Tc.Pc.v292, CFSG.KD.Fi24Tc.Pc.v293]
theorem CFSG.KD.Fi24Tc.Pc.p292 : Nat.beq (runC AR SD 288 (ckL CFSG.KD.Fi24Tc.Pc.l294) 2 292 CFSG.KD.Fi24Tc.Pc.l292) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f49 : Nat.beq (runC AR SD 288 (finC AR SD (nat_lit 49) 288 296) 2 294 CFSG.KD.Fi24Tc.Pc.l294) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk49 : chk (nat_lit 49) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 49) (lo := 288) (hi := 296) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 290) CFSG.KD.Fi24Tc.Pc.p288 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 292) CFSG.KD.Fi24Tc.Pc.p290 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 294) CFSG.KD.Fi24Tc.Pc.p292 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f49

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v296 : Nat := CFSG.KD.Fi24Tc.KV2 56
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v297 : Nat := CFSG.KD.Fi24Tc.KV2 57
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l298 : List Nat := [CFSG.KD.Fi24Tc.Pc.v296, CFSG.KD.Fi24Tc.Pc.v297]
theorem CFSG.KD.Fi24Tc.Pc.p296 : Nat.beq (runC AR SD 296 (ckL CFSG.KD.Fi24Tc.Pc.l298) 2 296 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v298 : Nat := CFSG.KD.Fi24Tc.KV2 58
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v299 : Nat := CFSG.KD.Fi24Tc.KV2 59
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l300 : List Nat := [CFSG.KD.Fi24Tc.Pc.v296, CFSG.KD.Fi24Tc.Pc.v297, CFSG.KD.Fi24Tc.Pc.v298, CFSG.KD.Fi24Tc.Pc.v299]
theorem CFSG.KD.Fi24Tc.Pc.p298 : Nat.beq (runC AR SD 296 (ckL CFSG.KD.Fi24Tc.Pc.l300) 2 298 CFSG.KD.Fi24Tc.Pc.l298) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v300 : Nat := CFSG.KD.Fi24Tc.KV2 60
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v301 : Nat := CFSG.KD.Fi24Tc.KV2 61
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l302 : List Nat := [CFSG.KD.Fi24Tc.Pc.v296, CFSG.KD.Fi24Tc.Pc.v297, CFSG.KD.Fi24Tc.Pc.v298, CFSG.KD.Fi24Tc.Pc.v299, CFSG.KD.Fi24Tc.Pc.v300, CFSG.KD.Fi24Tc.Pc.v301]
theorem CFSG.KD.Fi24Tc.Pc.p300 : Nat.beq (runC AR SD 296 (ckL CFSG.KD.Fi24Tc.Pc.l302) 2 300 CFSG.KD.Fi24Tc.Pc.l300) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f50 : Nat.beq (runC AR SD 296 (finC AR SD (nat_lit 50) 296 304) 2 302 CFSG.KD.Fi24Tc.Pc.l302) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk50 : chk (nat_lit 50) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 50) (lo := 296) (hi := 304) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 298) CFSG.KD.Fi24Tc.Pc.p296 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 300) CFSG.KD.Fi24Tc.Pc.p298 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 302) CFSG.KD.Fi24Tc.Pc.p300 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f50

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v304 : Nat := CFSG.KD.Fi24Tc.KV2 62
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v305 : Nat := CFSG.KD.Fi24Tc.KV2 63
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l306 : List Nat := [CFSG.KD.Fi24Tc.Pc.v304, CFSG.KD.Fi24Tc.Pc.v305]
theorem CFSG.KD.Fi24Tc.Pc.p304 : Nat.beq (runC AR SD 304 (ckL CFSG.KD.Fi24Tc.Pc.l306) 2 304 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v306 : Nat := CFSG.KD.Fi24Tc.KV2 64
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v307 : Nat := CFSG.KD.Fi24Tc.KV2 65
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l308 : List Nat := [CFSG.KD.Fi24Tc.Pc.v304, CFSG.KD.Fi24Tc.Pc.v305, CFSG.KD.Fi24Tc.Pc.v306, CFSG.KD.Fi24Tc.Pc.v307]
theorem CFSG.KD.Fi24Tc.Pc.p306 : Nat.beq (runC AR SD 304 (ckL CFSG.KD.Fi24Tc.Pc.l308) 2 306 CFSG.KD.Fi24Tc.Pc.l306) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v308 : Nat := CFSG.KD.Fi24Tc.KV2 66
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v309 : Nat := CFSG.KD.Fi24Tc.KV2 67
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l310 : List Nat := [CFSG.KD.Fi24Tc.Pc.v304, CFSG.KD.Fi24Tc.Pc.v305, CFSG.KD.Fi24Tc.Pc.v306, CFSG.KD.Fi24Tc.Pc.v307, CFSG.KD.Fi24Tc.Pc.v308, CFSG.KD.Fi24Tc.Pc.v309]
theorem CFSG.KD.Fi24Tc.Pc.p308 : Nat.beq (runC AR SD 304 (ckL CFSG.KD.Fi24Tc.Pc.l310) 2 308 CFSG.KD.Fi24Tc.Pc.l308) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f51 : Nat.beq (runC AR SD 304 (finC AR SD (nat_lit 51) 304 312) 2 310 CFSG.KD.Fi24Tc.Pc.l310) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk51 : chk (nat_lit 51) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 51) (lo := 304) (hi := 312) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 306) CFSG.KD.Fi24Tc.Pc.p304 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 308) CFSG.KD.Fi24Tc.Pc.p306 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 310) CFSG.KD.Fi24Tc.Pc.p308 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f51

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v312 : Nat := CFSG.KD.Fi24Tc.KV2 68
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v313 : Nat := CFSG.KD.Fi24Tc.KV2 69
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l314 : List Nat := [CFSG.KD.Fi24Tc.Pc.v312, CFSG.KD.Fi24Tc.Pc.v313]
theorem CFSG.KD.Fi24Tc.Pc.p312 : Nat.beq (runC AR SD 312 (ckL CFSG.KD.Fi24Tc.Pc.l314) 2 312 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v314 : Nat := CFSG.KD.Fi24Tc.KV2 70
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v315 : Nat := CFSG.KD.Fi24Tc.KV2 71
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l316 : List Nat := [CFSG.KD.Fi24Tc.Pc.v312, CFSG.KD.Fi24Tc.Pc.v313, CFSG.KD.Fi24Tc.Pc.v314, CFSG.KD.Fi24Tc.Pc.v315]
theorem CFSG.KD.Fi24Tc.Pc.p314 : Nat.beq (runC AR SD 312 (ckL CFSG.KD.Fi24Tc.Pc.l316) 2 314 CFSG.KD.Fi24Tc.Pc.l314) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v316 : Nat := CFSG.KD.Fi24Tc.KV2 72
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v317 : Nat := CFSG.KD.Fi24Tc.KV2 73
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l318 : List Nat := [CFSG.KD.Fi24Tc.Pc.v312, CFSG.KD.Fi24Tc.Pc.v313, CFSG.KD.Fi24Tc.Pc.v314, CFSG.KD.Fi24Tc.Pc.v315, CFSG.KD.Fi24Tc.Pc.v316, CFSG.KD.Fi24Tc.Pc.v317]
theorem CFSG.KD.Fi24Tc.Pc.p316 : Nat.beq (runC AR SD 312 (ckL CFSG.KD.Fi24Tc.Pc.l318) 2 316 CFSG.KD.Fi24Tc.Pc.l316) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f52 : Nat.beq (runC AR SD 312 (finC AR SD (nat_lit 52) 312 320) 2 318 CFSG.KD.Fi24Tc.Pc.l318) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk52 : chk (nat_lit 52) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 52) (lo := 312) (hi := 320) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 314) CFSG.KD.Fi24Tc.Pc.p312 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 316) CFSG.KD.Fi24Tc.Pc.p314 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 318) CFSG.KD.Fi24Tc.Pc.p316 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f52

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v320 : Nat := CFSG.KD.Fi24Tc.KV2 74
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v321 : Nat := CFSG.KD.Fi24Tc.KV2 75
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l322 : List Nat := [CFSG.KD.Fi24Tc.Pc.v320, CFSG.KD.Fi24Tc.Pc.v321]
theorem CFSG.KD.Fi24Tc.Pc.p320 : Nat.beq (runC AR SD 320 (ckL CFSG.KD.Fi24Tc.Pc.l322) 2 320 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v322 : Nat := CFSG.KD.Fi24Tc.KV2 76
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v323 : Nat := CFSG.KD.Fi24Tc.KV2 77
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l324 : List Nat := [CFSG.KD.Fi24Tc.Pc.v320, CFSG.KD.Fi24Tc.Pc.v321, CFSG.KD.Fi24Tc.Pc.v322, CFSG.KD.Fi24Tc.Pc.v323]
theorem CFSG.KD.Fi24Tc.Pc.p322 : Nat.beq (runC AR SD 320 (ckL CFSG.KD.Fi24Tc.Pc.l324) 2 322 CFSG.KD.Fi24Tc.Pc.l322) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v324 : Nat := CFSG.KD.Fi24Tc.KV2 78
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v325 : Nat := CFSG.KD.Fi24Tc.KV2 79
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l326 : List Nat := [CFSG.KD.Fi24Tc.Pc.v320, CFSG.KD.Fi24Tc.Pc.v321, CFSG.KD.Fi24Tc.Pc.v322, CFSG.KD.Fi24Tc.Pc.v323, CFSG.KD.Fi24Tc.Pc.v324, CFSG.KD.Fi24Tc.Pc.v325]
theorem CFSG.KD.Fi24Tc.Pc.p324 : Nat.beq (runC AR SD 320 (ckL CFSG.KD.Fi24Tc.Pc.l326) 2 324 CFSG.KD.Fi24Tc.Pc.l324) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f53 : Nat.beq (runC AR SD 320 (finC AR SD (nat_lit 53) 320 328) 2 326 CFSG.KD.Fi24Tc.Pc.l326) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk53 : chk (nat_lit 53) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 53) (lo := 320) (hi := 328) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 322) CFSG.KD.Fi24Tc.Pc.p320 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 324) CFSG.KD.Fi24Tc.Pc.p322 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 326) CFSG.KD.Fi24Tc.Pc.p324 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f53

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v328 : Nat := CFSG.KD.Fi24Tc.KV2 80
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v329 : Nat := CFSG.KD.Fi24Tc.KV2 81
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l330 : List Nat := [CFSG.KD.Fi24Tc.Pc.v328, CFSG.KD.Fi24Tc.Pc.v329]
theorem CFSG.KD.Fi24Tc.Pc.p328 : Nat.beq (runC AR SD 328 (ckL CFSG.KD.Fi24Tc.Pc.l330) 2 328 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v330 : Nat := CFSG.KD.Fi24Tc.KV2 82
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v331 : Nat := CFSG.KD.Fi24Tc.KV2 83
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l332 : List Nat := [CFSG.KD.Fi24Tc.Pc.v328, CFSG.KD.Fi24Tc.Pc.v329, CFSG.KD.Fi24Tc.Pc.v330, CFSG.KD.Fi24Tc.Pc.v331]
theorem CFSG.KD.Fi24Tc.Pc.p330 : Nat.beq (runC AR SD 328 (ckL CFSG.KD.Fi24Tc.Pc.l332) 2 330 CFSG.KD.Fi24Tc.Pc.l330) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v332 : Nat := CFSG.KD.Fi24Tc.KV2 84
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v333 : Nat := CFSG.KD.Fi24Tc.KV2 85
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l334 : List Nat := [CFSG.KD.Fi24Tc.Pc.v328, CFSG.KD.Fi24Tc.Pc.v329, CFSG.KD.Fi24Tc.Pc.v330, CFSG.KD.Fi24Tc.Pc.v331, CFSG.KD.Fi24Tc.Pc.v332, CFSG.KD.Fi24Tc.Pc.v333]
theorem CFSG.KD.Fi24Tc.Pc.p332 : Nat.beq (runC AR SD 328 (ckL CFSG.KD.Fi24Tc.Pc.l334) 2 332 CFSG.KD.Fi24Tc.Pc.l332) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f54 : Nat.beq (runC AR SD 328 (finC AR SD (nat_lit 54) 328 336) 2 334 CFSG.KD.Fi24Tc.Pc.l334) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk54 : chk (nat_lit 54) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 54) (lo := 328) (hi := 336) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 330) CFSG.KD.Fi24Tc.Pc.p328 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 332) CFSG.KD.Fi24Tc.Pc.p330 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 334) CFSG.KD.Fi24Tc.Pc.p332 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f54

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v336 : Nat := CFSG.KD.Fi24Tc.KV2 86
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v337 : Nat := CFSG.KD.Fi24Tc.KV2 87
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l338 : List Nat := [CFSG.KD.Fi24Tc.Pc.v336, CFSG.KD.Fi24Tc.Pc.v337]
theorem CFSG.KD.Fi24Tc.Pc.p336 : Nat.beq (runC AR SD 336 (ckL CFSG.KD.Fi24Tc.Pc.l338) 2 336 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v338 : Nat := CFSG.KD.Fi24Tc.KV2 88
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v339 : Nat := CFSG.KD.Fi24Tc.KV2 89
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l340 : List Nat := [CFSG.KD.Fi24Tc.Pc.v336, CFSG.KD.Fi24Tc.Pc.v337, CFSG.KD.Fi24Tc.Pc.v338, CFSG.KD.Fi24Tc.Pc.v339]
theorem CFSG.KD.Fi24Tc.Pc.p338 : Nat.beq (runC AR SD 336 (ckL CFSG.KD.Fi24Tc.Pc.l340) 2 338 CFSG.KD.Fi24Tc.Pc.l338) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v340 : Nat := CFSG.KD.Fi24Tc.KV2 90
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v341 : Nat := CFSG.KD.Fi24Tc.KV2 91
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l342 : List Nat := [CFSG.KD.Fi24Tc.Pc.v336, CFSG.KD.Fi24Tc.Pc.v337, CFSG.KD.Fi24Tc.Pc.v338, CFSG.KD.Fi24Tc.Pc.v339, CFSG.KD.Fi24Tc.Pc.v340, CFSG.KD.Fi24Tc.Pc.v341]
theorem CFSG.KD.Fi24Tc.Pc.p340 : Nat.beq (runC AR SD 336 (ckL CFSG.KD.Fi24Tc.Pc.l342) 2 340 CFSG.KD.Fi24Tc.Pc.l340) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f55 : Nat.beq (runC AR SD 336 (finC AR SD (nat_lit 55) 336 344) 2 342 CFSG.KD.Fi24Tc.Pc.l342) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk55 : chk (nat_lit 55) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 55) (lo := 336) (hi := 344) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 338) CFSG.KD.Fi24Tc.Pc.p336 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 340) CFSG.KD.Fi24Tc.Pc.p338 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 342) CFSG.KD.Fi24Tc.Pc.p340 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f55

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v344 : Nat := CFSG.KD.Fi24Tc.KV2 92
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v345 : Nat := CFSG.KD.Fi24Tc.KV2 93
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l346 : List Nat := [CFSG.KD.Fi24Tc.Pc.v344, CFSG.KD.Fi24Tc.Pc.v345]
theorem CFSG.KD.Fi24Tc.Pc.p344 : Nat.beq (runC AR SD 344 (ckL CFSG.KD.Fi24Tc.Pc.l346) 2 344 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v346 : Nat := CFSG.KD.Fi24Tc.KV2 94
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v347 : Nat := CFSG.KD.Fi24Tc.KV2 95
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l348 : List Nat := [CFSG.KD.Fi24Tc.Pc.v344, CFSG.KD.Fi24Tc.Pc.v345, CFSG.KD.Fi24Tc.Pc.v346, CFSG.KD.Fi24Tc.Pc.v347]
theorem CFSG.KD.Fi24Tc.Pc.p346 : Nat.beq (runC AR SD 344 (ckL CFSG.KD.Fi24Tc.Pc.l348) 2 346 CFSG.KD.Fi24Tc.Pc.l346) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v348 : Nat := CFSG.KD.Fi24Tc.KV2 96
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v349 : Nat := CFSG.KD.Fi24Tc.KV2 97
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l350 : List Nat := [CFSG.KD.Fi24Tc.Pc.v344, CFSG.KD.Fi24Tc.Pc.v345, CFSG.KD.Fi24Tc.Pc.v346, CFSG.KD.Fi24Tc.Pc.v347, CFSG.KD.Fi24Tc.Pc.v348, CFSG.KD.Fi24Tc.Pc.v349]
theorem CFSG.KD.Fi24Tc.Pc.p348 : Nat.beq (runC AR SD 344 (ckL CFSG.KD.Fi24Tc.Pc.l350) 2 348 CFSG.KD.Fi24Tc.Pc.l348) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f56 : Nat.beq (runC AR SD 344 (finC AR SD (nat_lit 56) 344 352) 2 350 CFSG.KD.Fi24Tc.Pc.l350) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk56 : chk (nat_lit 56) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 56) (lo := 344) (hi := 352) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 346) CFSG.KD.Fi24Tc.Pc.p344 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 348) CFSG.KD.Fi24Tc.Pc.p346 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 350) CFSG.KD.Fi24Tc.Pc.p348 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f56

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v352 : Nat := CFSG.KD.Fi24Tc.KV2 98
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v353 : Nat := CFSG.KD.Fi24Tc.KV2 99
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l354 : List Nat := [CFSG.KD.Fi24Tc.Pc.v352, CFSG.KD.Fi24Tc.Pc.v353]
theorem CFSG.KD.Fi24Tc.Pc.p352 : Nat.beq (runC AR SD 352 (ckL CFSG.KD.Fi24Tc.Pc.l354) 2 352 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v354 : Nat := CFSG.KD.Fi24Tc.KV2 100
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v355 : Nat := CFSG.KD.Fi24Tc.KV2 101
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l356 : List Nat := [CFSG.KD.Fi24Tc.Pc.v352, CFSG.KD.Fi24Tc.Pc.v353, CFSG.KD.Fi24Tc.Pc.v354, CFSG.KD.Fi24Tc.Pc.v355]
theorem CFSG.KD.Fi24Tc.Pc.p354 : Nat.beq (runC AR SD 352 (ckL CFSG.KD.Fi24Tc.Pc.l356) 2 354 CFSG.KD.Fi24Tc.Pc.l354) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v356 : Nat := CFSG.KD.Fi24Tc.KV2 102
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v357 : Nat := CFSG.KD.Fi24Tc.KV2 103
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l358 : List Nat := [CFSG.KD.Fi24Tc.Pc.v352, CFSG.KD.Fi24Tc.Pc.v353, CFSG.KD.Fi24Tc.Pc.v354, CFSG.KD.Fi24Tc.Pc.v355, CFSG.KD.Fi24Tc.Pc.v356, CFSG.KD.Fi24Tc.Pc.v357]
theorem CFSG.KD.Fi24Tc.Pc.p356 : Nat.beq (runC AR SD 352 (ckL CFSG.KD.Fi24Tc.Pc.l358) 2 356 CFSG.KD.Fi24Tc.Pc.l356) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f57 : Nat.beq (runC AR SD 352 (finC AR SD (nat_lit 57) 352 360) 2 358 CFSG.KD.Fi24Tc.Pc.l358) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk57 : chk (nat_lit 57) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 57) (lo := 352) (hi := 360) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 354) CFSG.KD.Fi24Tc.Pc.p352 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 356) CFSG.KD.Fi24Tc.Pc.p354 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 358) CFSG.KD.Fi24Tc.Pc.p356 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f57

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v360 : Nat := CFSG.KD.Fi24Tc.KV2 104
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v361 : Nat := CFSG.KD.Fi24Tc.KV2 105
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l362 : List Nat := [CFSG.KD.Fi24Tc.Pc.v360, CFSG.KD.Fi24Tc.Pc.v361]
theorem CFSG.KD.Fi24Tc.Pc.p360 : Nat.beq (runC AR SD 360 (ckL CFSG.KD.Fi24Tc.Pc.l362) 2 360 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v362 : Nat := CFSG.KD.Fi24Tc.KV2 106
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v363 : Nat := CFSG.KD.Fi24Tc.KV2 107
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l364 : List Nat := [CFSG.KD.Fi24Tc.Pc.v360, CFSG.KD.Fi24Tc.Pc.v361, CFSG.KD.Fi24Tc.Pc.v362, CFSG.KD.Fi24Tc.Pc.v363]
theorem CFSG.KD.Fi24Tc.Pc.p362 : Nat.beq (runC AR SD 360 (ckL CFSG.KD.Fi24Tc.Pc.l364) 2 362 CFSG.KD.Fi24Tc.Pc.l362) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v364 : Nat := CFSG.KD.Fi24Tc.KV2 108
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v365 : Nat := CFSG.KD.Fi24Tc.KV2 109
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l366 : List Nat := [CFSG.KD.Fi24Tc.Pc.v360, CFSG.KD.Fi24Tc.Pc.v361, CFSG.KD.Fi24Tc.Pc.v362, CFSG.KD.Fi24Tc.Pc.v363, CFSG.KD.Fi24Tc.Pc.v364, CFSG.KD.Fi24Tc.Pc.v365]
theorem CFSG.KD.Fi24Tc.Pc.p364 : Nat.beq (runC AR SD 360 (ckL CFSG.KD.Fi24Tc.Pc.l366) 2 364 CFSG.KD.Fi24Tc.Pc.l364) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f58 : Nat.beq (runC AR SD 360 (finC AR SD (nat_lit 58) 360 368) 2 366 CFSG.KD.Fi24Tc.Pc.l366) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk58 : chk (nat_lit 58) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 58) (lo := 360) (hi := 368) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 362) CFSG.KD.Fi24Tc.Pc.p360 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 364) CFSG.KD.Fi24Tc.Pc.p362 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 366) CFSG.KD.Fi24Tc.Pc.p364 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f58

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v368 : Nat := CFSG.KD.Fi24Tc.KV2 110
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v369 : Nat := CFSG.KD.Fi24Tc.KV2 111
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l370 : List Nat := [CFSG.KD.Fi24Tc.Pc.v368, CFSG.KD.Fi24Tc.Pc.v369]
theorem CFSG.KD.Fi24Tc.Pc.p368 : Nat.beq (runC AR SD 368 (ckL CFSG.KD.Fi24Tc.Pc.l370) 2 368 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v370 : Nat := CFSG.KD.Fi24Tc.KV2 112
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v371 : Nat := CFSG.KD.Fi24Tc.KV2 113
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l372 : List Nat := [CFSG.KD.Fi24Tc.Pc.v368, CFSG.KD.Fi24Tc.Pc.v369, CFSG.KD.Fi24Tc.Pc.v370, CFSG.KD.Fi24Tc.Pc.v371]
theorem CFSG.KD.Fi24Tc.Pc.p370 : Nat.beq (runC AR SD 368 (ckL CFSG.KD.Fi24Tc.Pc.l372) 2 370 CFSG.KD.Fi24Tc.Pc.l370) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v372 : Nat := CFSG.KD.Fi24Tc.KV2 114
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v373 : Nat := CFSG.KD.Fi24Tc.KV2 115
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l374 : List Nat := [CFSG.KD.Fi24Tc.Pc.v368, CFSG.KD.Fi24Tc.Pc.v369, CFSG.KD.Fi24Tc.Pc.v370, CFSG.KD.Fi24Tc.Pc.v371, CFSG.KD.Fi24Tc.Pc.v372, CFSG.KD.Fi24Tc.Pc.v373]
theorem CFSG.KD.Fi24Tc.Pc.p372 : Nat.beq (runC AR SD 368 (ckL CFSG.KD.Fi24Tc.Pc.l374) 2 372 CFSG.KD.Fi24Tc.Pc.l372) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f59 : Nat.beq (runC AR SD 368 (finC AR SD (nat_lit 59) 368 376) 2 374 CFSG.KD.Fi24Tc.Pc.l374) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk59 : chk (nat_lit 59) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 59) (lo := 368) (hi := 376) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 370) CFSG.KD.Fi24Tc.Pc.p368 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 372) CFSG.KD.Fi24Tc.Pc.p370 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 374) CFSG.KD.Fi24Tc.Pc.p372 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f59

end
