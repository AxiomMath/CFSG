module

public import Certificates.Kernel.Sporadic.Fi24Alpha.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Alpha KV2 "Certificates/Kernel/Sporadic/Fi24Alpha/data/v2.bin" 152491 4 21958704 15004304967878935675

public section

open CFSG.KD.Fi24Alpha CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v234 : Nat := CFSG.KD.Fi24Alpha.KV2 0
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v235 : Nat := CFSG.KD.Fi24Alpha.KV2 1
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l236 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v234, CFSG.KD.Fi24Alpha.Pc.v235]
theorem CFSG.KD.Fi24Alpha.Pc.p234 : Nat.beq (runC AR SD 234 (ckL CFSG.KD.Fi24Alpha.Pc.l236) 2 234 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v236 : Nat := CFSG.KD.Fi24Alpha.KV2 2
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v237 : Nat := CFSG.KD.Fi24Alpha.KV2 3
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l238 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v234, CFSG.KD.Fi24Alpha.Pc.v235, CFSG.KD.Fi24Alpha.Pc.v236, CFSG.KD.Fi24Alpha.Pc.v237]
theorem CFSG.KD.Fi24Alpha.Pc.p236 : Nat.beq (runC AR SD 234 (ckL CFSG.KD.Fi24Alpha.Pc.l238) 2 236 CFSG.KD.Fi24Alpha.Pc.l236) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v238 : Nat := CFSG.KD.Fi24Alpha.KV2 4
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v239 : Nat := CFSG.KD.Fi24Alpha.KV2 5
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l240 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v234, CFSG.KD.Fi24Alpha.Pc.v235, CFSG.KD.Fi24Alpha.Pc.v236, CFSG.KD.Fi24Alpha.Pc.v237, CFSG.KD.Fi24Alpha.Pc.v238, CFSG.KD.Fi24Alpha.Pc.v239]
theorem CFSG.KD.Fi24Alpha.Pc.p238 : Nat.beq (runC AR SD 234 (ckL CFSG.KD.Fi24Alpha.Pc.l240) 2 238 CFSG.KD.Fi24Alpha.Pc.l238) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a240_1 : Nat := CFSG.KD.Fi24Alpha.KV2 6
theorem CFSG.KD.Fi24Alpha.Pc.q240_1 : Nat.beq (powTop AR.mul (getV AR SD 234 CFSG.KD.Fi24Alpha.Pc.l240 (SD.na.getD 240 0)) (SD.nk.getD 240 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a240_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v240 : Nat := CFSG.KD.Fi24Alpha.KV2 7
theorem CFSG.KD.Fi24Alpha.Pc.r240 : Nat.beq (powR AR.mul AR.one (getV AR SD 234 CFSG.KD.Fi24Alpha.Pc.l240 (SD.na.getD 240 0)) (SD.nk.getD 240 1) 1 CFSG.KD.Fi24Alpha.Pc.a240_1 true) CFSG.KD.Fi24Alpha.Pc.v240 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v241 : Nat := CFSG.KD.Fi24Alpha.KV2 8
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v242 : Nat := CFSG.KD.Fi24Alpha.KV2 9
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l241 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v234, CFSG.KD.Fi24Alpha.Pc.v235, CFSG.KD.Fi24Alpha.Pc.v236, CFSG.KD.Fi24Alpha.Pc.v237, CFSG.KD.Fi24Alpha.Pc.v238, CFSG.KD.Fi24Alpha.Pc.v239, CFSG.KD.Fi24Alpha.Pc.v240]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l243 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v234, CFSG.KD.Fi24Alpha.Pc.v235, CFSG.KD.Fi24Alpha.Pc.v236, CFSG.KD.Fi24Alpha.Pc.v237, CFSG.KD.Fi24Alpha.Pc.v238, CFSG.KD.Fi24Alpha.Pc.v239, CFSG.KD.Fi24Alpha.Pc.v240, CFSG.KD.Fi24Alpha.Pc.v241, CFSG.KD.Fi24Alpha.Pc.v242]
theorem CFSG.KD.Fi24Alpha.Pc.p241 : Nat.beq (runC AR SD 234 (ckL CFSG.KD.Fi24Alpha.Pc.l243) 2 241 CFSG.KD.Fi24Alpha.Pc.l241) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v243 : Nat := CFSG.KD.Fi24Alpha.KV2 10
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l244 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v234, CFSG.KD.Fi24Alpha.Pc.v235, CFSG.KD.Fi24Alpha.Pc.v236, CFSG.KD.Fi24Alpha.Pc.v237, CFSG.KD.Fi24Alpha.Pc.v238, CFSG.KD.Fi24Alpha.Pc.v239, CFSG.KD.Fi24Alpha.Pc.v240, CFSG.KD.Fi24Alpha.Pc.v241, CFSG.KD.Fi24Alpha.Pc.v242, CFSG.KD.Fi24Alpha.Pc.v243]
theorem CFSG.KD.Fi24Alpha.Pc.p243 : Nat.beq (runC AR SD 234 (ckL CFSG.KD.Fi24Alpha.Pc.l244) 1 243 CFSG.KD.Fi24Alpha.Pc.l243) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v244 : Nat := CFSG.KD.Fi24Alpha.KV2 11
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v245 : Nat := CFSG.KD.Fi24Alpha.KV2 12
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l246 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v234, CFSG.KD.Fi24Alpha.Pc.v235, CFSG.KD.Fi24Alpha.Pc.v236, CFSG.KD.Fi24Alpha.Pc.v237, CFSG.KD.Fi24Alpha.Pc.v238, CFSG.KD.Fi24Alpha.Pc.v239, CFSG.KD.Fi24Alpha.Pc.v240, CFSG.KD.Fi24Alpha.Pc.v241, CFSG.KD.Fi24Alpha.Pc.v242, CFSG.KD.Fi24Alpha.Pc.v243, CFSG.KD.Fi24Alpha.Pc.v244, CFSG.KD.Fi24Alpha.Pc.v245]
theorem CFSG.KD.Fi24Alpha.Pc.p244 : Nat.beq (runC AR SD 234 (ckL CFSG.KD.Fi24Alpha.Pc.l246) 2 244 CFSG.KD.Fi24Alpha.Pc.l244) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v246 : Nat := CFSG.KD.Fi24Alpha.KV2 13
theorem CFSG.KD.Fi24Alpha.Pc.f20 : Nat.beq (runC AR SD 234 (finC AR SD (nat_lit 20) 234 247) 1 246 CFSG.KD.Fi24Alpha.Pc.l246) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk20 : chk (nat_lit 20) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 20) (lo := 234) (hi := 247) (m := 13) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 13) (m2 := 11) (j2 := 236) CFSG.KD.Fi24Alpha.Pc.p234 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 238) CFSG.KD.Fi24Alpha.Pc.p236 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 240) CFSG.KD.Fi24Alpha.Pc.p238 rfl rfl).trans ((runC_node (m := 7) (m2 := 6) (j2 := 241) (Lr := CFSG.KD.Fi24Alpha.Pc.l241) ((nodeV_pow (R := AR) (D := SD) (lo := 234) (L := CFSG.KD.Fi24Alpha.Pc.l240) (j := 240) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 234 CFSG.KD.Fi24Alpha.Pc.l240 (SD.na.getD 240 0)) (SD.nk.getD 240 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q240_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r240)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 243) CFSG.KD.Fi24Alpha.Pc.p241 rfl rfl).trans ((runC_seq (m := 4) (m2 := 3) (j2 := 244) CFSG.KD.Fi24Alpha.Pc.p243 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 246) CFSG.KD.Fi24Alpha.Pc.p244 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f20

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v247 : Nat := CFSG.KD.Fi24Alpha.KV2 14
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v248 : Nat := CFSG.KD.Fi24Alpha.KV2 15
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l249 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v247, CFSG.KD.Fi24Alpha.Pc.v248]
theorem CFSG.KD.Fi24Alpha.Pc.p247 : Nat.beq (runC AR SD 247 (ckL CFSG.KD.Fi24Alpha.Pc.l249) 2 247 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v249 : Nat := CFSG.KD.Fi24Alpha.KV2 16
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v250 : Nat := CFSG.KD.Fi24Alpha.KV2 17
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l251 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v247, CFSG.KD.Fi24Alpha.Pc.v248, CFSG.KD.Fi24Alpha.Pc.v249, CFSG.KD.Fi24Alpha.Pc.v250]
theorem CFSG.KD.Fi24Alpha.Pc.p249 : Nat.beq (runC AR SD 247 (ckL CFSG.KD.Fi24Alpha.Pc.l251) 2 249 CFSG.KD.Fi24Alpha.Pc.l249) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v251 : Nat := CFSG.KD.Fi24Alpha.KV2 18
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v252 : Nat := CFSG.KD.Fi24Alpha.KV2 19
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l253 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v247, CFSG.KD.Fi24Alpha.Pc.v248, CFSG.KD.Fi24Alpha.Pc.v249, CFSG.KD.Fi24Alpha.Pc.v250, CFSG.KD.Fi24Alpha.Pc.v251, CFSG.KD.Fi24Alpha.Pc.v252]
theorem CFSG.KD.Fi24Alpha.Pc.p251 : Nat.beq (runC AR SD 247 (ckL CFSG.KD.Fi24Alpha.Pc.l253) 2 251 CFSG.KD.Fi24Alpha.Pc.l251) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v253 : Nat := CFSG.KD.Fi24Alpha.KV2 20
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v254 : Nat := CFSG.KD.Fi24Alpha.KV2 21
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l255 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v247, CFSG.KD.Fi24Alpha.Pc.v248, CFSG.KD.Fi24Alpha.Pc.v249, CFSG.KD.Fi24Alpha.Pc.v250, CFSG.KD.Fi24Alpha.Pc.v251, CFSG.KD.Fi24Alpha.Pc.v252, CFSG.KD.Fi24Alpha.Pc.v253, CFSG.KD.Fi24Alpha.Pc.v254]
theorem CFSG.KD.Fi24Alpha.Pc.p253 : Nat.beq (runC AR SD 247 (ckL CFSG.KD.Fi24Alpha.Pc.l255) 2 253 CFSG.KD.Fi24Alpha.Pc.l253) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v255 : Nat := CFSG.KD.Fi24Alpha.KV2 22
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v256 : Nat := CFSG.KD.Fi24Alpha.KV2 23
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l257 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v247, CFSG.KD.Fi24Alpha.Pc.v248, CFSG.KD.Fi24Alpha.Pc.v249, CFSG.KD.Fi24Alpha.Pc.v250, CFSG.KD.Fi24Alpha.Pc.v251, CFSG.KD.Fi24Alpha.Pc.v252, CFSG.KD.Fi24Alpha.Pc.v253, CFSG.KD.Fi24Alpha.Pc.v254, CFSG.KD.Fi24Alpha.Pc.v255, CFSG.KD.Fi24Alpha.Pc.v256]
theorem CFSG.KD.Fi24Alpha.Pc.p255 : Nat.beq (runC AR SD 247 (ckL CFSG.KD.Fi24Alpha.Pc.l257) 2 255 CFSG.KD.Fi24Alpha.Pc.l255) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v257 : Nat := CFSG.KD.Fi24Alpha.KV2 24
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v258 : Nat := CFSG.KD.Fi24Alpha.KV2 25
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l259 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v247, CFSG.KD.Fi24Alpha.Pc.v248, CFSG.KD.Fi24Alpha.Pc.v249, CFSG.KD.Fi24Alpha.Pc.v250, CFSG.KD.Fi24Alpha.Pc.v251, CFSG.KD.Fi24Alpha.Pc.v252, CFSG.KD.Fi24Alpha.Pc.v253, CFSG.KD.Fi24Alpha.Pc.v254, CFSG.KD.Fi24Alpha.Pc.v255, CFSG.KD.Fi24Alpha.Pc.v256, CFSG.KD.Fi24Alpha.Pc.v257, CFSG.KD.Fi24Alpha.Pc.v258]
theorem CFSG.KD.Fi24Alpha.Pc.p257 : Nat.beq (runC AR SD 247 (ckL CFSG.KD.Fi24Alpha.Pc.l259) 2 257 CFSG.KD.Fi24Alpha.Pc.l257) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v259 : Nat := CFSG.KD.Fi24Alpha.KV2 26
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v260 : Nat := CFSG.KD.Fi24Alpha.KV2 27
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l261 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v247, CFSG.KD.Fi24Alpha.Pc.v248, CFSG.KD.Fi24Alpha.Pc.v249, CFSG.KD.Fi24Alpha.Pc.v250, CFSG.KD.Fi24Alpha.Pc.v251, CFSG.KD.Fi24Alpha.Pc.v252, CFSG.KD.Fi24Alpha.Pc.v253, CFSG.KD.Fi24Alpha.Pc.v254, CFSG.KD.Fi24Alpha.Pc.v255, CFSG.KD.Fi24Alpha.Pc.v256, CFSG.KD.Fi24Alpha.Pc.v257, CFSG.KD.Fi24Alpha.Pc.v258, CFSG.KD.Fi24Alpha.Pc.v259, CFSG.KD.Fi24Alpha.Pc.v260]
theorem CFSG.KD.Fi24Alpha.Pc.p259 : Nat.beq (runC AR SD 247 (ckL CFSG.KD.Fi24Alpha.Pc.l261) 2 259 CFSG.KD.Fi24Alpha.Pc.l259) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v261 : Nat := CFSG.KD.Fi24Alpha.KV2 28
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v262 : Nat := CFSG.KD.Fi24Alpha.KV2 29
theorem CFSG.KD.Fi24Alpha.Pc.f21 : Nat.beq (runC AR SD 247 (finC AR SD (nat_lit 21) 247 263) 2 261 CFSG.KD.Fi24Alpha.Pc.l261) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk21 : chk (nat_lit 21) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 21) (lo := 247) (hi := 263) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 249) CFSG.KD.Fi24Alpha.Pc.p247 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 251) CFSG.KD.Fi24Alpha.Pc.p249 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 253) CFSG.KD.Fi24Alpha.Pc.p251 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 255) CFSG.KD.Fi24Alpha.Pc.p253 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 257) CFSG.KD.Fi24Alpha.Pc.p255 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 259) CFSG.KD.Fi24Alpha.Pc.p257 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 261) CFSG.KD.Fi24Alpha.Pc.p259 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f21

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v263 : Nat := CFSG.KD.Fi24Alpha.KV2 30
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v264 : Nat := CFSG.KD.Fi24Alpha.KV2 31
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l265 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v263, CFSG.KD.Fi24Alpha.Pc.v264]
theorem CFSG.KD.Fi24Alpha.Pc.p263 : Nat.beq (runC AR SD 263 (ckL CFSG.KD.Fi24Alpha.Pc.l265) 2 263 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v265 : Nat := CFSG.KD.Fi24Alpha.KV2 32
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v266 : Nat := CFSG.KD.Fi24Alpha.KV2 33
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l267 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v263, CFSG.KD.Fi24Alpha.Pc.v264, CFSG.KD.Fi24Alpha.Pc.v265, CFSG.KD.Fi24Alpha.Pc.v266]
theorem CFSG.KD.Fi24Alpha.Pc.p265 : Nat.beq (runC AR SD 263 (ckL CFSG.KD.Fi24Alpha.Pc.l267) 2 265 CFSG.KD.Fi24Alpha.Pc.l265) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v267 : Nat := CFSG.KD.Fi24Alpha.KV2 34
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v268 : Nat := CFSG.KD.Fi24Alpha.KV2 35
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l269 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v263, CFSG.KD.Fi24Alpha.Pc.v264, CFSG.KD.Fi24Alpha.Pc.v265, CFSG.KD.Fi24Alpha.Pc.v266, CFSG.KD.Fi24Alpha.Pc.v267, CFSG.KD.Fi24Alpha.Pc.v268]
theorem CFSG.KD.Fi24Alpha.Pc.p267 : Nat.beq (runC AR SD 263 (ckL CFSG.KD.Fi24Alpha.Pc.l269) 2 267 CFSG.KD.Fi24Alpha.Pc.l267) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a269_1 : Nat := CFSG.KD.Fi24Alpha.KV2 36
theorem CFSG.KD.Fi24Alpha.Pc.q269_1 : Nat.beq (powTop AR.mul (getV AR SD 263 CFSG.KD.Fi24Alpha.Pc.l269 (SD.na.getD 269 0)) (SD.nk.getD 269 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a269_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v269 : Nat := CFSG.KD.Fi24Alpha.KV2 37
theorem CFSG.KD.Fi24Alpha.Pc.r269 : Nat.beq (powR AR.mul AR.one (getV AR SD 263 CFSG.KD.Fi24Alpha.Pc.l269 (SD.na.getD 269 0)) (SD.nk.getD 269 1) 1 CFSG.KD.Fi24Alpha.Pc.a269_1 true) CFSG.KD.Fi24Alpha.Pc.v269 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v270 : Nat := CFSG.KD.Fi24Alpha.KV2 38
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v271 : Nat := CFSG.KD.Fi24Alpha.KV2 39
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l270 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v263, CFSG.KD.Fi24Alpha.Pc.v264, CFSG.KD.Fi24Alpha.Pc.v265, CFSG.KD.Fi24Alpha.Pc.v266, CFSG.KD.Fi24Alpha.Pc.v267, CFSG.KD.Fi24Alpha.Pc.v268, CFSG.KD.Fi24Alpha.Pc.v269]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l272 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v263, CFSG.KD.Fi24Alpha.Pc.v264, CFSG.KD.Fi24Alpha.Pc.v265, CFSG.KD.Fi24Alpha.Pc.v266, CFSG.KD.Fi24Alpha.Pc.v267, CFSG.KD.Fi24Alpha.Pc.v268, CFSG.KD.Fi24Alpha.Pc.v269, CFSG.KD.Fi24Alpha.Pc.v270, CFSG.KD.Fi24Alpha.Pc.v271]
theorem CFSG.KD.Fi24Alpha.Pc.p270 : Nat.beq (runC AR SD 263 (ckL CFSG.KD.Fi24Alpha.Pc.l272) 2 270 CFSG.KD.Fi24Alpha.Pc.l270) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a272_1 : Nat := CFSG.KD.Fi24Alpha.KV2 40
theorem CFSG.KD.Fi24Alpha.Pc.q272_1 : Nat.beq (powTop AR.mul (getV AR SD 263 CFSG.KD.Fi24Alpha.Pc.l272 (SD.na.getD 272 0)) (SD.nk.getD 272 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a272_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v272 : Nat := CFSG.KD.Fi24Alpha.KV2 41
theorem CFSG.KD.Fi24Alpha.Pc.r272 : Nat.beq (powR AR.mul AR.one (getV AR SD 263 CFSG.KD.Fi24Alpha.Pc.l272 (SD.na.getD 272 0)) (SD.nk.getD 272 1) 1 CFSG.KD.Fi24Alpha.Pc.a272_1 true) CFSG.KD.Fi24Alpha.Pc.v272 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v273 : Nat := CFSG.KD.Fi24Alpha.KV2 42
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l273 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v263, CFSG.KD.Fi24Alpha.Pc.v264, CFSG.KD.Fi24Alpha.Pc.v265, CFSG.KD.Fi24Alpha.Pc.v266, CFSG.KD.Fi24Alpha.Pc.v267, CFSG.KD.Fi24Alpha.Pc.v268, CFSG.KD.Fi24Alpha.Pc.v269, CFSG.KD.Fi24Alpha.Pc.v270, CFSG.KD.Fi24Alpha.Pc.v271, CFSG.KD.Fi24Alpha.Pc.v272]
theorem CFSG.KD.Fi24Alpha.Pc.f22 : Nat.beq (runC AR SD 263 (finC AR SD (nat_lit 22) 263 274) 1 273 CFSG.KD.Fi24Alpha.Pc.l273) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk22 : chk (nat_lit 22) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 22) (lo := 263) (hi := 274) (m := 11) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 11) (m2 := 9) (j2 := 265) CFSG.KD.Fi24Alpha.Pc.p263 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 267) CFSG.KD.Fi24Alpha.Pc.p265 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 269) CFSG.KD.Fi24Alpha.Pc.p267 rfl rfl).trans ((runC_node (m := 5) (m2 := 4) (j2 := 270) (Lr := CFSG.KD.Fi24Alpha.Pc.l270) ((nodeV_pow (R := AR) (D := SD) (lo := 263) (L := CFSG.KD.Fi24Alpha.Pc.l269) (j := 269) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 263 CFSG.KD.Fi24Alpha.Pc.l269 (SD.na.getD 269 0)) (SD.nk.getD 269 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q269_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r269)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 4) (m2 := 2) (j2 := 272) CFSG.KD.Fi24Alpha.Pc.p270 rfl rfl).trans (runC_node (m := 2) (m2 := 1) (j2 := 273) (Lr := CFSG.KD.Fi24Alpha.Pc.l273) ((nodeV_pow (R := AR) (D := SD) (lo := 263) (L := CFSG.KD.Fi24Alpha.Pc.l272) (j := 272) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 263 CFSG.KD.Fi24Alpha.Pc.l272 (SD.na.getD 272 0)) (SD.nk.getD 272 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q272_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r272)))) (by quickRfl) rfl rfl rfl)))))))).trans CFSG.KD.Fi24Alpha.Pc.f22

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v274 : Nat := CFSG.KD.Fi24Alpha.KV2 43
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v275 : Nat := CFSG.KD.Fi24Alpha.KV2 44
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l276 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v274, CFSG.KD.Fi24Alpha.Pc.v275]
theorem CFSG.KD.Fi24Alpha.Pc.p274 : Nat.beq (runC AR SD 274 (ckL CFSG.KD.Fi24Alpha.Pc.l276) 2 274 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v276 : Nat := CFSG.KD.Fi24Alpha.KV2 45
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v277 : Nat := CFSG.KD.Fi24Alpha.KV2 46
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l278 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v274, CFSG.KD.Fi24Alpha.Pc.v275, CFSG.KD.Fi24Alpha.Pc.v276, CFSG.KD.Fi24Alpha.Pc.v277]
theorem CFSG.KD.Fi24Alpha.Pc.p276 : Nat.beq (runC AR SD 274 (ckL CFSG.KD.Fi24Alpha.Pc.l278) 2 276 CFSG.KD.Fi24Alpha.Pc.l276) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v278 : Nat := CFSG.KD.Fi24Alpha.KV2 47
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l279 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v274, CFSG.KD.Fi24Alpha.Pc.v275, CFSG.KD.Fi24Alpha.Pc.v276, CFSG.KD.Fi24Alpha.Pc.v277, CFSG.KD.Fi24Alpha.Pc.v278]
theorem CFSG.KD.Fi24Alpha.Pc.p278 : Nat.beq (runC AR SD 274 (ckL CFSG.KD.Fi24Alpha.Pc.l279) 1 278 CFSG.KD.Fi24Alpha.Pc.l278) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a279_1 : Nat := CFSG.KD.Fi24Alpha.KV2 48
theorem CFSG.KD.Fi24Alpha.Pc.q279_1 : Nat.beq (powTop AR.mul (getV AR SD 274 CFSG.KD.Fi24Alpha.Pc.l279 (SD.na.getD 279 0)) (SD.nk.getD 279 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a279_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v279 : Nat := CFSG.KD.Fi24Alpha.KV2 49
theorem CFSG.KD.Fi24Alpha.Pc.r279 : Nat.beq (powR AR.mul AR.one (getV AR SD 274 CFSG.KD.Fi24Alpha.Pc.l279 (SD.na.getD 279 0)) (SD.nk.getD 279 1) 1 CFSG.KD.Fi24Alpha.Pc.a279_1 true) CFSG.KD.Fi24Alpha.Pc.v279 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v280 : Nat := CFSG.KD.Fi24Alpha.KV2 50
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v281 : Nat := CFSG.KD.Fi24Alpha.KV2 51
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l280 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v274, CFSG.KD.Fi24Alpha.Pc.v275, CFSG.KD.Fi24Alpha.Pc.v276, CFSG.KD.Fi24Alpha.Pc.v277, CFSG.KD.Fi24Alpha.Pc.v278, CFSG.KD.Fi24Alpha.Pc.v279]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l282 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v274, CFSG.KD.Fi24Alpha.Pc.v275, CFSG.KD.Fi24Alpha.Pc.v276, CFSG.KD.Fi24Alpha.Pc.v277, CFSG.KD.Fi24Alpha.Pc.v278, CFSG.KD.Fi24Alpha.Pc.v279, CFSG.KD.Fi24Alpha.Pc.v280, CFSG.KD.Fi24Alpha.Pc.v281]
theorem CFSG.KD.Fi24Alpha.Pc.p280 : Nat.beq (runC AR SD 274 (ckL CFSG.KD.Fi24Alpha.Pc.l282) 2 280 CFSG.KD.Fi24Alpha.Pc.l280) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v282 : Nat := CFSG.KD.Fi24Alpha.KV2 52
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v283 : Nat := CFSG.KD.Fi24Alpha.KV2 53
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l284 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v274, CFSG.KD.Fi24Alpha.Pc.v275, CFSG.KD.Fi24Alpha.Pc.v276, CFSG.KD.Fi24Alpha.Pc.v277, CFSG.KD.Fi24Alpha.Pc.v278, CFSG.KD.Fi24Alpha.Pc.v279, CFSG.KD.Fi24Alpha.Pc.v280, CFSG.KD.Fi24Alpha.Pc.v281, CFSG.KD.Fi24Alpha.Pc.v282, CFSG.KD.Fi24Alpha.Pc.v283]
theorem CFSG.KD.Fi24Alpha.Pc.p282 : Nat.beq (runC AR SD 274 (ckL CFSG.KD.Fi24Alpha.Pc.l284) 2 282 CFSG.KD.Fi24Alpha.Pc.l282) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v284 : Nat := CFSG.KD.Fi24Alpha.KV2 54
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v285 : Nat := CFSG.KD.Fi24Alpha.KV2 55
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l286 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v274, CFSG.KD.Fi24Alpha.Pc.v275, CFSG.KD.Fi24Alpha.Pc.v276, CFSG.KD.Fi24Alpha.Pc.v277, CFSG.KD.Fi24Alpha.Pc.v278, CFSG.KD.Fi24Alpha.Pc.v279, CFSG.KD.Fi24Alpha.Pc.v280, CFSG.KD.Fi24Alpha.Pc.v281, CFSG.KD.Fi24Alpha.Pc.v282, CFSG.KD.Fi24Alpha.Pc.v283, CFSG.KD.Fi24Alpha.Pc.v284, CFSG.KD.Fi24Alpha.Pc.v285]
theorem CFSG.KD.Fi24Alpha.Pc.p284 : Nat.beq (runC AR SD 274 (ckL CFSG.KD.Fi24Alpha.Pc.l286) 2 284 CFSG.KD.Fi24Alpha.Pc.l284) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v286 : Nat := CFSG.KD.Fi24Alpha.KV2 56
theorem CFSG.KD.Fi24Alpha.Pc.f23 : Nat.beq (runC AR SD 274 (finC AR SD (nat_lit 23) 274 287) 1 286 CFSG.KD.Fi24Alpha.Pc.l286) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk23 : chk (nat_lit 23) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 23) (lo := 274) (hi := 287) (m := 13) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 13) (m2 := 11) (j2 := 276) CFSG.KD.Fi24Alpha.Pc.p274 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 278) CFSG.KD.Fi24Alpha.Pc.p276 rfl rfl).trans ((runC_seq (m := 9) (m2 := 8) (j2 := 279) CFSG.KD.Fi24Alpha.Pc.p278 rfl rfl).trans ((runC_node (m := 8) (m2 := 7) (j2 := 280) (Lr := CFSG.KD.Fi24Alpha.Pc.l280) ((nodeV_pow (R := AR) (D := SD) (lo := 274) (L := CFSG.KD.Fi24Alpha.Pc.l279) (j := 279) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 274 CFSG.KD.Fi24Alpha.Pc.l279 (SD.na.getD 279 0)) (SD.nk.getD 279 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q279_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r279)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 282) CFSG.KD.Fi24Alpha.Pc.p280 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 284) CFSG.KD.Fi24Alpha.Pc.p282 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 286) CFSG.KD.Fi24Alpha.Pc.p284 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f23

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a287_2 : Nat := CFSG.KD.Fi24Alpha.KV2 57
theorem CFSG.KD.Fi24Alpha.Pc.q287_2 : Nat.beq (powTop AR.mul (getV AR SD 287 [] (SD.na.getD 287 0)) (SD.nk.getD 287 1) 2 (ckP CFSG.KD.Fi24Alpha.Pc.a287_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a287_1 : Nat := CFSG.KD.Fi24Alpha.KV2 58
theorem CFSG.KD.Fi24Alpha.Pc.q287_1 : Nat.beq (powTop AR.mul (getV AR SD 287 [] (SD.na.getD 287 0)) (SD.nk.getD 287 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a287_1) 1 CFSG.KD.Fi24Alpha.Pc.a287_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v287 : Nat := CFSG.KD.Fi24Alpha.KV2 59
theorem CFSG.KD.Fi24Alpha.Pc.r287 : Nat.beq (powR AR.mul AR.one (getV AR SD 287 [] (SD.na.getD 287 0)) (SD.nk.getD 287 1) 1 CFSG.KD.Fi24Alpha.Pc.a287_1 true) CFSG.KD.Fi24Alpha.Pc.v287 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v288 : Nat := CFSG.KD.Fi24Alpha.KV2 60
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v289 : Nat := CFSG.KD.Fi24Alpha.KV2 61
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l288 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v287]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l290 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v287, CFSG.KD.Fi24Alpha.Pc.v288, CFSG.KD.Fi24Alpha.Pc.v289]
theorem CFSG.KD.Fi24Alpha.Pc.p288 : Nat.beq (runC AR SD 287 (ckL CFSG.KD.Fi24Alpha.Pc.l290) 2 288 CFSG.KD.Fi24Alpha.Pc.l288) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v290 : Nat := CFSG.KD.Fi24Alpha.KV2 62
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v291 : Nat := CFSG.KD.Fi24Alpha.KV2 63
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l292 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v287, CFSG.KD.Fi24Alpha.Pc.v288, CFSG.KD.Fi24Alpha.Pc.v289, CFSG.KD.Fi24Alpha.Pc.v290, CFSG.KD.Fi24Alpha.Pc.v291]
theorem CFSG.KD.Fi24Alpha.Pc.p290 : Nat.beq (runC AR SD 287 (ckL CFSG.KD.Fi24Alpha.Pc.l292) 2 290 CFSG.KD.Fi24Alpha.Pc.l290) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v292 : Nat := CFSG.KD.Fi24Alpha.KV2 64
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v293 : Nat := CFSG.KD.Fi24Alpha.KV2 65
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l294 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v287, CFSG.KD.Fi24Alpha.Pc.v288, CFSG.KD.Fi24Alpha.Pc.v289, CFSG.KD.Fi24Alpha.Pc.v290, CFSG.KD.Fi24Alpha.Pc.v291, CFSG.KD.Fi24Alpha.Pc.v292, CFSG.KD.Fi24Alpha.Pc.v293]
theorem CFSG.KD.Fi24Alpha.Pc.p292 : Nat.beq (runC AR SD 287 (ckL CFSG.KD.Fi24Alpha.Pc.l294) 2 292 CFSG.KD.Fi24Alpha.Pc.l292) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v294 : Nat := CFSG.KD.Fi24Alpha.KV2 66
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v295 : Nat := CFSG.KD.Fi24Alpha.KV2 67
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l296 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v287, CFSG.KD.Fi24Alpha.Pc.v288, CFSG.KD.Fi24Alpha.Pc.v289, CFSG.KD.Fi24Alpha.Pc.v290, CFSG.KD.Fi24Alpha.Pc.v291, CFSG.KD.Fi24Alpha.Pc.v292, CFSG.KD.Fi24Alpha.Pc.v293, CFSG.KD.Fi24Alpha.Pc.v294, CFSG.KD.Fi24Alpha.Pc.v295]
theorem CFSG.KD.Fi24Alpha.Pc.p294 : Nat.beq (runC AR SD 287 (ckL CFSG.KD.Fi24Alpha.Pc.l296) 2 294 CFSG.KD.Fi24Alpha.Pc.l294) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v296 : Nat := CFSG.KD.Fi24Alpha.KV2 68
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v297 : Nat := CFSG.KD.Fi24Alpha.KV2 69
theorem CFSG.KD.Fi24Alpha.Pc.f24 : Nat.beq (runC AR SD 287 (finC AR SD (nat_lit 24) 287 298) 2 296 CFSG.KD.Fi24Alpha.Pc.l296) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk24 : chk (nat_lit 24) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 24) (lo := 287) (hi := 298) (m := 11) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 11) (m2 := 10) (j2 := 288) (Lr := CFSG.KD.Fi24Alpha.Pc.l288) ((nodeV_pow (R := AR) (D := SD) (lo := 287) (L := []) (j := 287) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 287 [] (SD.na.getD 287 0)) (SD.nk.getD 287 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q287_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Alpha.Pc.q287_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r287))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 290) CFSG.KD.Fi24Alpha.Pc.p288 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 292) CFSG.KD.Fi24Alpha.Pc.p290 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 294) CFSG.KD.Fi24Alpha.Pc.p292 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 296) CFSG.KD.Fi24Alpha.Pc.p294 rfl rfl))))))).trans CFSG.KD.Fi24Alpha.Pc.f24

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a298_2 : Nat := CFSG.KD.Fi24Alpha.KV2 70
theorem CFSG.KD.Fi24Alpha.Pc.q298_2 : Nat.beq (powTop AR.mul (getV AR SD 298 [] (SD.na.getD 298 0)) (SD.nk.getD 298 1) 2 (ckP CFSG.KD.Fi24Alpha.Pc.a298_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a298_1 : Nat := CFSG.KD.Fi24Alpha.KV2 71
theorem CFSG.KD.Fi24Alpha.Pc.q298_1 : Nat.beq (powTop AR.mul (getV AR SD 298 [] (SD.na.getD 298 0)) (SD.nk.getD 298 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a298_1) 1 CFSG.KD.Fi24Alpha.Pc.a298_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v298 : Nat := CFSG.KD.Fi24Alpha.KV2 72
theorem CFSG.KD.Fi24Alpha.Pc.r298 : Nat.beq (powR AR.mul AR.one (getV AR SD 298 [] (SD.na.getD 298 0)) (SD.nk.getD 298 1) 1 CFSG.KD.Fi24Alpha.Pc.a298_1 true) CFSG.KD.Fi24Alpha.Pc.v298 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v299 : Nat := CFSG.KD.Fi24Alpha.KV2 73
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v300 : Nat := CFSG.KD.Fi24Alpha.KV2 74
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l299 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v298]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l301 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v298, CFSG.KD.Fi24Alpha.Pc.v299, CFSG.KD.Fi24Alpha.Pc.v300]
theorem CFSG.KD.Fi24Alpha.Pc.p299 : Nat.beq (runC AR SD 298 (ckL CFSG.KD.Fi24Alpha.Pc.l301) 2 299 CFSG.KD.Fi24Alpha.Pc.l299) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v301 : Nat := CFSG.KD.Fi24Alpha.KV2 75
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l302 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v298, CFSG.KD.Fi24Alpha.Pc.v299, CFSG.KD.Fi24Alpha.Pc.v300, CFSG.KD.Fi24Alpha.Pc.v301]
theorem CFSG.KD.Fi24Alpha.Pc.p301 : Nat.beq (runC AR SD 298 (ckL CFSG.KD.Fi24Alpha.Pc.l302) 1 301 CFSG.KD.Fi24Alpha.Pc.l301) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a302_1 : Nat := CFSG.KD.Fi24Alpha.KV2 76
theorem CFSG.KD.Fi24Alpha.Pc.q302_1 : Nat.beq (powTop AR.mul (getV AR SD 298 CFSG.KD.Fi24Alpha.Pc.l302 (SD.na.getD 302 0)) (SD.nk.getD 302 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a302_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v302 : Nat := CFSG.KD.Fi24Alpha.KV2 77
theorem CFSG.KD.Fi24Alpha.Pc.r302 : Nat.beq (powR AR.mul AR.one (getV AR SD 298 CFSG.KD.Fi24Alpha.Pc.l302 (SD.na.getD 302 0)) (SD.nk.getD 302 1) 1 CFSG.KD.Fi24Alpha.Pc.a302_1 true) CFSG.KD.Fi24Alpha.Pc.v302 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v303 : Nat := CFSG.KD.Fi24Alpha.KV2 78
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v304 : Nat := CFSG.KD.Fi24Alpha.KV2 79
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l303 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v298, CFSG.KD.Fi24Alpha.Pc.v299, CFSG.KD.Fi24Alpha.Pc.v300, CFSG.KD.Fi24Alpha.Pc.v301, CFSG.KD.Fi24Alpha.Pc.v302]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l305 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v298, CFSG.KD.Fi24Alpha.Pc.v299, CFSG.KD.Fi24Alpha.Pc.v300, CFSG.KD.Fi24Alpha.Pc.v301, CFSG.KD.Fi24Alpha.Pc.v302, CFSG.KD.Fi24Alpha.Pc.v303, CFSG.KD.Fi24Alpha.Pc.v304]
theorem CFSG.KD.Fi24Alpha.Pc.p303 : Nat.beq (runC AR SD 298 (ckL CFSG.KD.Fi24Alpha.Pc.l305) 2 303 CFSG.KD.Fi24Alpha.Pc.l303) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v305 : Nat := CFSG.KD.Fi24Alpha.KV2 80
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v306 : Nat := CFSG.KD.Fi24Alpha.KV2 81
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l307 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v298, CFSG.KD.Fi24Alpha.Pc.v299, CFSG.KD.Fi24Alpha.Pc.v300, CFSG.KD.Fi24Alpha.Pc.v301, CFSG.KD.Fi24Alpha.Pc.v302, CFSG.KD.Fi24Alpha.Pc.v303, CFSG.KD.Fi24Alpha.Pc.v304, CFSG.KD.Fi24Alpha.Pc.v305, CFSG.KD.Fi24Alpha.Pc.v306]
theorem CFSG.KD.Fi24Alpha.Pc.p305 : Nat.beq (runC AR SD 298 (ckL CFSG.KD.Fi24Alpha.Pc.l307) 2 305 CFSG.KD.Fi24Alpha.Pc.l305) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v307 : Nat := CFSG.KD.Fi24Alpha.KV2 82
theorem CFSG.KD.Fi24Alpha.Pc.f25 : Nat.beq (runC AR SD 298 (finC AR SD (nat_lit 25) 298 308) 1 307 CFSG.KD.Fi24Alpha.Pc.l307) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk25 : chk (nat_lit 25) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 25) (lo := 298) (hi := 308) (m := 10) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 10) (m2 := 9) (j2 := 299) (Lr := CFSG.KD.Fi24Alpha.Pc.l299) ((nodeV_pow (R := AR) (D := SD) (lo := 298) (L := []) (j := 298) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 298 [] (SD.na.getD 298 0)) (SD.nk.getD 298 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q298_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Alpha.Pc.q298_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r298))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 301) CFSG.KD.Fi24Alpha.Pc.p299 rfl rfl).trans ((runC_seq (m := 7) (m2 := 6) (j2 := 302) CFSG.KD.Fi24Alpha.Pc.p301 rfl rfl).trans ((runC_node (m := 6) (m2 := 5) (j2 := 303) (Lr := CFSG.KD.Fi24Alpha.Pc.l303) ((nodeV_pow (R := AR) (D := SD) (lo := 298) (L := CFSG.KD.Fi24Alpha.Pc.l302) (j := 302) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 298 CFSG.KD.Fi24Alpha.Pc.l302 (SD.na.getD 302 0)) (SD.nk.getD 302 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q302_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r302)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 305) CFSG.KD.Fi24Alpha.Pc.p303 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 307) CFSG.KD.Fi24Alpha.Pc.p305 rfl rfl)))))))).trans CFSG.KD.Fi24Alpha.Pc.f25

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v308 : Nat := CFSG.KD.Fi24Alpha.KV2 83
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v309 : Nat := CFSG.KD.Fi24Alpha.KV2 84
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l310 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v308, CFSG.KD.Fi24Alpha.Pc.v309]
theorem CFSG.KD.Fi24Alpha.Pc.p308 : Nat.beq (runC AR SD 308 (ckL CFSG.KD.Fi24Alpha.Pc.l310) 2 308 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v310 : Nat := CFSG.KD.Fi24Alpha.KV2 85
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v311 : Nat := CFSG.KD.Fi24Alpha.KV2 86
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l312 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v308, CFSG.KD.Fi24Alpha.Pc.v309, CFSG.KD.Fi24Alpha.Pc.v310, CFSG.KD.Fi24Alpha.Pc.v311]
theorem CFSG.KD.Fi24Alpha.Pc.p310 : Nat.beq (runC AR SD 308 (ckL CFSG.KD.Fi24Alpha.Pc.l312) 2 310 CFSG.KD.Fi24Alpha.Pc.l310) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v312 : Nat := CFSG.KD.Fi24Alpha.KV2 87
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v313 : Nat := CFSG.KD.Fi24Alpha.KV2 88
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l314 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v308, CFSG.KD.Fi24Alpha.Pc.v309, CFSG.KD.Fi24Alpha.Pc.v310, CFSG.KD.Fi24Alpha.Pc.v311, CFSG.KD.Fi24Alpha.Pc.v312, CFSG.KD.Fi24Alpha.Pc.v313]
theorem CFSG.KD.Fi24Alpha.Pc.p312 : Nat.beq (runC AR SD 308 (ckL CFSG.KD.Fi24Alpha.Pc.l314) 2 312 CFSG.KD.Fi24Alpha.Pc.l312) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v314 : Nat := CFSG.KD.Fi24Alpha.KV2 89
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v315 : Nat := CFSG.KD.Fi24Alpha.KV2 90
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l316 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v308, CFSG.KD.Fi24Alpha.Pc.v309, CFSG.KD.Fi24Alpha.Pc.v310, CFSG.KD.Fi24Alpha.Pc.v311, CFSG.KD.Fi24Alpha.Pc.v312, CFSG.KD.Fi24Alpha.Pc.v313, CFSG.KD.Fi24Alpha.Pc.v314, CFSG.KD.Fi24Alpha.Pc.v315]
theorem CFSG.KD.Fi24Alpha.Pc.p314 : Nat.beq (runC AR SD 308 (ckL CFSG.KD.Fi24Alpha.Pc.l316) 2 314 CFSG.KD.Fi24Alpha.Pc.l314) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v316 : Nat := CFSG.KD.Fi24Alpha.KV2 91
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v317 : Nat := CFSG.KD.Fi24Alpha.KV2 92
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l318 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v308, CFSG.KD.Fi24Alpha.Pc.v309, CFSG.KD.Fi24Alpha.Pc.v310, CFSG.KD.Fi24Alpha.Pc.v311, CFSG.KD.Fi24Alpha.Pc.v312, CFSG.KD.Fi24Alpha.Pc.v313, CFSG.KD.Fi24Alpha.Pc.v314, CFSG.KD.Fi24Alpha.Pc.v315, CFSG.KD.Fi24Alpha.Pc.v316, CFSG.KD.Fi24Alpha.Pc.v317]
theorem CFSG.KD.Fi24Alpha.Pc.p316 : Nat.beq (runC AR SD 308 (ckL CFSG.KD.Fi24Alpha.Pc.l318) 2 316 CFSG.KD.Fi24Alpha.Pc.l316) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v318 : Nat := CFSG.KD.Fi24Alpha.KV2 93
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v319 : Nat := CFSG.KD.Fi24Alpha.KV2 94
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l320 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v308, CFSG.KD.Fi24Alpha.Pc.v309, CFSG.KD.Fi24Alpha.Pc.v310, CFSG.KD.Fi24Alpha.Pc.v311, CFSG.KD.Fi24Alpha.Pc.v312, CFSG.KD.Fi24Alpha.Pc.v313, CFSG.KD.Fi24Alpha.Pc.v314, CFSG.KD.Fi24Alpha.Pc.v315, CFSG.KD.Fi24Alpha.Pc.v316, CFSG.KD.Fi24Alpha.Pc.v317, CFSG.KD.Fi24Alpha.Pc.v318, CFSG.KD.Fi24Alpha.Pc.v319]
theorem CFSG.KD.Fi24Alpha.Pc.p318 : Nat.beq (runC AR SD 308 (ckL CFSG.KD.Fi24Alpha.Pc.l320) 2 318 CFSG.KD.Fi24Alpha.Pc.l318) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v320 : Nat := CFSG.KD.Fi24Alpha.KV2 95
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v321 : Nat := CFSG.KD.Fi24Alpha.KV2 96
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l322 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v308, CFSG.KD.Fi24Alpha.Pc.v309, CFSG.KD.Fi24Alpha.Pc.v310, CFSG.KD.Fi24Alpha.Pc.v311, CFSG.KD.Fi24Alpha.Pc.v312, CFSG.KD.Fi24Alpha.Pc.v313, CFSG.KD.Fi24Alpha.Pc.v314, CFSG.KD.Fi24Alpha.Pc.v315, CFSG.KD.Fi24Alpha.Pc.v316, CFSG.KD.Fi24Alpha.Pc.v317, CFSG.KD.Fi24Alpha.Pc.v318, CFSG.KD.Fi24Alpha.Pc.v319, CFSG.KD.Fi24Alpha.Pc.v320, CFSG.KD.Fi24Alpha.Pc.v321]
theorem CFSG.KD.Fi24Alpha.Pc.p320 : Nat.beq (runC AR SD 308 (ckL CFSG.KD.Fi24Alpha.Pc.l322) 2 320 CFSG.KD.Fi24Alpha.Pc.l320) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v322 : Nat := CFSG.KD.Fi24Alpha.KV2 97
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v323 : Nat := CFSG.KD.Fi24Alpha.KV2 98
theorem CFSG.KD.Fi24Alpha.Pc.f26 : Nat.beq (runC AR SD 308 (finC AR SD (nat_lit 26) 308 324) 2 322 CFSG.KD.Fi24Alpha.Pc.l322) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk26 : chk (nat_lit 26) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 26) (lo := 308) (hi := 324) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 310) CFSG.KD.Fi24Alpha.Pc.p308 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 312) CFSG.KD.Fi24Alpha.Pc.p310 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 314) CFSG.KD.Fi24Alpha.Pc.p312 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 316) CFSG.KD.Fi24Alpha.Pc.p314 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 318) CFSG.KD.Fi24Alpha.Pc.p316 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 320) CFSG.KD.Fi24Alpha.Pc.p318 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 322) CFSG.KD.Fi24Alpha.Pc.p320 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f26

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v324 : Nat := CFSG.KD.Fi24Alpha.KV2 99
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v325 : Nat := CFSG.KD.Fi24Alpha.KV2 100
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l326 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v324, CFSG.KD.Fi24Alpha.Pc.v325]
theorem CFSG.KD.Fi24Alpha.Pc.p324 : Nat.beq (runC AR SD 324 (ckL CFSG.KD.Fi24Alpha.Pc.l326) 2 324 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v326 : Nat := CFSG.KD.Fi24Alpha.KV2 101
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v327 : Nat := CFSG.KD.Fi24Alpha.KV2 102
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l328 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v324, CFSG.KD.Fi24Alpha.Pc.v325, CFSG.KD.Fi24Alpha.Pc.v326, CFSG.KD.Fi24Alpha.Pc.v327]
theorem CFSG.KD.Fi24Alpha.Pc.p326 : Nat.beq (runC AR SD 324 (ckL CFSG.KD.Fi24Alpha.Pc.l328) 2 326 CFSG.KD.Fi24Alpha.Pc.l326) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v328 : Nat := CFSG.KD.Fi24Alpha.KV2 103
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v329 : Nat := CFSG.KD.Fi24Alpha.KV2 104
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l330 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v324, CFSG.KD.Fi24Alpha.Pc.v325, CFSG.KD.Fi24Alpha.Pc.v326, CFSG.KD.Fi24Alpha.Pc.v327, CFSG.KD.Fi24Alpha.Pc.v328, CFSG.KD.Fi24Alpha.Pc.v329]
theorem CFSG.KD.Fi24Alpha.Pc.p328 : Nat.beq (runC AR SD 324 (ckL CFSG.KD.Fi24Alpha.Pc.l330) 2 328 CFSG.KD.Fi24Alpha.Pc.l328) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v330 : Nat := CFSG.KD.Fi24Alpha.KV2 105
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v331 : Nat := CFSG.KD.Fi24Alpha.KV2 106
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l332 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v324, CFSG.KD.Fi24Alpha.Pc.v325, CFSG.KD.Fi24Alpha.Pc.v326, CFSG.KD.Fi24Alpha.Pc.v327, CFSG.KD.Fi24Alpha.Pc.v328, CFSG.KD.Fi24Alpha.Pc.v329, CFSG.KD.Fi24Alpha.Pc.v330, CFSG.KD.Fi24Alpha.Pc.v331]
theorem CFSG.KD.Fi24Alpha.Pc.p330 : Nat.beq (runC AR SD 324 (ckL CFSG.KD.Fi24Alpha.Pc.l332) 2 330 CFSG.KD.Fi24Alpha.Pc.l330) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v332 : Nat := CFSG.KD.Fi24Alpha.KV2 107
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v333 : Nat := CFSG.KD.Fi24Alpha.KV2 108
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l334 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v324, CFSG.KD.Fi24Alpha.Pc.v325, CFSG.KD.Fi24Alpha.Pc.v326, CFSG.KD.Fi24Alpha.Pc.v327, CFSG.KD.Fi24Alpha.Pc.v328, CFSG.KD.Fi24Alpha.Pc.v329, CFSG.KD.Fi24Alpha.Pc.v330, CFSG.KD.Fi24Alpha.Pc.v331, CFSG.KD.Fi24Alpha.Pc.v332, CFSG.KD.Fi24Alpha.Pc.v333]
theorem CFSG.KD.Fi24Alpha.Pc.p332 : Nat.beq (runC AR SD 324 (ckL CFSG.KD.Fi24Alpha.Pc.l334) 2 332 CFSG.KD.Fi24Alpha.Pc.l332) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v334 : Nat := CFSG.KD.Fi24Alpha.KV2 109
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v335 : Nat := CFSG.KD.Fi24Alpha.KV2 110
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l336 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v324, CFSG.KD.Fi24Alpha.Pc.v325, CFSG.KD.Fi24Alpha.Pc.v326, CFSG.KD.Fi24Alpha.Pc.v327, CFSG.KD.Fi24Alpha.Pc.v328, CFSG.KD.Fi24Alpha.Pc.v329, CFSG.KD.Fi24Alpha.Pc.v330, CFSG.KD.Fi24Alpha.Pc.v331, CFSG.KD.Fi24Alpha.Pc.v332, CFSG.KD.Fi24Alpha.Pc.v333, CFSG.KD.Fi24Alpha.Pc.v334, CFSG.KD.Fi24Alpha.Pc.v335]
theorem CFSG.KD.Fi24Alpha.Pc.p334 : Nat.beq (runC AR SD 324 (ckL CFSG.KD.Fi24Alpha.Pc.l336) 2 334 CFSG.KD.Fi24Alpha.Pc.l334) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v336 : Nat := CFSG.KD.Fi24Alpha.KV2 111
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v337 : Nat := CFSG.KD.Fi24Alpha.KV2 112
theorem CFSG.KD.Fi24Alpha.Pc.f27 : Nat.beq (runC AR SD 324 (finC AR SD (nat_lit 27) 324 338) 2 336 CFSG.KD.Fi24Alpha.Pc.l336) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk27 : chk (nat_lit 27) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 27) (lo := 324) (hi := 338) (m := 14) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 14) (m2 := 12) (j2 := 326) CFSG.KD.Fi24Alpha.Pc.p324 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 328) CFSG.KD.Fi24Alpha.Pc.p326 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 330) CFSG.KD.Fi24Alpha.Pc.p328 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 332) CFSG.KD.Fi24Alpha.Pc.p330 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 334) CFSG.KD.Fi24Alpha.Pc.p332 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 336) CFSG.KD.Fi24Alpha.Pc.p334 rfl rfl)))))))).trans CFSG.KD.Fi24Alpha.Pc.f27

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.a338_1 : Nat := CFSG.KD.Fi24Alpha.KV2 113
theorem CFSG.KD.Fi24Alpha.Pc.q338_1 : Nat.beq (powTop AR.mul (getV AR SD 338 [] (SD.na.getD 338 0)) (SD.nk.getD 338 1) 1 (ckP CFSG.KD.Fi24Alpha.Pc.a338_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v338 : Nat := CFSG.KD.Fi24Alpha.KV2 114
theorem CFSG.KD.Fi24Alpha.Pc.r338 : Nat.beq (powR AR.mul AR.one (getV AR SD 338 [] (SD.na.getD 338 0)) (SD.nk.getD 338 1) 1 CFSG.KD.Fi24Alpha.Pc.a338_1 true) CFSG.KD.Fi24Alpha.Pc.v338 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v339 : Nat := CFSG.KD.Fi24Alpha.KV2 115
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v340 : Nat := CFSG.KD.Fi24Alpha.KV2 116
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l339 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v338]
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l341 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v338, CFSG.KD.Fi24Alpha.Pc.v339, CFSG.KD.Fi24Alpha.Pc.v340]
theorem CFSG.KD.Fi24Alpha.Pc.p339 : Nat.beq (runC AR SD 338 (ckL CFSG.KD.Fi24Alpha.Pc.l341) 2 339 CFSG.KD.Fi24Alpha.Pc.l339) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v341 : Nat := CFSG.KD.Fi24Alpha.KV2 117
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v342 : Nat := CFSG.KD.Fi24Alpha.KV2 118
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l343 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v338, CFSG.KD.Fi24Alpha.Pc.v339, CFSG.KD.Fi24Alpha.Pc.v340, CFSG.KD.Fi24Alpha.Pc.v341, CFSG.KD.Fi24Alpha.Pc.v342]
theorem CFSG.KD.Fi24Alpha.Pc.p341 : Nat.beq (runC AR SD 338 (ckL CFSG.KD.Fi24Alpha.Pc.l343) 2 341 CFSG.KD.Fi24Alpha.Pc.l341) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v343 : Nat := CFSG.KD.Fi24Alpha.KV2 119
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v344 : Nat := CFSG.KD.Fi24Alpha.KV2 120
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l345 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v338, CFSG.KD.Fi24Alpha.Pc.v339, CFSG.KD.Fi24Alpha.Pc.v340, CFSG.KD.Fi24Alpha.Pc.v341, CFSG.KD.Fi24Alpha.Pc.v342, CFSG.KD.Fi24Alpha.Pc.v343, CFSG.KD.Fi24Alpha.Pc.v344]
theorem CFSG.KD.Fi24Alpha.Pc.p343 : Nat.beq (runC AR SD 338 (ckL CFSG.KD.Fi24Alpha.Pc.l345) 2 343 CFSG.KD.Fi24Alpha.Pc.l343) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v345 : Nat := CFSG.KD.Fi24Alpha.KV2 121
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v346 : Nat := CFSG.KD.Fi24Alpha.KV2 122
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l347 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v338, CFSG.KD.Fi24Alpha.Pc.v339, CFSG.KD.Fi24Alpha.Pc.v340, CFSG.KD.Fi24Alpha.Pc.v341, CFSG.KD.Fi24Alpha.Pc.v342, CFSG.KD.Fi24Alpha.Pc.v343, CFSG.KD.Fi24Alpha.Pc.v344, CFSG.KD.Fi24Alpha.Pc.v345, CFSG.KD.Fi24Alpha.Pc.v346]
theorem CFSG.KD.Fi24Alpha.Pc.p345 : Nat.beq (runC AR SD 338 (ckL CFSG.KD.Fi24Alpha.Pc.l347) 2 345 CFSG.KD.Fi24Alpha.Pc.l345) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v347 : Nat := CFSG.KD.Fi24Alpha.KV2 123
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v348 : Nat := CFSG.KD.Fi24Alpha.KV2 124
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l349 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v338, CFSG.KD.Fi24Alpha.Pc.v339, CFSG.KD.Fi24Alpha.Pc.v340, CFSG.KD.Fi24Alpha.Pc.v341, CFSG.KD.Fi24Alpha.Pc.v342, CFSG.KD.Fi24Alpha.Pc.v343, CFSG.KD.Fi24Alpha.Pc.v344, CFSG.KD.Fi24Alpha.Pc.v345, CFSG.KD.Fi24Alpha.Pc.v346, CFSG.KD.Fi24Alpha.Pc.v347, CFSG.KD.Fi24Alpha.Pc.v348]
theorem CFSG.KD.Fi24Alpha.Pc.p347 : Nat.beq (runC AR SD 338 (ckL CFSG.KD.Fi24Alpha.Pc.l349) 2 347 CFSG.KD.Fi24Alpha.Pc.l347) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v349 : Nat := CFSG.KD.Fi24Alpha.KV2 125
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v350 : Nat := CFSG.KD.Fi24Alpha.KV2 126
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l351 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v338, CFSG.KD.Fi24Alpha.Pc.v339, CFSG.KD.Fi24Alpha.Pc.v340, CFSG.KD.Fi24Alpha.Pc.v341, CFSG.KD.Fi24Alpha.Pc.v342, CFSG.KD.Fi24Alpha.Pc.v343, CFSG.KD.Fi24Alpha.Pc.v344, CFSG.KD.Fi24Alpha.Pc.v345, CFSG.KD.Fi24Alpha.Pc.v346, CFSG.KD.Fi24Alpha.Pc.v347, CFSG.KD.Fi24Alpha.Pc.v348, CFSG.KD.Fi24Alpha.Pc.v349, CFSG.KD.Fi24Alpha.Pc.v350]
theorem CFSG.KD.Fi24Alpha.Pc.p349 : Nat.beq (runC AR SD 338 (ckL CFSG.KD.Fi24Alpha.Pc.l351) 2 349 CFSG.KD.Fi24Alpha.Pc.l349) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v351 : Nat := CFSG.KD.Fi24Alpha.KV2 127
theorem CFSG.KD.Fi24Alpha.Pc.f28 : Nat.beq (runC AR SD 338 (finC AR SD (nat_lit 28) 338 352) 1 351 CFSG.KD.Fi24Alpha.Pc.l351) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk28 : chk (nat_lit 28) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 28) (lo := 338) (hi := 352) (m := 14) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 14) (m2 := 13) (j2 := 339) (Lr := CFSG.KD.Fi24Alpha.Pc.l339) ((nodeV_pow (R := AR) (D := SD) (lo := 338) (L := []) (j := 338) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 338 [] (SD.na.getD 338 0)) (SD.nk.getD 338 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Alpha.Pc.q338_1 rfl).trans (powR_last CFSG.KD.Fi24Alpha.Pc.r338)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 341) CFSG.KD.Fi24Alpha.Pc.p339 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 343) CFSG.KD.Fi24Alpha.Pc.p341 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 345) CFSG.KD.Fi24Alpha.Pc.p343 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 347) CFSG.KD.Fi24Alpha.Pc.p345 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 349) CFSG.KD.Fi24Alpha.Pc.p347 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 351) CFSG.KD.Fi24Alpha.Pc.p349 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f28

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v352 : Nat := CFSG.KD.Fi24Alpha.KV2 128
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v353 : Nat := CFSG.KD.Fi24Alpha.KV2 129
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l354 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v352, CFSG.KD.Fi24Alpha.Pc.v353]
theorem CFSG.KD.Fi24Alpha.Pc.p352 : Nat.beq (runC AR SD 352 (ckL CFSG.KD.Fi24Alpha.Pc.l354) 2 352 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v354 : Nat := CFSG.KD.Fi24Alpha.KV2 130
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v355 : Nat := CFSG.KD.Fi24Alpha.KV2 131
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l356 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v352, CFSG.KD.Fi24Alpha.Pc.v353, CFSG.KD.Fi24Alpha.Pc.v354, CFSG.KD.Fi24Alpha.Pc.v355]
theorem CFSG.KD.Fi24Alpha.Pc.p354 : Nat.beq (runC AR SD 352 (ckL CFSG.KD.Fi24Alpha.Pc.l356) 2 354 CFSG.KD.Fi24Alpha.Pc.l354) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v356 : Nat := CFSG.KD.Fi24Alpha.KV2 132
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v357 : Nat := CFSG.KD.Fi24Alpha.KV2 133
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l358 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v352, CFSG.KD.Fi24Alpha.Pc.v353, CFSG.KD.Fi24Alpha.Pc.v354, CFSG.KD.Fi24Alpha.Pc.v355, CFSG.KD.Fi24Alpha.Pc.v356, CFSG.KD.Fi24Alpha.Pc.v357]
theorem CFSG.KD.Fi24Alpha.Pc.p356 : Nat.beq (runC AR SD 352 (ckL CFSG.KD.Fi24Alpha.Pc.l358) 2 356 CFSG.KD.Fi24Alpha.Pc.l356) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v358 : Nat := CFSG.KD.Fi24Alpha.KV2 134
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v359 : Nat := CFSG.KD.Fi24Alpha.KV2 135
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l360 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v352, CFSG.KD.Fi24Alpha.Pc.v353, CFSG.KD.Fi24Alpha.Pc.v354, CFSG.KD.Fi24Alpha.Pc.v355, CFSG.KD.Fi24Alpha.Pc.v356, CFSG.KD.Fi24Alpha.Pc.v357, CFSG.KD.Fi24Alpha.Pc.v358, CFSG.KD.Fi24Alpha.Pc.v359]
theorem CFSG.KD.Fi24Alpha.Pc.p358 : Nat.beq (runC AR SD 352 (ckL CFSG.KD.Fi24Alpha.Pc.l360) 2 358 CFSG.KD.Fi24Alpha.Pc.l358) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v360 : Nat := CFSG.KD.Fi24Alpha.KV2 136
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v361 : Nat := CFSG.KD.Fi24Alpha.KV2 137
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l362 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v352, CFSG.KD.Fi24Alpha.Pc.v353, CFSG.KD.Fi24Alpha.Pc.v354, CFSG.KD.Fi24Alpha.Pc.v355, CFSG.KD.Fi24Alpha.Pc.v356, CFSG.KD.Fi24Alpha.Pc.v357, CFSG.KD.Fi24Alpha.Pc.v358, CFSG.KD.Fi24Alpha.Pc.v359, CFSG.KD.Fi24Alpha.Pc.v360, CFSG.KD.Fi24Alpha.Pc.v361]
theorem CFSG.KD.Fi24Alpha.Pc.p360 : Nat.beq (runC AR SD 352 (ckL CFSG.KD.Fi24Alpha.Pc.l362) 2 360 CFSG.KD.Fi24Alpha.Pc.l360) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v362 : Nat := CFSG.KD.Fi24Alpha.KV2 138
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v363 : Nat := CFSG.KD.Fi24Alpha.KV2 139
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l364 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v352, CFSG.KD.Fi24Alpha.Pc.v353, CFSG.KD.Fi24Alpha.Pc.v354, CFSG.KD.Fi24Alpha.Pc.v355, CFSG.KD.Fi24Alpha.Pc.v356, CFSG.KD.Fi24Alpha.Pc.v357, CFSG.KD.Fi24Alpha.Pc.v358, CFSG.KD.Fi24Alpha.Pc.v359, CFSG.KD.Fi24Alpha.Pc.v360, CFSG.KD.Fi24Alpha.Pc.v361, CFSG.KD.Fi24Alpha.Pc.v362, CFSG.KD.Fi24Alpha.Pc.v363]
theorem CFSG.KD.Fi24Alpha.Pc.p362 : Nat.beq (runC AR SD 352 (ckL CFSG.KD.Fi24Alpha.Pc.l364) 2 362 CFSG.KD.Fi24Alpha.Pc.l362) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v364 : Nat := CFSG.KD.Fi24Alpha.KV2 140
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v365 : Nat := CFSG.KD.Fi24Alpha.KV2 141
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l366 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v352, CFSG.KD.Fi24Alpha.Pc.v353, CFSG.KD.Fi24Alpha.Pc.v354, CFSG.KD.Fi24Alpha.Pc.v355, CFSG.KD.Fi24Alpha.Pc.v356, CFSG.KD.Fi24Alpha.Pc.v357, CFSG.KD.Fi24Alpha.Pc.v358, CFSG.KD.Fi24Alpha.Pc.v359, CFSG.KD.Fi24Alpha.Pc.v360, CFSG.KD.Fi24Alpha.Pc.v361, CFSG.KD.Fi24Alpha.Pc.v362, CFSG.KD.Fi24Alpha.Pc.v363, CFSG.KD.Fi24Alpha.Pc.v364, CFSG.KD.Fi24Alpha.Pc.v365]
theorem CFSG.KD.Fi24Alpha.Pc.p364 : Nat.beq (runC AR SD 352 (ckL CFSG.KD.Fi24Alpha.Pc.l366) 2 364 CFSG.KD.Fi24Alpha.Pc.l364) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v366 : Nat := CFSG.KD.Fi24Alpha.KV2 142
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v367 : Nat := CFSG.KD.Fi24Alpha.KV2 143
theorem CFSG.KD.Fi24Alpha.Pc.f29 : Nat.beq (runC AR SD 352 (finC AR SD (nat_lit 29) 352 368) 2 366 CFSG.KD.Fi24Alpha.Pc.l366) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk29 : chk (nat_lit 29) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 29) (lo := 352) (hi := 368) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 354) CFSG.KD.Fi24Alpha.Pc.p352 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 356) CFSG.KD.Fi24Alpha.Pc.p354 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 358) CFSG.KD.Fi24Alpha.Pc.p356 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 360) CFSG.KD.Fi24Alpha.Pc.p358 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 362) CFSG.KD.Fi24Alpha.Pc.p360 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 364) CFSG.KD.Fi24Alpha.Pc.p362 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 366) CFSG.KD.Fi24Alpha.Pc.p364 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f29

end
