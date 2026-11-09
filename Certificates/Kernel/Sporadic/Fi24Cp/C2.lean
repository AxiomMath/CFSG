module

public import Certificates.Kernel.Sporadic.Fi24Cp.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Cp KV2 "Certificates/Kernel/Sporadic/Fi24Cp/data/v2.bin" 152491 4 22721159 5361718875037589063

public section

open CFSG.KD.Fi24Cp CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v238 : Nat := CFSG.KD.Fi24Cp.KV2 0
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v239 : Nat := CFSG.KD.Fi24Cp.KV2 1
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l240 : List Nat := [CFSG.KD.Fi24Cp.Pc.v238, CFSG.KD.Fi24Cp.Pc.v239]
theorem CFSG.KD.Fi24Cp.Pc.p238 : Nat.beq (runC AR SD 238 (ckL CFSG.KD.Fi24Cp.Pc.l240) 2 238 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v240 : Nat := CFSG.KD.Fi24Cp.KV2 2
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v241 : Nat := CFSG.KD.Fi24Cp.KV2 3
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l242 : List Nat := [CFSG.KD.Fi24Cp.Pc.v238, CFSG.KD.Fi24Cp.Pc.v239, CFSG.KD.Fi24Cp.Pc.v240, CFSG.KD.Fi24Cp.Pc.v241]
theorem CFSG.KD.Fi24Cp.Pc.p240 : Nat.beq (runC AR SD 238 (ckL CFSG.KD.Fi24Cp.Pc.l242) 2 240 CFSG.KD.Fi24Cp.Pc.l240) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v242 : Nat := CFSG.KD.Fi24Cp.KV2 4
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v243 : Nat := CFSG.KD.Fi24Cp.KV2 5
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l244 : List Nat := [CFSG.KD.Fi24Cp.Pc.v238, CFSG.KD.Fi24Cp.Pc.v239, CFSG.KD.Fi24Cp.Pc.v240, CFSG.KD.Fi24Cp.Pc.v241, CFSG.KD.Fi24Cp.Pc.v242, CFSG.KD.Fi24Cp.Pc.v243]
theorem CFSG.KD.Fi24Cp.Pc.p242 : Nat.beq (runC AR SD 238 (ckL CFSG.KD.Fi24Cp.Pc.l244) 2 242 CFSG.KD.Fi24Cp.Pc.l242) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v244 : Nat := CFSG.KD.Fi24Cp.KV2 6
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l245 : List Nat := [CFSG.KD.Fi24Cp.Pc.v238, CFSG.KD.Fi24Cp.Pc.v239, CFSG.KD.Fi24Cp.Pc.v240, CFSG.KD.Fi24Cp.Pc.v241, CFSG.KD.Fi24Cp.Pc.v242, CFSG.KD.Fi24Cp.Pc.v243, CFSG.KD.Fi24Cp.Pc.v244]
theorem CFSG.KD.Fi24Cp.Pc.p244 : Nat.beq (runC AR SD 238 (ckL CFSG.KD.Fi24Cp.Pc.l245) 1 244 CFSG.KD.Fi24Cp.Pc.l244) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a245_1 : Nat := CFSG.KD.Fi24Cp.KV2 7
theorem CFSG.KD.Fi24Cp.Pc.q245_1 : Nat.beq (powTop AR.mul (getV AR SD 238 CFSG.KD.Fi24Cp.Pc.l245 (SD.na.getD 245 0)) (SD.nk.getD 245 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a245_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v245 : Nat := CFSG.KD.Fi24Cp.KV2 8
theorem CFSG.KD.Fi24Cp.Pc.r245 : Nat.beq (powR AR.mul AR.one (getV AR SD 238 CFSG.KD.Fi24Cp.Pc.l245 (SD.na.getD 245 0)) (SD.nk.getD 245 1) 1 CFSG.KD.Fi24Cp.Pc.a245_1 true) CFSG.KD.Fi24Cp.Pc.v245 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v246 : Nat := CFSG.KD.Fi24Cp.KV2 9
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v247 : Nat := CFSG.KD.Fi24Cp.KV2 10
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l246 : List Nat := [CFSG.KD.Fi24Cp.Pc.v238, CFSG.KD.Fi24Cp.Pc.v239, CFSG.KD.Fi24Cp.Pc.v240, CFSG.KD.Fi24Cp.Pc.v241, CFSG.KD.Fi24Cp.Pc.v242, CFSG.KD.Fi24Cp.Pc.v243, CFSG.KD.Fi24Cp.Pc.v244, CFSG.KD.Fi24Cp.Pc.v245]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l248 : List Nat := [CFSG.KD.Fi24Cp.Pc.v238, CFSG.KD.Fi24Cp.Pc.v239, CFSG.KD.Fi24Cp.Pc.v240, CFSG.KD.Fi24Cp.Pc.v241, CFSG.KD.Fi24Cp.Pc.v242, CFSG.KD.Fi24Cp.Pc.v243, CFSG.KD.Fi24Cp.Pc.v244, CFSG.KD.Fi24Cp.Pc.v245, CFSG.KD.Fi24Cp.Pc.v246, CFSG.KD.Fi24Cp.Pc.v247]
theorem CFSG.KD.Fi24Cp.Pc.p246 : Nat.beq (runC AR SD 238 (ckL CFSG.KD.Fi24Cp.Pc.l248) 2 246 CFSG.KD.Fi24Cp.Pc.l246) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v248 : Nat := CFSG.KD.Fi24Cp.KV2 11
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v249 : Nat := CFSG.KD.Fi24Cp.KV2 12
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l250 : List Nat := [CFSG.KD.Fi24Cp.Pc.v238, CFSG.KD.Fi24Cp.Pc.v239, CFSG.KD.Fi24Cp.Pc.v240, CFSG.KD.Fi24Cp.Pc.v241, CFSG.KD.Fi24Cp.Pc.v242, CFSG.KD.Fi24Cp.Pc.v243, CFSG.KD.Fi24Cp.Pc.v244, CFSG.KD.Fi24Cp.Pc.v245, CFSG.KD.Fi24Cp.Pc.v246, CFSG.KD.Fi24Cp.Pc.v247, CFSG.KD.Fi24Cp.Pc.v248, CFSG.KD.Fi24Cp.Pc.v249]
theorem CFSG.KD.Fi24Cp.Pc.p248 : Nat.beq (runC AR SD 238 (ckL CFSG.KD.Fi24Cp.Pc.l250) 2 248 CFSG.KD.Fi24Cp.Pc.l248) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v250 : Nat := CFSG.KD.Fi24Cp.KV2 13
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v251 : Nat := CFSG.KD.Fi24Cp.KV2 14
theorem CFSG.KD.Fi24Cp.Pc.f20 : Nat.beq (runC AR SD 238 (finC AR SD (nat_lit 20) 238 252) 2 250 CFSG.KD.Fi24Cp.Pc.l250) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk20 : chk (nat_lit 20) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 20) (lo := 238) (hi := 252) (m := 14) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 14) (m2 := 12) (j2 := 240) CFSG.KD.Fi24Cp.Pc.p238 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 242) CFSG.KD.Fi24Cp.Pc.p240 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 244) CFSG.KD.Fi24Cp.Pc.p242 rfl rfl).trans ((runC_seq (m := 8) (m2 := 7) (j2 := 245) CFSG.KD.Fi24Cp.Pc.p244 rfl rfl).trans ((runC_node (m := 7) (m2 := 6) (j2 := 246) (Lr := CFSG.KD.Fi24Cp.Pc.l246) ((nodeV_pow (R := AR) (D := SD) (lo := 238) (L := CFSG.KD.Fi24Cp.Pc.l245) (j := 245) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 238 CFSG.KD.Fi24Cp.Pc.l245 (SD.na.getD 245 0)) (SD.nk.getD 245 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q245_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r245)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 248) CFSG.KD.Fi24Cp.Pc.p246 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 250) CFSG.KD.Fi24Cp.Pc.p248 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f20

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v252 : Nat := CFSG.KD.Fi24Cp.KV2 15
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v253 : Nat := CFSG.KD.Fi24Cp.KV2 16
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l254 : List Nat := [CFSG.KD.Fi24Cp.Pc.v252, CFSG.KD.Fi24Cp.Pc.v253]
theorem CFSG.KD.Fi24Cp.Pc.p252 : Nat.beq (runC AR SD 252 (ckL CFSG.KD.Fi24Cp.Pc.l254) 2 252 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v254 : Nat := CFSG.KD.Fi24Cp.KV2 17
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v255 : Nat := CFSG.KD.Fi24Cp.KV2 18
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l256 : List Nat := [CFSG.KD.Fi24Cp.Pc.v252, CFSG.KD.Fi24Cp.Pc.v253, CFSG.KD.Fi24Cp.Pc.v254, CFSG.KD.Fi24Cp.Pc.v255]
theorem CFSG.KD.Fi24Cp.Pc.p254 : Nat.beq (runC AR SD 252 (ckL CFSG.KD.Fi24Cp.Pc.l256) 2 254 CFSG.KD.Fi24Cp.Pc.l254) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v256 : Nat := CFSG.KD.Fi24Cp.KV2 19
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v257 : Nat := CFSG.KD.Fi24Cp.KV2 20
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l258 : List Nat := [CFSG.KD.Fi24Cp.Pc.v252, CFSG.KD.Fi24Cp.Pc.v253, CFSG.KD.Fi24Cp.Pc.v254, CFSG.KD.Fi24Cp.Pc.v255, CFSG.KD.Fi24Cp.Pc.v256, CFSG.KD.Fi24Cp.Pc.v257]
theorem CFSG.KD.Fi24Cp.Pc.p256 : Nat.beq (runC AR SD 252 (ckL CFSG.KD.Fi24Cp.Pc.l258) 2 256 CFSG.KD.Fi24Cp.Pc.l256) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v258 : Nat := CFSG.KD.Fi24Cp.KV2 21
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l259 : List Nat := [CFSG.KD.Fi24Cp.Pc.v252, CFSG.KD.Fi24Cp.Pc.v253, CFSG.KD.Fi24Cp.Pc.v254, CFSG.KD.Fi24Cp.Pc.v255, CFSG.KD.Fi24Cp.Pc.v256, CFSG.KD.Fi24Cp.Pc.v257, CFSG.KD.Fi24Cp.Pc.v258]
theorem CFSG.KD.Fi24Cp.Pc.p258 : Nat.beq (runC AR SD 252 (ckL CFSG.KD.Fi24Cp.Pc.l259) 1 258 CFSG.KD.Fi24Cp.Pc.l258) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v259 : Nat := CFSG.KD.Fi24Cp.KV2 22
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v260 : Nat := CFSG.KD.Fi24Cp.KV2 23
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l261 : List Nat := [CFSG.KD.Fi24Cp.Pc.v252, CFSG.KD.Fi24Cp.Pc.v253, CFSG.KD.Fi24Cp.Pc.v254, CFSG.KD.Fi24Cp.Pc.v255, CFSG.KD.Fi24Cp.Pc.v256, CFSG.KD.Fi24Cp.Pc.v257, CFSG.KD.Fi24Cp.Pc.v258, CFSG.KD.Fi24Cp.Pc.v259, CFSG.KD.Fi24Cp.Pc.v260]
theorem CFSG.KD.Fi24Cp.Pc.p259 : Nat.beq (runC AR SD 252 (ckL CFSG.KD.Fi24Cp.Pc.l261) 2 259 CFSG.KD.Fi24Cp.Pc.l259) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v261 : Nat := CFSG.KD.Fi24Cp.KV2 24
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v262 : Nat := CFSG.KD.Fi24Cp.KV2 25
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l263 : List Nat := [CFSG.KD.Fi24Cp.Pc.v252, CFSG.KD.Fi24Cp.Pc.v253, CFSG.KD.Fi24Cp.Pc.v254, CFSG.KD.Fi24Cp.Pc.v255, CFSG.KD.Fi24Cp.Pc.v256, CFSG.KD.Fi24Cp.Pc.v257, CFSG.KD.Fi24Cp.Pc.v258, CFSG.KD.Fi24Cp.Pc.v259, CFSG.KD.Fi24Cp.Pc.v260, CFSG.KD.Fi24Cp.Pc.v261, CFSG.KD.Fi24Cp.Pc.v262]
theorem CFSG.KD.Fi24Cp.Pc.p261 : Nat.beq (runC AR SD 252 (ckL CFSG.KD.Fi24Cp.Pc.l263) 2 261 CFSG.KD.Fi24Cp.Pc.l261) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v263 : Nat := CFSG.KD.Fi24Cp.KV2 26
theorem CFSG.KD.Fi24Cp.Pc.f21 : Nat.beq (runC AR SD 252 (finC AR SD (nat_lit 21) 252 264) 1 263 CFSG.KD.Fi24Cp.Pc.l263) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk21 : chk (nat_lit 21) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 21) (lo := 252) (hi := 264) (m := 12) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 12) (m2 := 10) (j2 := 254) CFSG.KD.Fi24Cp.Pc.p252 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 256) CFSG.KD.Fi24Cp.Pc.p254 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 258) CFSG.KD.Fi24Cp.Pc.p256 rfl rfl).trans ((runC_seq (m := 6) (m2 := 5) (j2 := 259) CFSG.KD.Fi24Cp.Pc.p258 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 261) CFSG.KD.Fi24Cp.Pc.p259 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 263) CFSG.KD.Fi24Cp.Pc.p261 rfl rfl)))))))).trans CFSG.KD.Fi24Cp.Pc.f21

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a264_2 : Nat := CFSG.KD.Fi24Cp.KV2 27
theorem CFSG.KD.Fi24Cp.Pc.q264_2 : Nat.beq (powTop AR.mul (getV AR SD 264 [] (SD.na.getD 264 0)) (SD.nk.getD 264 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a264_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a264_1 : Nat := CFSG.KD.Fi24Cp.KV2 28
theorem CFSG.KD.Fi24Cp.Pc.q264_1 : Nat.beq (powTop AR.mul (getV AR SD 264 [] (SD.na.getD 264 0)) (SD.nk.getD 264 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a264_1) 1 CFSG.KD.Fi24Cp.Pc.a264_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v264 : Nat := CFSG.KD.Fi24Cp.KV2 29
theorem CFSG.KD.Fi24Cp.Pc.r264 : Nat.beq (powR AR.mul AR.one (getV AR SD 264 [] (SD.na.getD 264 0)) (SD.nk.getD 264 1) 1 CFSG.KD.Fi24Cp.Pc.a264_1 true) CFSG.KD.Fi24Cp.Pc.v264 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v265 : Nat := CFSG.KD.Fi24Cp.KV2 30
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v266 : Nat := CFSG.KD.Fi24Cp.KV2 31
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l265 : List Nat := [CFSG.KD.Fi24Cp.Pc.v264]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l267 : List Nat := [CFSG.KD.Fi24Cp.Pc.v264, CFSG.KD.Fi24Cp.Pc.v265, CFSG.KD.Fi24Cp.Pc.v266]
theorem CFSG.KD.Fi24Cp.Pc.p265 : Nat.beq (runC AR SD 264 (ckL CFSG.KD.Fi24Cp.Pc.l267) 2 265 CFSG.KD.Fi24Cp.Pc.l265) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v267 : Nat := CFSG.KD.Fi24Cp.KV2 32
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v268 : Nat := CFSG.KD.Fi24Cp.KV2 33
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l269 : List Nat := [CFSG.KD.Fi24Cp.Pc.v264, CFSG.KD.Fi24Cp.Pc.v265, CFSG.KD.Fi24Cp.Pc.v266, CFSG.KD.Fi24Cp.Pc.v267, CFSG.KD.Fi24Cp.Pc.v268]
theorem CFSG.KD.Fi24Cp.Pc.p267 : Nat.beq (runC AR SD 264 (ckL CFSG.KD.Fi24Cp.Pc.l269) 2 267 CFSG.KD.Fi24Cp.Pc.l267) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v269 : Nat := CFSG.KD.Fi24Cp.KV2 34
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v270 : Nat := CFSG.KD.Fi24Cp.KV2 35
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l271 : List Nat := [CFSG.KD.Fi24Cp.Pc.v264, CFSG.KD.Fi24Cp.Pc.v265, CFSG.KD.Fi24Cp.Pc.v266, CFSG.KD.Fi24Cp.Pc.v267, CFSG.KD.Fi24Cp.Pc.v268, CFSG.KD.Fi24Cp.Pc.v269, CFSG.KD.Fi24Cp.Pc.v270]
theorem CFSG.KD.Fi24Cp.Pc.p269 : Nat.beq (runC AR SD 264 (ckL CFSG.KD.Fi24Cp.Pc.l271) 2 269 CFSG.KD.Fi24Cp.Pc.l269) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v271 : Nat := CFSG.KD.Fi24Cp.KV2 36
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v272 : Nat := CFSG.KD.Fi24Cp.KV2 37
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l273 : List Nat := [CFSG.KD.Fi24Cp.Pc.v264, CFSG.KD.Fi24Cp.Pc.v265, CFSG.KD.Fi24Cp.Pc.v266, CFSG.KD.Fi24Cp.Pc.v267, CFSG.KD.Fi24Cp.Pc.v268, CFSG.KD.Fi24Cp.Pc.v269, CFSG.KD.Fi24Cp.Pc.v270, CFSG.KD.Fi24Cp.Pc.v271, CFSG.KD.Fi24Cp.Pc.v272]
theorem CFSG.KD.Fi24Cp.Pc.p271 : Nat.beq (runC AR SD 264 (ckL CFSG.KD.Fi24Cp.Pc.l273) 2 271 CFSG.KD.Fi24Cp.Pc.l271) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v273 : Nat := CFSG.KD.Fi24Cp.KV2 38
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v274 : Nat := CFSG.KD.Fi24Cp.KV2 39
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l275 : List Nat := [CFSG.KD.Fi24Cp.Pc.v264, CFSG.KD.Fi24Cp.Pc.v265, CFSG.KD.Fi24Cp.Pc.v266, CFSG.KD.Fi24Cp.Pc.v267, CFSG.KD.Fi24Cp.Pc.v268, CFSG.KD.Fi24Cp.Pc.v269, CFSG.KD.Fi24Cp.Pc.v270, CFSG.KD.Fi24Cp.Pc.v271, CFSG.KD.Fi24Cp.Pc.v272, CFSG.KD.Fi24Cp.Pc.v273, CFSG.KD.Fi24Cp.Pc.v274]
theorem CFSG.KD.Fi24Cp.Pc.p273 : Nat.beq (runC AR SD 264 (ckL CFSG.KD.Fi24Cp.Pc.l275) 2 273 CFSG.KD.Fi24Cp.Pc.l273) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v275 : Nat := CFSG.KD.Fi24Cp.KV2 40
theorem CFSG.KD.Fi24Cp.Pc.f22 : Nat.beq (runC AR SD 264 (finC AR SD (nat_lit 22) 264 276) 1 275 CFSG.KD.Fi24Cp.Pc.l275) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk22 : chk (nat_lit 22) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 22) (lo := 264) (hi := 276) (m := 12) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 12) (m2 := 11) (j2 := 265) (Lr := CFSG.KD.Fi24Cp.Pc.l265) ((nodeV_pow (R := AR) (D := SD) (lo := 264) (L := []) (j := 264) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 264 [] (SD.na.getD 264 0)) (SD.nk.getD 264 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q264_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q264_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r264))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 267) CFSG.KD.Fi24Cp.Pc.p265 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 269) CFSG.KD.Fi24Cp.Pc.p267 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 271) CFSG.KD.Fi24Cp.Pc.p269 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 273) CFSG.KD.Fi24Cp.Pc.p271 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 275) CFSG.KD.Fi24Cp.Pc.p273 rfl rfl)))))))).trans CFSG.KD.Fi24Cp.Pc.f22

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v276 : Nat := CFSG.KD.Fi24Cp.KV2 41
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v277 : Nat := CFSG.KD.Fi24Cp.KV2 42
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l278 : List Nat := [CFSG.KD.Fi24Cp.Pc.v276, CFSG.KD.Fi24Cp.Pc.v277]
theorem CFSG.KD.Fi24Cp.Pc.p276 : Nat.beq (runC AR SD 276 (ckL CFSG.KD.Fi24Cp.Pc.l278) 2 276 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v278 : Nat := CFSG.KD.Fi24Cp.KV2 43
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v279 : Nat := CFSG.KD.Fi24Cp.KV2 44
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l280 : List Nat := [CFSG.KD.Fi24Cp.Pc.v276, CFSG.KD.Fi24Cp.Pc.v277, CFSG.KD.Fi24Cp.Pc.v278, CFSG.KD.Fi24Cp.Pc.v279]
theorem CFSG.KD.Fi24Cp.Pc.p278 : Nat.beq (runC AR SD 276 (ckL CFSG.KD.Fi24Cp.Pc.l280) 2 278 CFSG.KD.Fi24Cp.Pc.l278) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v280 : Nat := CFSG.KD.Fi24Cp.KV2 45
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v281 : Nat := CFSG.KD.Fi24Cp.KV2 46
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l282 : List Nat := [CFSG.KD.Fi24Cp.Pc.v276, CFSG.KD.Fi24Cp.Pc.v277, CFSG.KD.Fi24Cp.Pc.v278, CFSG.KD.Fi24Cp.Pc.v279, CFSG.KD.Fi24Cp.Pc.v280, CFSG.KD.Fi24Cp.Pc.v281]
theorem CFSG.KD.Fi24Cp.Pc.p280 : Nat.beq (runC AR SD 276 (ckL CFSG.KD.Fi24Cp.Pc.l282) 2 280 CFSG.KD.Fi24Cp.Pc.l280) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v282 : Nat := CFSG.KD.Fi24Cp.KV2 47
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v283 : Nat := CFSG.KD.Fi24Cp.KV2 48
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l284 : List Nat := [CFSG.KD.Fi24Cp.Pc.v276, CFSG.KD.Fi24Cp.Pc.v277, CFSG.KD.Fi24Cp.Pc.v278, CFSG.KD.Fi24Cp.Pc.v279, CFSG.KD.Fi24Cp.Pc.v280, CFSG.KD.Fi24Cp.Pc.v281, CFSG.KD.Fi24Cp.Pc.v282, CFSG.KD.Fi24Cp.Pc.v283]
theorem CFSG.KD.Fi24Cp.Pc.p282 : Nat.beq (runC AR SD 276 (ckL CFSG.KD.Fi24Cp.Pc.l284) 2 282 CFSG.KD.Fi24Cp.Pc.l282) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a284_1 : Nat := CFSG.KD.Fi24Cp.KV2 49
theorem CFSG.KD.Fi24Cp.Pc.q284_1 : Nat.beq (powTop AR.mul (getV AR SD 276 CFSG.KD.Fi24Cp.Pc.l284 (SD.na.getD 284 0)) (SD.nk.getD 284 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a284_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v284 : Nat := CFSG.KD.Fi24Cp.KV2 50
theorem CFSG.KD.Fi24Cp.Pc.r284 : Nat.beq (powR AR.mul AR.one (getV AR SD 276 CFSG.KD.Fi24Cp.Pc.l284 (SD.na.getD 284 0)) (SD.nk.getD 284 1) 1 CFSG.KD.Fi24Cp.Pc.a284_1 true) CFSG.KD.Fi24Cp.Pc.v284 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v285 : Nat := CFSG.KD.Fi24Cp.KV2 51
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l285 : List Nat := [CFSG.KD.Fi24Cp.Pc.v276, CFSG.KD.Fi24Cp.Pc.v277, CFSG.KD.Fi24Cp.Pc.v278, CFSG.KD.Fi24Cp.Pc.v279, CFSG.KD.Fi24Cp.Pc.v280, CFSG.KD.Fi24Cp.Pc.v281, CFSG.KD.Fi24Cp.Pc.v282, CFSG.KD.Fi24Cp.Pc.v283, CFSG.KD.Fi24Cp.Pc.v284]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l286 : List Nat := [CFSG.KD.Fi24Cp.Pc.v276, CFSG.KD.Fi24Cp.Pc.v277, CFSG.KD.Fi24Cp.Pc.v278, CFSG.KD.Fi24Cp.Pc.v279, CFSG.KD.Fi24Cp.Pc.v280, CFSG.KD.Fi24Cp.Pc.v281, CFSG.KD.Fi24Cp.Pc.v282, CFSG.KD.Fi24Cp.Pc.v283, CFSG.KD.Fi24Cp.Pc.v284, CFSG.KD.Fi24Cp.Pc.v285]
theorem CFSG.KD.Fi24Cp.Pc.p285 : Nat.beq (runC AR SD 276 (ckL CFSG.KD.Fi24Cp.Pc.l286) 1 285 CFSG.KD.Fi24Cp.Pc.l285) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v286 : Nat := CFSG.KD.Fi24Cp.KV2 52
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l287 : List Nat := [CFSG.KD.Fi24Cp.Pc.v276, CFSG.KD.Fi24Cp.Pc.v277, CFSG.KD.Fi24Cp.Pc.v278, CFSG.KD.Fi24Cp.Pc.v279, CFSG.KD.Fi24Cp.Pc.v280, CFSG.KD.Fi24Cp.Pc.v281, CFSG.KD.Fi24Cp.Pc.v282, CFSG.KD.Fi24Cp.Pc.v283, CFSG.KD.Fi24Cp.Pc.v284, CFSG.KD.Fi24Cp.Pc.v285, CFSG.KD.Fi24Cp.Pc.v286]
theorem CFSG.KD.Fi24Cp.Pc.p286 : Nat.beq (runC AR SD 276 (ckL CFSG.KD.Fi24Cp.Pc.l287) 1 286 CFSG.KD.Fi24Cp.Pc.l286) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v287 : Nat := CFSG.KD.Fi24Cp.KV2 53
theorem CFSG.KD.Fi24Cp.Pc.f23 : Nat.beq (runC AR SD 276 (finC AR SD (nat_lit 23) 276 288) 1 287 CFSG.KD.Fi24Cp.Pc.l287) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk23 : chk (nat_lit 23) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 23) (lo := 276) (hi := 288) (m := 12) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 12) (m2 := 10) (j2 := 278) CFSG.KD.Fi24Cp.Pc.p276 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 280) CFSG.KD.Fi24Cp.Pc.p278 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 282) CFSG.KD.Fi24Cp.Pc.p280 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 284) CFSG.KD.Fi24Cp.Pc.p282 rfl rfl).trans ((runC_node (m := 4) (m2 := 3) (j2 := 285) (Lr := CFSG.KD.Fi24Cp.Pc.l285) ((nodeV_pow (R := AR) (D := SD) (lo := 276) (L := CFSG.KD.Fi24Cp.Pc.l284) (j := 284) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 276 CFSG.KD.Fi24Cp.Pc.l284 (SD.na.getD 284 0)) (SD.nk.getD 284 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q284_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r284)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 3) (m2 := 2) (j2 := 286) CFSG.KD.Fi24Cp.Pc.p285 rfl rfl).trans (runC_seq (m := 2) (m2 := 1) (j2 := 287) CFSG.KD.Fi24Cp.Pc.p286 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f23

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v288 : Nat := CFSG.KD.Fi24Cp.KV2 54
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v289 : Nat := CFSG.KD.Fi24Cp.KV2 55
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l290 : List Nat := [CFSG.KD.Fi24Cp.Pc.v288, CFSG.KD.Fi24Cp.Pc.v289]
theorem CFSG.KD.Fi24Cp.Pc.p288 : Nat.beq (runC AR SD 288 (ckL CFSG.KD.Fi24Cp.Pc.l290) 2 288 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v290 : Nat := CFSG.KD.Fi24Cp.KV2 56
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v291 : Nat := CFSG.KD.Fi24Cp.KV2 57
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l292 : List Nat := [CFSG.KD.Fi24Cp.Pc.v288, CFSG.KD.Fi24Cp.Pc.v289, CFSG.KD.Fi24Cp.Pc.v290, CFSG.KD.Fi24Cp.Pc.v291]
theorem CFSG.KD.Fi24Cp.Pc.p290 : Nat.beq (runC AR SD 288 (ckL CFSG.KD.Fi24Cp.Pc.l292) 2 290 CFSG.KD.Fi24Cp.Pc.l290) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v292 : Nat := CFSG.KD.Fi24Cp.KV2 58
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v293 : Nat := CFSG.KD.Fi24Cp.KV2 59
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l294 : List Nat := [CFSG.KD.Fi24Cp.Pc.v288, CFSG.KD.Fi24Cp.Pc.v289, CFSG.KD.Fi24Cp.Pc.v290, CFSG.KD.Fi24Cp.Pc.v291, CFSG.KD.Fi24Cp.Pc.v292, CFSG.KD.Fi24Cp.Pc.v293]
theorem CFSG.KD.Fi24Cp.Pc.p292 : Nat.beq (runC AR SD 288 (ckL CFSG.KD.Fi24Cp.Pc.l294) 2 292 CFSG.KD.Fi24Cp.Pc.l292) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v294 : Nat := CFSG.KD.Fi24Cp.KV2 60
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v295 : Nat := CFSG.KD.Fi24Cp.KV2 61
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l296 : List Nat := [CFSG.KD.Fi24Cp.Pc.v288, CFSG.KD.Fi24Cp.Pc.v289, CFSG.KD.Fi24Cp.Pc.v290, CFSG.KD.Fi24Cp.Pc.v291, CFSG.KD.Fi24Cp.Pc.v292, CFSG.KD.Fi24Cp.Pc.v293, CFSG.KD.Fi24Cp.Pc.v294, CFSG.KD.Fi24Cp.Pc.v295]
theorem CFSG.KD.Fi24Cp.Pc.p294 : Nat.beq (runC AR SD 288 (ckL CFSG.KD.Fi24Cp.Pc.l296) 2 294 CFSG.KD.Fi24Cp.Pc.l294) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v296 : Nat := CFSG.KD.Fi24Cp.KV2 62
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v297 : Nat := CFSG.KD.Fi24Cp.KV2 63
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l298 : List Nat := [CFSG.KD.Fi24Cp.Pc.v288, CFSG.KD.Fi24Cp.Pc.v289, CFSG.KD.Fi24Cp.Pc.v290, CFSG.KD.Fi24Cp.Pc.v291, CFSG.KD.Fi24Cp.Pc.v292, CFSG.KD.Fi24Cp.Pc.v293, CFSG.KD.Fi24Cp.Pc.v294, CFSG.KD.Fi24Cp.Pc.v295, CFSG.KD.Fi24Cp.Pc.v296, CFSG.KD.Fi24Cp.Pc.v297]
theorem CFSG.KD.Fi24Cp.Pc.p296 : Nat.beq (runC AR SD 288 (ckL CFSG.KD.Fi24Cp.Pc.l298) 2 296 CFSG.KD.Fi24Cp.Pc.l296) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v298 : Nat := CFSG.KD.Fi24Cp.KV2 64
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v299 : Nat := CFSG.KD.Fi24Cp.KV2 65
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l300 : List Nat := [CFSG.KD.Fi24Cp.Pc.v288, CFSG.KD.Fi24Cp.Pc.v289, CFSG.KD.Fi24Cp.Pc.v290, CFSG.KD.Fi24Cp.Pc.v291, CFSG.KD.Fi24Cp.Pc.v292, CFSG.KD.Fi24Cp.Pc.v293, CFSG.KD.Fi24Cp.Pc.v294, CFSG.KD.Fi24Cp.Pc.v295, CFSG.KD.Fi24Cp.Pc.v296, CFSG.KD.Fi24Cp.Pc.v297, CFSG.KD.Fi24Cp.Pc.v298, CFSG.KD.Fi24Cp.Pc.v299]
theorem CFSG.KD.Fi24Cp.Pc.p298 : Nat.beq (runC AR SD 288 (ckL CFSG.KD.Fi24Cp.Pc.l300) 2 298 CFSG.KD.Fi24Cp.Pc.l298) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v300 : Nat := CFSG.KD.Fi24Cp.KV2 66
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v301 : Nat := CFSG.KD.Fi24Cp.KV2 67
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l302 : List Nat := [CFSG.KD.Fi24Cp.Pc.v288, CFSG.KD.Fi24Cp.Pc.v289, CFSG.KD.Fi24Cp.Pc.v290, CFSG.KD.Fi24Cp.Pc.v291, CFSG.KD.Fi24Cp.Pc.v292, CFSG.KD.Fi24Cp.Pc.v293, CFSG.KD.Fi24Cp.Pc.v294, CFSG.KD.Fi24Cp.Pc.v295, CFSG.KD.Fi24Cp.Pc.v296, CFSG.KD.Fi24Cp.Pc.v297, CFSG.KD.Fi24Cp.Pc.v298, CFSG.KD.Fi24Cp.Pc.v299, CFSG.KD.Fi24Cp.Pc.v300, CFSG.KD.Fi24Cp.Pc.v301]
theorem CFSG.KD.Fi24Cp.Pc.p300 : Nat.beq (runC AR SD 288 (ckL CFSG.KD.Fi24Cp.Pc.l302) 2 300 CFSG.KD.Fi24Cp.Pc.l300) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v302 : Nat := CFSG.KD.Fi24Cp.KV2 68
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v303 : Nat := CFSG.KD.Fi24Cp.KV2 69
theorem CFSG.KD.Fi24Cp.Pc.f24 : Nat.beq (runC AR SD 288 (finC AR SD (nat_lit 24) 288 304) 2 302 CFSG.KD.Fi24Cp.Pc.l302) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk24 : chk (nat_lit 24) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 24) (lo := 288) (hi := 304) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 290) CFSG.KD.Fi24Cp.Pc.p288 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 292) CFSG.KD.Fi24Cp.Pc.p290 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 294) CFSG.KD.Fi24Cp.Pc.p292 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 296) CFSG.KD.Fi24Cp.Pc.p294 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 298) CFSG.KD.Fi24Cp.Pc.p296 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 300) CFSG.KD.Fi24Cp.Pc.p298 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 302) CFSG.KD.Fi24Cp.Pc.p300 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f24

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v304 : Nat := CFSG.KD.Fi24Cp.KV2 70
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v305 : Nat := CFSG.KD.Fi24Cp.KV2 71
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l306 : List Nat := [CFSG.KD.Fi24Cp.Pc.v304, CFSG.KD.Fi24Cp.Pc.v305]
theorem CFSG.KD.Fi24Cp.Pc.p304 : Nat.beq (runC AR SD 304 (ckL CFSG.KD.Fi24Cp.Pc.l306) 2 304 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v306 : Nat := CFSG.KD.Fi24Cp.KV2 72
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v307 : Nat := CFSG.KD.Fi24Cp.KV2 73
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l308 : List Nat := [CFSG.KD.Fi24Cp.Pc.v304, CFSG.KD.Fi24Cp.Pc.v305, CFSG.KD.Fi24Cp.Pc.v306, CFSG.KD.Fi24Cp.Pc.v307]
theorem CFSG.KD.Fi24Cp.Pc.p306 : Nat.beq (runC AR SD 304 (ckL CFSG.KD.Fi24Cp.Pc.l308) 2 306 CFSG.KD.Fi24Cp.Pc.l306) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v308 : Nat := CFSG.KD.Fi24Cp.KV2 74
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v309 : Nat := CFSG.KD.Fi24Cp.KV2 75
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l310 : List Nat := [CFSG.KD.Fi24Cp.Pc.v304, CFSG.KD.Fi24Cp.Pc.v305, CFSG.KD.Fi24Cp.Pc.v306, CFSG.KD.Fi24Cp.Pc.v307, CFSG.KD.Fi24Cp.Pc.v308, CFSG.KD.Fi24Cp.Pc.v309]
theorem CFSG.KD.Fi24Cp.Pc.p308 : Nat.beq (runC AR SD 304 (ckL CFSG.KD.Fi24Cp.Pc.l310) 2 308 CFSG.KD.Fi24Cp.Pc.l308) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v310 : Nat := CFSG.KD.Fi24Cp.KV2 76
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v311 : Nat := CFSG.KD.Fi24Cp.KV2 77
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l312 : List Nat := [CFSG.KD.Fi24Cp.Pc.v304, CFSG.KD.Fi24Cp.Pc.v305, CFSG.KD.Fi24Cp.Pc.v306, CFSG.KD.Fi24Cp.Pc.v307, CFSG.KD.Fi24Cp.Pc.v308, CFSG.KD.Fi24Cp.Pc.v309, CFSG.KD.Fi24Cp.Pc.v310, CFSG.KD.Fi24Cp.Pc.v311]
theorem CFSG.KD.Fi24Cp.Pc.p310 : Nat.beq (runC AR SD 304 (ckL CFSG.KD.Fi24Cp.Pc.l312) 2 310 CFSG.KD.Fi24Cp.Pc.l310) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v312 : Nat := CFSG.KD.Fi24Cp.KV2 78
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v313 : Nat := CFSG.KD.Fi24Cp.KV2 79
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l314 : List Nat := [CFSG.KD.Fi24Cp.Pc.v304, CFSG.KD.Fi24Cp.Pc.v305, CFSG.KD.Fi24Cp.Pc.v306, CFSG.KD.Fi24Cp.Pc.v307, CFSG.KD.Fi24Cp.Pc.v308, CFSG.KD.Fi24Cp.Pc.v309, CFSG.KD.Fi24Cp.Pc.v310, CFSG.KD.Fi24Cp.Pc.v311, CFSG.KD.Fi24Cp.Pc.v312, CFSG.KD.Fi24Cp.Pc.v313]
theorem CFSG.KD.Fi24Cp.Pc.p312 : Nat.beq (runC AR SD 304 (ckL CFSG.KD.Fi24Cp.Pc.l314) 2 312 CFSG.KD.Fi24Cp.Pc.l312) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v314 : Nat := CFSG.KD.Fi24Cp.KV2 80
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v315 : Nat := CFSG.KD.Fi24Cp.KV2 81
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l316 : List Nat := [CFSG.KD.Fi24Cp.Pc.v304, CFSG.KD.Fi24Cp.Pc.v305, CFSG.KD.Fi24Cp.Pc.v306, CFSG.KD.Fi24Cp.Pc.v307, CFSG.KD.Fi24Cp.Pc.v308, CFSG.KD.Fi24Cp.Pc.v309, CFSG.KD.Fi24Cp.Pc.v310, CFSG.KD.Fi24Cp.Pc.v311, CFSG.KD.Fi24Cp.Pc.v312, CFSG.KD.Fi24Cp.Pc.v313, CFSG.KD.Fi24Cp.Pc.v314, CFSG.KD.Fi24Cp.Pc.v315]
theorem CFSG.KD.Fi24Cp.Pc.p314 : Nat.beq (runC AR SD 304 (ckL CFSG.KD.Fi24Cp.Pc.l316) 2 314 CFSG.KD.Fi24Cp.Pc.l314) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v316 : Nat := CFSG.KD.Fi24Cp.KV2 82
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v317 : Nat := CFSG.KD.Fi24Cp.KV2 83
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l318 : List Nat := [CFSG.KD.Fi24Cp.Pc.v304, CFSG.KD.Fi24Cp.Pc.v305, CFSG.KD.Fi24Cp.Pc.v306, CFSG.KD.Fi24Cp.Pc.v307, CFSG.KD.Fi24Cp.Pc.v308, CFSG.KD.Fi24Cp.Pc.v309, CFSG.KD.Fi24Cp.Pc.v310, CFSG.KD.Fi24Cp.Pc.v311, CFSG.KD.Fi24Cp.Pc.v312, CFSG.KD.Fi24Cp.Pc.v313, CFSG.KD.Fi24Cp.Pc.v314, CFSG.KD.Fi24Cp.Pc.v315, CFSG.KD.Fi24Cp.Pc.v316, CFSG.KD.Fi24Cp.Pc.v317]
theorem CFSG.KD.Fi24Cp.Pc.p316 : Nat.beq (runC AR SD 304 (ckL CFSG.KD.Fi24Cp.Pc.l318) 2 316 CFSG.KD.Fi24Cp.Pc.l316) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v318 : Nat := CFSG.KD.Fi24Cp.KV2 84
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v319 : Nat := CFSG.KD.Fi24Cp.KV2 85
theorem CFSG.KD.Fi24Cp.Pc.f25 : Nat.beq (runC AR SD 304 (finC AR SD (nat_lit 25) 304 320) 2 318 CFSG.KD.Fi24Cp.Pc.l318) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk25 : chk (nat_lit 25) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 25) (lo := 304) (hi := 320) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 306) CFSG.KD.Fi24Cp.Pc.p304 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 308) CFSG.KD.Fi24Cp.Pc.p306 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 310) CFSG.KD.Fi24Cp.Pc.p308 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 312) CFSG.KD.Fi24Cp.Pc.p310 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 314) CFSG.KD.Fi24Cp.Pc.p312 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 316) CFSG.KD.Fi24Cp.Pc.p314 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 318) CFSG.KD.Fi24Cp.Pc.p316 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f25

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v320 : Nat := CFSG.KD.Fi24Cp.KV2 86
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v321 : Nat := CFSG.KD.Fi24Cp.KV2 87
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l322 : List Nat := [CFSG.KD.Fi24Cp.Pc.v320, CFSG.KD.Fi24Cp.Pc.v321]
theorem CFSG.KD.Fi24Cp.Pc.p320 : Nat.beq (runC AR SD 320 (ckL CFSG.KD.Fi24Cp.Pc.l322) 2 320 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v322 : Nat := CFSG.KD.Fi24Cp.KV2 88
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v323 : Nat := CFSG.KD.Fi24Cp.KV2 89
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l324 : List Nat := [CFSG.KD.Fi24Cp.Pc.v320, CFSG.KD.Fi24Cp.Pc.v321, CFSG.KD.Fi24Cp.Pc.v322, CFSG.KD.Fi24Cp.Pc.v323]
theorem CFSG.KD.Fi24Cp.Pc.p322 : Nat.beq (runC AR SD 320 (ckL CFSG.KD.Fi24Cp.Pc.l324) 2 322 CFSG.KD.Fi24Cp.Pc.l322) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v324 : Nat := CFSG.KD.Fi24Cp.KV2 90
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l325 : List Nat := [CFSG.KD.Fi24Cp.Pc.v320, CFSG.KD.Fi24Cp.Pc.v321, CFSG.KD.Fi24Cp.Pc.v322, CFSG.KD.Fi24Cp.Pc.v323, CFSG.KD.Fi24Cp.Pc.v324]
theorem CFSG.KD.Fi24Cp.Pc.p324 : Nat.beq (runC AR SD 320 (ckL CFSG.KD.Fi24Cp.Pc.l325) 1 324 CFSG.KD.Fi24Cp.Pc.l324) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v325 : Nat := CFSG.KD.Fi24Cp.KV2 91
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l326 : List Nat := [CFSG.KD.Fi24Cp.Pc.v320, CFSG.KD.Fi24Cp.Pc.v321, CFSG.KD.Fi24Cp.Pc.v322, CFSG.KD.Fi24Cp.Pc.v323, CFSG.KD.Fi24Cp.Pc.v324, CFSG.KD.Fi24Cp.Pc.v325]
theorem CFSG.KD.Fi24Cp.Pc.p325 : Nat.beq (runC AR SD 320 (ckL CFSG.KD.Fi24Cp.Pc.l326) 1 325 CFSG.KD.Fi24Cp.Pc.l325) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v326 : Nat := CFSG.KD.Fi24Cp.KV2 92
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v327 : Nat := CFSG.KD.Fi24Cp.KV2 93
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l328 : List Nat := [CFSG.KD.Fi24Cp.Pc.v320, CFSG.KD.Fi24Cp.Pc.v321, CFSG.KD.Fi24Cp.Pc.v322, CFSG.KD.Fi24Cp.Pc.v323, CFSG.KD.Fi24Cp.Pc.v324, CFSG.KD.Fi24Cp.Pc.v325, CFSG.KD.Fi24Cp.Pc.v326, CFSG.KD.Fi24Cp.Pc.v327]
theorem CFSG.KD.Fi24Cp.Pc.p326 : Nat.beq (runC AR SD 320 (ckL CFSG.KD.Fi24Cp.Pc.l328) 2 326 CFSG.KD.Fi24Cp.Pc.l326) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v328 : Nat := CFSG.KD.Fi24Cp.KV2 94
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v329 : Nat := CFSG.KD.Fi24Cp.KV2 95
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l330 : List Nat := [CFSG.KD.Fi24Cp.Pc.v320, CFSG.KD.Fi24Cp.Pc.v321, CFSG.KD.Fi24Cp.Pc.v322, CFSG.KD.Fi24Cp.Pc.v323, CFSG.KD.Fi24Cp.Pc.v324, CFSG.KD.Fi24Cp.Pc.v325, CFSG.KD.Fi24Cp.Pc.v326, CFSG.KD.Fi24Cp.Pc.v327, CFSG.KD.Fi24Cp.Pc.v328, CFSG.KD.Fi24Cp.Pc.v329]
theorem CFSG.KD.Fi24Cp.Pc.p328 : Nat.beq (runC AR SD 320 (ckL CFSG.KD.Fi24Cp.Pc.l330) 2 328 CFSG.KD.Fi24Cp.Pc.l328) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v330 : Nat := CFSG.KD.Fi24Cp.KV2 96
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v331 : Nat := CFSG.KD.Fi24Cp.KV2 97
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l332 : List Nat := [CFSG.KD.Fi24Cp.Pc.v320, CFSG.KD.Fi24Cp.Pc.v321, CFSG.KD.Fi24Cp.Pc.v322, CFSG.KD.Fi24Cp.Pc.v323, CFSG.KD.Fi24Cp.Pc.v324, CFSG.KD.Fi24Cp.Pc.v325, CFSG.KD.Fi24Cp.Pc.v326, CFSG.KD.Fi24Cp.Pc.v327, CFSG.KD.Fi24Cp.Pc.v328, CFSG.KD.Fi24Cp.Pc.v329, CFSG.KD.Fi24Cp.Pc.v330, CFSG.KD.Fi24Cp.Pc.v331]
theorem CFSG.KD.Fi24Cp.Pc.p330 : Nat.beq (runC AR SD 320 (ckL CFSG.KD.Fi24Cp.Pc.l332) 2 330 CFSG.KD.Fi24Cp.Pc.l330) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v332 : Nat := CFSG.KD.Fi24Cp.KV2 98
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v333 : Nat := CFSG.KD.Fi24Cp.KV2 99
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l334 : List Nat := [CFSG.KD.Fi24Cp.Pc.v320, CFSG.KD.Fi24Cp.Pc.v321, CFSG.KD.Fi24Cp.Pc.v322, CFSG.KD.Fi24Cp.Pc.v323, CFSG.KD.Fi24Cp.Pc.v324, CFSG.KD.Fi24Cp.Pc.v325, CFSG.KD.Fi24Cp.Pc.v326, CFSG.KD.Fi24Cp.Pc.v327, CFSG.KD.Fi24Cp.Pc.v328, CFSG.KD.Fi24Cp.Pc.v329, CFSG.KD.Fi24Cp.Pc.v330, CFSG.KD.Fi24Cp.Pc.v331, CFSG.KD.Fi24Cp.Pc.v332, CFSG.KD.Fi24Cp.Pc.v333]
theorem CFSG.KD.Fi24Cp.Pc.p332 : Nat.beq (runC AR SD 320 (ckL CFSG.KD.Fi24Cp.Pc.l334) 2 332 CFSG.KD.Fi24Cp.Pc.l332) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v334 : Nat := CFSG.KD.Fi24Cp.KV2 100
theorem CFSG.KD.Fi24Cp.Pc.f26 : Nat.beq (runC AR SD 320 (finC AR SD (nat_lit 26) 320 335) 1 334 CFSG.KD.Fi24Cp.Pc.l334) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk26 : chk (nat_lit 26) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 26) (lo := 320) (hi := 335) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 322) CFSG.KD.Fi24Cp.Pc.p320 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 324) CFSG.KD.Fi24Cp.Pc.p322 rfl rfl).trans ((runC_seq (m := 11) (m2 := 10) (j2 := 325) CFSG.KD.Fi24Cp.Pc.p324 rfl rfl).trans ((runC_seq (m := 10) (m2 := 9) (j2 := 326) CFSG.KD.Fi24Cp.Pc.p325 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 328) CFSG.KD.Fi24Cp.Pc.p326 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 330) CFSG.KD.Fi24Cp.Pc.p328 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 332) CFSG.KD.Fi24Cp.Pc.p330 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 334) CFSG.KD.Fi24Cp.Pc.p332 rfl rfl)))))))))).trans CFSG.KD.Fi24Cp.Pc.f26

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v335 : Nat := CFSG.KD.Fi24Cp.KV2 101
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v336 : Nat := CFSG.KD.Fi24Cp.KV2 102
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l337 : List Nat := [CFSG.KD.Fi24Cp.Pc.v335, CFSG.KD.Fi24Cp.Pc.v336]
theorem CFSG.KD.Fi24Cp.Pc.p335 : Nat.beq (runC AR SD 335 (ckL CFSG.KD.Fi24Cp.Pc.l337) 2 335 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v337 : Nat := CFSG.KD.Fi24Cp.KV2 103
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v338 : Nat := CFSG.KD.Fi24Cp.KV2 104
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l339 : List Nat := [CFSG.KD.Fi24Cp.Pc.v335, CFSG.KD.Fi24Cp.Pc.v336, CFSG.KD.Fi24Cp.Pc.v337, CFSG.KD.Fi24Cp.Pc.v338]
theorem CFSG.KD.Fi24Cp.Pc.p337 : Nat.beq (runC AR SD 335 (ckL CFSG.KD.Fi24Cp.Pc.l339) 2 337 CFSG.KD.Fi24Cp.Pc.l337) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v339 : Nat := CFSG.KD.Fi24Cp.KV2 105
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v340 : Nat := CFSG.KD.Fi24Cp.KV2 106
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l341 : List Nat := [CFSG.KD.Fi24Cp.Pc.v335, CFSG.KD.Fi24Cp.Pc.v336, CFSG.KD.Fi24Cp.Pc.v337, CFSG.KD.Fi24Cp.Pc.v338, CFSG.KD.Fi24Cp.Pc.v339, CFSG.KD.Fi24Cp.Pc.v340]
theorem CFSG.KD.Fi24Cp.Pc.p339 : Nat.beq (runC AR SD 335 (ckL CFSG.KD.Fi24Cp.Pc.l341) 2 339 CFSG.KD.Fi24Cp.Pc.l339) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v341 : Nat := CFSG.KD.Fi24Cp.KV2 107
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v342 : Nat := CFSG.KD.Fi24Cp.KV2 108
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l343 : List Nat := [CFSG.KD.Fi24Cp.Pc.v335, CFSG.KD.Fi24Cp.Pc.v336, CFSG.KD.Fi24Cp.Pc.v337, CFSG.KD.Fi24Cp.Pc.v338, CFSG.KD.Fi24Cp.Pc.v339, CFSG.KD.Fi24Cp.Pc.v340, CFSG.KD.Fi24Cp.Pc.v341, CFSG.KD.Fi24Cp.Pc.v342]
theorem CFSG.KD.Fi24Cp.Pc.p341 : Nat.beq (runC AR SD 335 (ckL CFSG.KD.Fi24Cp.Pc.l343) 2 341 CFSG.KD.Fi24Cp.Pc.l341) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v343 : Nat := CFSG.KD.Fi24Cp.KV2 109
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v344 : Nat := CFSG.KD.Fi24Cp.KV2 110
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l345 : List Nat := [CFSG.KD.Fi24Cp.Pc.v335, CFSG.KD.Fi24Cp.Pc.v336, CFSG.KD.Fi24Cp.Pc.v337, CFSG.KD.Fi24Cp.Pc.v338, CFSG.KD.Fi24Cp.Pc.v339, CFSG.KD.Fi24Cp.Pc.v340, CFSG.KD.Fi24Cp.Pc.v341, CFSG.KD.Fi24Cp.Pc.v342, CFSG.KD.Fi24Cp.Pc.v343, CFSG.KD.Fi24Cp.Pc.v344]
theorem CFSG.KD.Fi24Cp.Pc.p343 : Nat.beq (runC AR SD 335 (ckL CFSG.KD.Fi24Cp.Pc.l345) 2 343 CFSG.KD.Fi24Cp.Pc.l343) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v345 : Nat := CFSG.KD.Fi24Cp.KV2 111
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v346 : Nat := CFSG.KD.Fi24Cp.KV2 112
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l347 : List Nat := [CFSG.KD.Fi24Cp.Pc.v335, CFSG.KD.Fi24Cp.Pc.v336, CFSG.KD.Fi24Cp.Pc.v337, CFSG.KD.Fi24Cp.Pc.v338, CFSG.KD.Fi24Cp.Pc.v339, CFSG.KD.Fi24Cp.Pc.v340, CFSG.KD.Fi24Cp.Pc.v341, CFSG.KD.Fi24Cp.Pc.v342, CFSG.KD.Fi24Cp.Pc.v343, CFSG.KD.Fi24Cp.Pc.v344, CFSG.KD.Fi24Cp.Pc.v345, CFSG.KD.Fi24Cp.Pc.v346]
theorem CFSG.KD.Fi24Cp.Pc.p345 : Nat.beq (runC AR SD 335 (ckL CFSG.KD.Fi24Cp.Pc.l347) 2 345 CFSG.KD.Fi24Cp.Pc.l345) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v347 : Nat := CFSG.KD.Fi24Cp.KV2 113
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v348 : Nat := CFSG.KD.Fi24Cp.KV2 114
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l349 : List Nat := [CFSG.KD.Fi24Cp.Pc.v335, CFSG.KD.Fi24Cp.Pc.v336, CFSG.KD.Fi24Cp.Pc.v337, CFSG.KD.Fi24Cp.Pc.v338, CFSG.KD.Fi24Cp.Pc.v339, CFSG.KD.Fi24Cp.Pc.v340, CFSG.KD.Fi24Cp.Pc.v341, CFSG.KD.Fi24Cp.Pc.v342, CFSG.KD.Fi24Cp.Pc.v343, CFSG.KD.Fi24Cp.Pc.v344, CFSG.KD.Fi24Cp.Pc.v345, CFSG.KD.Fi24Cp.Pc.v346, CFSG.KD.Fi24Cp.Pc.v347, CFSG.KD.Fi24Cp.Pc.v348]
theorem CFSG.KD.Fi24Cp.Pc.p347 : Nat.beq (runC AR SD 335 (ckL CFSG.KD.Fi24Cp.Pc.l349) 2 347 CFSG.KD.Fi24Cp.Pc.l347) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v349 : Nat := CFSG.KD.Fi24Cp.KV2 115
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v350 : Nat := CFSG.KD.Fi24Cp.KV2 116
theorem CFSG.KD.Fi24Cp.Pc.f27 : Nat.beq (runC AR SD 335 (finC AR SD (nat_lit 27) 335 351) 2 349 CFSG.KD.Fi24Cp.Pc.l349) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk27 : chk (nat_lit 27) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 27) (lo := 335) (hi := 351) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 337) CFSG.KD.Fi24Cp.Pc.p335 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 339) CFSG.KD.Fi24Cp.Pc.p337 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 341) CFSG.KD.Fi24Cp.Pc.p339 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 343) CFSG.KD.Fi24Cp.Pc.p341 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 345) CFSG.KD.Fi24Cp.Pc.p343 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 347) CFSG.KD.Fi24Cp.Pc.p345 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 349) CFSG.KD.Fi24Cp.Pc.p347 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f27

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v351 : Nat := CFSG.KD.Fi24Cp.KV2 117
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v352 : Nat := CFSG.KD.Fi24Cp.KV2 118
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l353 : List Nat := [CFSG.KD.Fi24Cp.Pc.v351, CFSG.KD.Fi24Cp.Pc.v352]
theorem CFSG.KD.Fi24Cp.Pc.p351 : Nat.beq (runC AR SD 351 (ckL CFSG.KD.Fi24Cp.Pc.l353) 2 351 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v353 : Nat := CFSG.KD.Fi24Cp.KV2 119
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v354 : Nat := CFSG.KD.Fi24Cp.KV2 120
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l355 : List Nat := [CFSG.KD.Fi24Cp.Pc.v351, CFSG.KD.Fi24Cp.Pc.v352, CFSG.KD.Fi24Cp.Pc.v353, CFSG.KD.Fi24Cp.Pc.v354]
theorem CFSG.KD.Fi24Cp.Pc.p353 : Nat.beq (runC AR SD 351 (ckL CFSG.KD.Fi24Cp.Pc.l355) 2 353 CFSG.KD.Fi24Cp.Pc.l353) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v355 : Nat := CFSG.KD.Fi24Cp.KV2 121
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v356 : Nat := CFSG.KD.Fi24Cp.KV2 122
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l357 : List Nat := [CFSG.KD.Fi24Cp.Pc.v351, CFSG.KD.Fi24Cp.Pc.v352, CFSG.KD.Fi24Cp.Pc.v353, CFSG.KD.Fi24Cp.Pc.v354, CFSG.KD.Fi24Cp.Pc.v355, CFSG.KD.Fi24Cp.Pc.v356]
theorem CFSG.KD.Fi24Cp.Pc.p355 : Nat.beq (runC AR SD 351 (ckL CFSG.KD.Fi24Cp.Pc.l357) 2 355 CFSG.KD.Fi24Cp.Pc.l355) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v357 : Nat := CFSG.KD.Fi24Cp.KV2 123
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v358 : Nat := CFSG.KD.Fi24Cp.KV2 124
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l359 : List Nat := [CFSG.KD.Fi24Cp.Pc.v351, CFSG.KD.Fi24Cp.Pc.v352, CFSG.KD.Fi24Cp.Pc.v353, CFSG.KD.Fi24Cp.Pc.v354, CFSG.KD.Fi24Cp.Pc.v355, CFSG.KD.Fi24Cp.Pc.v356, CFSG.KD.Fi24Cp.Pc.v357, CFSG.KD.Fi24Cp.Pc.v358]
theorem CFSG.KD.Fi24Cp.Pc.p357 : Nat.beq (runC AR SD 351 (ckL CFSG.KD.Fi24Cp.Pc.l359) 2 357 CFSG.KD.Fi24Cp.Pc.l357) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v359 : Nat := CFSG.KD.Fi24Cp.KV2 125
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v360 : Nat := CFSG.KD.Fi24Cp.KV2 126
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l361 : List Nat := [CFSG.KD.Fi24Cp.Pc.v351, CFSG.KD.Fi24Cp.Pc.v352, CFSG.KD.Fi24Cp.Pc.v353, CFSG.KD.Fi24Cp.Pc.v354, CFSG.KD.Fi24Cp.Pc.v355, CFSG.KD.Fi24Cp.Pc.v356, CFSG.KD.Fi24Cp.Pc.v357, CFSG.KD.Fi24Cp.Pc.v358, CFSG.KD.Fi24Cp.Pc.v359, CFSG.KD.Fi24Cp.Pc.v360]
theorem CFSG.KD.Fi24Cp.Pc.p359 : Nat.beq (runC AR SD 351 (ckL CFSG.KD.Fi24Cp.Pc.l361) 2 359 CFSG.KD.Fi24Cp.Pc.l359) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v361 : Nat := CFSG.KD.Fi24Cp.KV2 127
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v362 : Nat := CFSG.KD.Fi24Cp.KV2 128
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l363 : List Nat := [CFSG.KD.Fi24Cp.Pc.v351, CFSG.KD.Fi24Cp.Pc.v352, CFSG.KD.Fi24Cp.Pc.v353, CFSG.KD.Fi24Cp.Pc.v354, CFSG.KD.Fi24Cp.Pc.v355, CFSG.KD.Fi24Cp.Pc.v356, CFSG.KD.Fi24Cp.Pc.v357, CFSG.KD.Fi24Cp.Pc.v358, CFSG.KD.Fi24Cp.Pc.v359, CFSG.KD.Fi24Cp.Pc.v360, CFSG.KD.Fi24Cp.Pc.v361, CFSG.KD.Fi24Cp.Pc.v362]
theorem CFSG.KD.Fi24Cp.Pc.p361 : Nat.beq (runC AR SD 351 (ckL CFSG.KD.Fi24Cp.Pc.l363) 2 361 CFSG.KD.Fi24Cp.Pc.l361) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v363 : Nat := CFSG.KD.Fi24Cp.KV2 129
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v364 : Nat := CFSG.KD.Fi24Cp.KV2 130
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l365 : List Nat := [CFSG.KD.Fi24Cp.Pc.v351, CFSG.KD.Fi24Cp.Pc.v352, CFSG.KD.Fi24Cp.Pc.v353, CFSG.KD.Fi24Cp.Pc.v354, CFSG.KD.Fi24Cp.Pc.v355, CFSG.KD.Fi24Cp.Pc.v356, CFSG.KD.Fi24Cp.Pc.v357, CFSG.KD.Fi24Cp.Pc.v358, CFSG.KD.Fi24Cp.Pc.v359, CFSG.KD.Fi24Cp.Pc.v360, CFSG.KD.Fi24Cp.Pc.v361, CFSG.KD.Fi24Cp.Pc.v362, CFSG.KD.Fi24Cp.Pc.v363, CFSG.KD.Fi24Cp.Pc.v364]
theorem CFSG.KD.Fi24Cp.Pc.p363 : Nat.beq (runC AR SD 351 (ckL CFSG.KD.Fi24Cp.Pc.l365) 2 363 CFSG.KD.Fi24Cp.Pc.l363) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v365 : Nat := CFSG.KD.Fi24Cp.KV2 131
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v366 : Nat := CFSG.KD.Fi24Cp.KV2 132
theorem CFSG.KD.Fi24Cp.Pc.f28 : Nat.beq (runC AR SD 351 (finC AR SD (nat_lit 28) 351 367) 2 365 CFSG.KD.Fi24Cp.Pc.l365) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk28 : chk (nat_lit 28) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 28) (lo := 351) (hi := 367) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 353) CFSG.KD.Fi24Cp.Pc.p351 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 355) CFSG.KD.Fi24Cp.Pc.p353 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 357) CFSG.KD.Fi24Cp.Pc.p355 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 359) CFSG.KD.Fi24Cp.Pc.p357 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 361) CFSG.KD.Fi24Cp.Pc.p359 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 363) CFSG.KD.Fi24Cp.Pc.p361 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 365) CFSG.KD.Fi24Cp.Pc.p363 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f28

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v367 : Nat := CFSG.KD.Fi24Cp.KV2 133
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v368 : Nat := CFSG.KD.Fi24Cp.KV2 134
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l369 : List Nat := [CFSG.KD.Fi24Cp.Pc.v367, CFSG.KD.Fi24Cp.Pc.v368]
theorem CFSG.KD.Fi24Cp.Pc.p367 : Nat.beq (runC AR SD 367 (ckL CFSG.KD.Fi24Cp.Pc.l369) 2 367 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v369 : Nat := CFSG.KD.Fi24Cp.KV2 135
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v370 : Nat := CFSG.KD.Fi24Cp.KV2 136
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l371 : List Nat := [CFSG.KD.Fi24Cp.Pc.v367, CFSG.KD.Fi24Cp.Pc.v368, CFSG.KD.Fi24Cp.Pc.v369, CFSG.KD.Fi24Cp.Pc.v370]
theorem CFSG.KD.Fi24Cp.Pc.p369 : Nat.beq (runC AR SD 367 (ckL CFSG.KD.Fi24Cp.Pc.l371) 2 369 CFSG.KD.Fi24Cp.Pc.l369) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v371 : Nat := CFSG.KD.Fi24Cp.KV2 137
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v372 : Nat := CFSG.KD.Fi24Cp.KV2 138
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l373 : List Nat := [CFSG.KD.Fi24Cp.Pc.v367, CFSG.KD.Fi24Cp.Pc.v368, CFSG.KD.Fi24Cp.Pc.v369, CFSG.KD.Fi24Cp.Pc.v370, CFSG.KD.Fi24Cp.Pc.v371, CFSG.KD.Fi24Cp.Pc.v372]
theorem CFSG.KD.Fi24Cp.Pc.p371 : Nat.beq (runC AR SD 367 (ckL CFSG.KD.Fi24Cp.Pc.l373) 2 371 CFSG.KD.Fi24Cp.Pc.l371) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v373 : Nat := CFSG.KD.Fi24Cp.KV2 139
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v374 : Nat := CFSG.KD.Fi24Cp.KV2 140
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l375 : List Nat := [CFSG.KD.Fi24Cp.Pc.v367, CFSG.KD.Fi24Cp.Pc.v368, CFSG.KD.Fi24Cp.Pc.v369, CFSG.KD.Fi24Cp.Pc.v370, CFSG.KD.Fi24Cp.Pc.v371, CFSG.KD.Fi24Cp.Pc.v372, CFSG.KD.Fi24Cp.Pc.v373, CFSG.KD.Fi24Cp.Pc.v374]
theorem CFSG.KD.Fi24Cp.Pc.p373 : Nat.beq (runC AR SD 367 (ckL CFSG.KD.Fi24Cp.Pc.l375) 2 373 CFSG.KD.Fi24Cp.Pc.l373) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v375 : Nat := CFSG.KD.Fi24Cp.KV2 141
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v376 : Nat := CFSG.KD.Fi24Cp.KV2 142
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l377 : List Nat := [CFSG.KD.Fi24Cp.Pc.v367, CFSG.KD.Fi24Cp.Pc.v368, CFSG.KD.Fi24Cp.Pc.v369, CFSG.KD.Fi24Cp.Pc.v370, CFSG.KD.Fi24Cp.Pc.v371, CFSG.KD.Fi24Cp.Pc.v372, CFSG.KD.Fi24Cp.Pc.v373, CFSG.KD.Fi24Cp.Pc.v374, CFSG.KD.Fi24Cp.Pc.v375, CFSG.KD.Fi24Cp.Pc.v376]
theorem CFSG.KD.Fi24Cp.Pc.p375 : Nat.beq (runC AR SD 367 (ckL CFSG.KD.Fi24Cp.Pc.l377) 2 375 CFSG.KD.Fi24Cp.Pc.l375) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v377 : Nat := CFSG.KD.Fi24Cp.KV2 143
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v378 : Nat := CFSG.KD.Fi24Cp.KV2 144
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l379 : List Nat := [CFSG.KD.Fi24Cp.Pc.v367, CFSG.KD.Fi24Cp.Pc.v368, CFSG.KD.Fi24Cp.Pc.v369, CFSG.KD.Fi24Cp.Pc.v370, CFSG.KD.Fi24Cp.Pc.v371, CFSG.KD.Fi24Cp.Pc.v372, CFSG.KD.Fi24Cp.Pc.v373, CFSG.KD.Fi24Cp.Pc.v374, CFSG.KD.Fi24Cp.Pc.v375, CFSG.KD.Fi24Cp.Pc.v376, CFSG.KD.Fi24Cp.Pc.v377, CFSG.KD.Fi24Cp.Pc.v378]
theorem CFSG.KD.Fi24Cp.Pc.p377 : Nat.beq (runC AR SD 367 (ckL CFSG.KD.Fi24Cp.Pc.l379) 2 377 CFSG.KD.Fi24Cp.Pc.l377) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v379 : Nat := CFSG.KD.Fi24Cp.KV2 145
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v380 : Nat := CFSG.KD.Fi24Cp.KV2 146
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l381 : List Nat := [CFSG.KD.Fi24Cp.Pc.v367, CFSG.KD.Fi24Cp.Pc.v368, CFSG.KD.Fi24Cp.Pc.v369, CFSG.KD.Fi24Cp.Pc.v370, CFSG.KD.Fi24Cp.Pc.v371, CFSG.KD.Fi24Cp.Pc.v372, CFSG.KD.Fi24Cp.Pc.v373, CFSG.KD.Fi24Cp.Pc.v374, CFSG.KD.Fi24Cp.Pc.v375, CFSG.KD.Fi24Cp.Pc.v376, CFSG.KD.Fi24Cp.Pc.v377, CFSG.KD.Fi24Cp.Pc.v378, CFSG.KD.Fi24Cp.Pc.v379, CFSG.KD.Fi24Cp.Pc.v380]
theorem CFSG.KD.Fi24Cp.Pc.p379 : Nat.beq (runC AR SD 367 (ckL CFSG.KD.Fi24Cp.Pc.l381) 2 379 CFSG.KD.Fi24Cp.Pc.l379) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v381 : Nat := CFSG.KD.Fi24Cp.KV2 147
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v382 : Nat := CFSG.KD.Fi24Cp.KV2 148
theorem CFSG.KD.Fi24Cp.Pc.f29 : Nat.beq (runC AR SD 367 (finC AR SD (nat_lit 29) 367 383) 2 381 CFSG.KD.Fi24Cp.Pc.l381) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk29 : chk (nat_lit 29) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 29) (lo := 367) (hi := 383) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 369) CFSG.KD.Fi24Cp.Pc.p367 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 371) CFSG.KD.Fi24Cp.Pc.p369 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 373) CFSG.KD.Fi24Cp.Pc.p371 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 375) CFSG.KD.Fi24Cp.Pc.p373 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 377) CFSG.KD.Fi24Cp.Pc.p375 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 379) CFSG.KD.Fi24Cp.Pc.p377 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 381) CFSG.KD.Fi24Cp.Pc.p379 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f29

end
