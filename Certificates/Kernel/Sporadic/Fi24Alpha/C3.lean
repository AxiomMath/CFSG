module

public import Certificates.Kernel.Sporadic.Fi24Alpha.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Alpha KV3 "Certificates/Kernel/Sporadic/Fi24Alpha/data/v3.bin" 152491 4 24246069 13255713964358306770

public section

open CFSG.KD.Fi24Alpha CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v368 : Nat := CFSG.KD.Fi24Alpha.KV3 0
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v369 : Nat := CFSG.KD.Fi24Alpha.KV3 1
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l370 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v368, CFSG.KD.Fi24Alpha.Pc.v369]
theorem CFSG.KD.Fi24Alpha.Pc.p368 : Nat.beq (runC AR SD 368 (ckL CFSG.KD.Fi24Alpha.Pc.l370) 2 368 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v370 : Nat := CFSG.KD.Fi24Alpha.KV3 2
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v371 : Nat := CFSG.KD.Fi24Alpha.KV3 3
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l372 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v368, CFSG.KD.Fi24Alpha.Pc.v369, CFSG.KD.Fi24Alpha.Pc.v370, CFSG.KD.Fi24Alpha.Pc.v371]
theorem CFSG.KD.Fi24Alpha.Pc.p370 : Nat.beq (runC AR SD 368 (ckL CFSG.KD.Fi24Alpha.Pc.l372) 2 370 CFSG.KD.Fi24Alpha.Pc.l370) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v372 : Nat := CFSG.KD.Fi24Alpha.KV3 4
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v373 : Nat := CFSG.KD.Fi24Alpha.KV3 5
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l374 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v368, CFSG.KD.Fi24Alpha.Pc.v369, CFSG.KD.Fi24Alpha.Pc.v370, CFSG.KD.Fi24Alpha.Pc.v371, CFSG.KD.Fi24Alpha.Pc.v372, CFSG.KD.Fi24Alpha.Pc.v373]
theorem CFSG.KD.Fi24Alpha.Pc.p372 : Nat.beq (runC AR SD 368 (ckL CFSG.KD.Fi24Alpha.Pc.l374) 2 372 CFSG.KD.Fi24Alpha.Pc.l372) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v374 : Nat := CFSG.KD.Fi24Alpha.KV3 6
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v375 : Nat := CFSG.KD.Fi24Alpha.KV3 7
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l376 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v368, CFSG.KD.Fi24Alpha.Pc.v369, CFSG.KD.Fi24Alpha.Pc.v370, CFSG.KD.Fi24Alpha.Pc.v371, CFSG.KD.Fi24Alpha.Pc.v372, CFSG.KD.Fi24Alpha.Pc.v373, CFSG.KD.Fi24Alpha.Pc.v374, CFSG.KD.Fi24Alpha.Pc.v375]
theorem CFSG.KD.Fi24Alpha.Pc.p374 : Nat.beq (runC AR SD 368 (ckL CFSG.KD.Fi24Alpha.Pc.l376) 2 374 CFSG.KD.Fi24Alpha.Pc.l374) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v376 : Nat := CFSG.KD.Fi24Alpha.KV3 8
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v377 : Nat := CFSG.KD.Fi24Alpha.KV3 9
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l378 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v368, CFSG.KD.Fi24Alpha.Pc.v369, CFSG.KD.Fi24Alpha.Pc.v370, CFSG.KD.Fi24Alpha.Pc.v371, CFSG.KD.Fi24Alpha.Pc.v372, CFSG.KD.Fi24Alpha.Pc.v373, CFSG.KD.Fi24Alpha.Pc.v374, CFSG.KD.Fi24Alpha.Pc.v375, CFSG.KD.Fi24Alpha.Pc.v376, CFSG.KD.Fi24Alpha.Pc.v377]
theorem CFSG.KD.Fi24Alpha.Pc.p376 : Nat.beq (runC AR SD 368 (ckL CFSG.KD.Fi24Alpha.Pc.l378) 2 376 CFSG.KD.Fi24Alpha.Pc.l376) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v378 : Nat := CFSG.KD.Fi24Alpha.KV3 10
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v379 : Nat := CFSG.KD.Fi24Alpha.KV3 11
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l380 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v368, CFSG.KD.Fi24Alpha.Pc.v369, CFSG.KD.Fi24Alpha.Pc.v370, CFSG.KD.Fi24Alpha.Pc.v371, CFSG.KD.Fi24Alpha.Pc.v372, CFSG.KD.Fi24Alpha.Pc.v373, CFSG.KD.Fi24Alpha.Pc.v374, CFSG.KD.Fi24Alpha.Pc.v375, CFSG.KD.Fi24Alpha.Pc.v376, CFSG.KD.Fi24Alpha.Pc.v377, CFSG.KD.Fi24Alpha.Pc.v378, CFSG.KD.Fi24Alpha.Pc.v379]
theorem CFSG.KD.Fi24Alpha.Pc.p378 : Nat.beq (runC AR SD 368 (ckL CFSG.KD.Fi24Alpha.Pc.l380) 2 378 CFSG.KD.Fi24Alpha.Pc.l378) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v380 : Nat := CFSG.KD.Fi24Alpha.KV3 12
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v381 : Nat := CFSG.KD.Fi24Alpha.KV3 13
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l382 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v368, CFSG.KD.Fi24Alpha.Pc.v369, CFSG.KD.Fi24Alpha.Pc.v370, CFSG.KD.Fi24Alpha.Pc.v371, CFSG.KD.Fi24Alpha.Pc.v372, CFSG.KD.Fi24Alpha.Pc.v373, CFSG.KD.Fi24Alpha.Pc.v374, CFSG.KD.Fi24Alpha.Pc.v375, CFSG.KD.Fi24Alpha.Pc.v376, CFSG.KD.Fi24Alpha.Pc.v377, CFSG.KD.Fi24Alpha.Pc.v378, CFSG.KD.Fi24Alpha.Pc.v379, CFSG.KD.Fi24Alpha.Pc.v380, CFSG.KD.Fi24Alpha.Pc.v381]
theorem CFSG.KD.Fi24Alpha.Pc.p380 : Nat.beq (runC AR SD 368 (ckL CFSG.KD.Fi24Alpha.Pc.l382) 2 380 CFSG.KD.Fi24Alpha.Pc.l380) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v382 : Nat := CFSG.KD.Fi24Alpha.KV3 14
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v383 : Nat := CFSG.KD.Fi24Alpha.KV3 15
theorem CFSG.KD.Fi24Alpha.Pc.f30 : Nat.beq (runC AR SD 368 (finC AR SD (nat_lit 30) 368 384) 2 382 CFSG.KD.Fi24Alpha.Pc.l382) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk30 : chk (nat_lit 30) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 30) (lo := 368) (hi := 384) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 370) CFSG.KD.Fi24Alpha.Pc.p368 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 372) CFSG.KD.Fi24Alpha.Pc.p370 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 374) CFSG.KD.Fi24Alpha.Pc.p372 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 376) CFSG.KD.Fi24Alpha.Pc.p374 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 378) CFSG.KD.Fi24Alpha.Pc.p376 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 380) CFSG.KD.Fi24Alpha.Pc.p378 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 382) CFSG.KD.Fi24Alpha.Pc.p380 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f30

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v384 : Nat := CFSG.KD.Fi24Alpha.KV3 16
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v385 : Nat := CFSG.KD.Fi24Alpha.KV3 17
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l386 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v384, CFSG.KD.Fi24Alpha.Pc.v385]
theorem CFSG.KD.Fi24Alpha.Pc.p384 : Nat.beq (runC AR SD 384 (ckL CFSG.KD.Fi24Alpha.Pc.l386) 2 384 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v386 : Nat := CFSG.KD.Fi24Alpha.KV3 18
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v387 : Nat := CFSG.KD.Fi24Alpha.KV3 19
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l388 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v384, CFSG.KD.Fi24Alpha.Pc.v385, CFSG.KD.Fi24Alpha.Pc.v386, CFSG.KD.Fi24Alpha.Pc.v387]
theorem CFSG.KD.Fi24Alpha.Pc.p386 : Nat.beq (runC AR SD 384 (ckL CFSG.KD.Fi24Alpha.Pc.l388) 2 386 CFSG.KD.Fi24Alpha.Pc.l386) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v388 : Nat := CFSG.KD.Fi24Alpha.KV3 20
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v389 : Nat := CFSG.KD.Fi24Alpha.KV3 21
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l390 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v384, CFSG.KD.Fi24Alpha.Pc.v385, CFSG.KD.Fi24Alpha.Pc.v386, CFSG.KD.Fi24Alpha.Pc.v387, CFSG.KD.Fi24Alpha.Pc.v388, CFSG.KD.Fi24Alpha.Pc.v389]
theorem CFSG.KD.Fi24Alpha.Pc.p388 : Nat.beq (runC AR SD 384 (ckL CFSG.KD.Fi24Alpha.Pc.l390) 2 388 CFSG.KD.Fi24Alpha.Pc.l388) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v390 : Nat := CFSG.KD.Fi24Alpha.KV3 22
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v391 : Nat := CFSG.KD.Fi24Alpha.KV3 23
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l392 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v384, CFSG.KD.Fi24Alpha.Pc.v385, CFSG.KD.Fi24Alpha.Pc.v386, CFSG.KD.Fi24Alpha.Pc.v387, CFSG.KD.Fi24Alpha.Pc.v388, CFSG.KD.Fi24Alpha.Pc.v389, CFSG.KD.Fi24Alpha.Pc.v390, CFSG.KD.Fi24Alpha.Pc.v391]
theorem CFSG.KD.Fi24Alpha.Pc.p390 : Nat.beq (runC AR SD 384 (ckL CFSG.KD.Fi24Alpha.Pc.l392) 2 390 CFSG.KD.Fi24Alpha.Pc.l390) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v392 : Nat := CFSG.KD.Fi24Alpha.KV3 24
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v393 : Nat := CFSG.KD.Fi24Alpha.KV3 25
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l394 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v384, CFSG.KD.Fi24Alpha.Pc.v385, CFSG.KD.Fi24Alpha.Pc.v386, CFSG.KD.Fi24Alpha.Pc.v387, CFSG.KD.Fi24Alpha.Pc.v388, CFSG.KD.Fi24Alpha.Pc.v389, CFSG.KD.Fi24Alpha.Pc.v390, CFSG.KD.Fi24Alpha.Pc.v391, CFSG.KD.Fi24Alpha.Pc.v392, CFSG.KD.Fi24Alpha.Pc.v393]
theorem CFSG.KD.Fi24Alpha.Pc.p392 : Nat.beq (runC AR SD 384 (ckL CFSG.KD.Fi24Alpha.Pc.l394) 2 392 CFSG.KD.Fi24Alpha.Pc.l392) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v394 : Nat := CFSG.KD.Fi24Alpha.KV3 26
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v395 : Nat := CFSG.KD.Fi24Alpha.KV3 27
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l396 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v384, CFSG.KD.Fi24Alpha.Pc.v385, CFSG.KD.Fi24Alpha.Pc.v386, CFSG.KD.Fi24Alpha.Pc.v387, CFSG.KD.Fi24Alpha.Pc.v388, CFSG.KD.Fi24Alpha.Pc.v389, CFSG.KD.Fi24Alpha.Pc.v390, CFSG.KD.Fi24Alpha.Pc.v391, CFSG.KD.Fi24Alpha.Pc.v392, CFSG.KD.Fi24Alpha.Pc.v393, CFSG.KD.Fi24Alpha.Pc.v394, CFSG.KD.Fi24Alpha.Pc.v395]
theorem CFSG.KD.Fi24Alpha.Pc.p394 : Nat.beq (runC AR SD 384 (ckL CFSG.KD.Fi24Alpha.Pc.l396) 2 394 CFSG.KD.Fi24Alpha.Pc.l394) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v396 : Nat := CFSG.KD.Fi24Alpha.KV3 28
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v397 : Nat := CFSG.KD.Fi24Alpha.KV3 29
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l398 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v384, CFSG.KD.Fi24Alpha.Pc.v385, CFSG.KD.Fi24Alpha.Pc.v386, CFSG.KD.Fi24Alpha.Pc.v387, CFSG.KD.Fi24Alpha.Pc.v388, CFSG.KD.Fi24Alpha.Pc.v389, CFSG.KD.Fi24Alpha.Pc.v390, CFSG.KD.Fi24Alpha.Pc.v391, CFSG.KD.Fi24Alpha.Pc.v392, CFSG.KD.Fi24Alpha.Pc.v393, CFSG.KD.Fi24Alpha.Pc.v394, CFSG.KD.Fi24Alpha.Pc.v395, CFSG.KD.Fi24Alpha.Pc.v396, CFSG.KD.Fi24Alpha.Pc.v397]
theorem CFSG.KD.Fi24Alpha.Pc.p396 : Nat.beq (runC AR SD 384 (ckL CFSG.KD.Fi24Alpha.Pc.l398) 2 396 CFSG.KD.Fi24Alpha.Pc.l396) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v398 : Nat := CFSG.KD.Fi24Alpha.KV3 30
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v399 : Nat := CFSG.KD.Fi24Alpha.KV3 31
theorem CFSG.KD.Fi24Alpha.Pc.f31 : Nat.beq (runC AR SD 384 (finC AR SD (nat_lit 31) 384 400) 2 398 CFSG.KD.Fi24Alpha.Pc.l398) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk31 : chk (nat_lit 31) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 31) (lo := 384) (hi := 400) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 386) CFSG.KD.Fi24Alpha.Pc.p384 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 388) CFSG.KD.Fi24Alpha.Pc.p386 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 390) CFSG.KD.Fi24Alpha.Pc.p388 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 392) CFSG.KD.Fi24Alpha.Pc.p390 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 394) CFSG.KD.Fi24Alpha.Pc.p392 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 396) CFSG.KD.Fi24Alpha.Pc.p394 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 398) CFSG.KD.Fi24Alpha.Pc.p396 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f31

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v400 : Nat := CFSG.KD.Fi24Alpha.KV3 32
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v401 : Nat := CFSG.KD.Fi24Alpha.KV3 33
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l402 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v400, CFSG.KD.Fi24Alpha.Pc.v401]
theorem CFSG.KD.Fi24Alpha.Pc.p400 : Nat.beq (runC AR SD 400 (ckL CFSG.KD.Fi24Alpha.Pc.l402) 2 400 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v402 : Nat := CFSG.KD.Fi24Alpha.KV3 34
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v403 : Nat := CFSG.KD.Fi24Alpha.KV3 35
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l404 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v400, CFSG.KD.Fi24Alpha.Pc.v401, CFSG.KD.Fi24Alpha.Pc.v402, CFSG.KD.Fi24Alpha.Pc.v403]
theorem CFSG.KD.Fi24Alpha.Pc.p402 : Nat.beq (runC AR SD 400 (ckL CFSG.KD.Fi24Alpha.Pc.l404) 2 402 CFSG.KD.Fi24Alpha.Pc.l402) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v404 : Nat := CFSG.KD.Fi24Alpha.KV3 36
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v405 : Nat := CFSG.KD.Fi24Alpha.KV3 37
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l406 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v400, CFSG.KD.Fi24Alpha.Pc.v401, CFSG.KD.Fi24Alpha.Pc.v402, CFSG.KD.Fi24Alpha.Pc.v403, CFSG.KD.Fi24Alpha.Pc.v404, CFSG.KD.Fi24Alpha.Pc.v405]
theorem CFSG.KD.Fi24Alpha.Pc.p404 : Nat.beq (runC AR SD 400 (ckL CFSG.KD.Fi24Alpha.Pc.l406) 2 404 CFSG.KD.Fi24Alpha.Pc.l404) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v406 : Nat := CFSG.KD.Fi24Alpha.KV3 38
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v407 : Nat := CFSG.KD.Fi24Alpha.KV3 39
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l408 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v400, CFSG.KD.Fi24Alpha.Pc.v401, CFSG.KD.Fi24Alpha.Pc.v402, CFSG.KD.Fi24Alpha.Pc.v403, CFSG.KD.Fi24Alpha.Pc.v404, CFSG.KD.Fi24Alpha.Pc.v405, CFSG.KD.Fi24Alpha.Pc.v406, CFSG.KD.Fi24Alpha.Pc.v407]
theorem CFSG.KD.Fi24Alpha.Pc.p406 : Nat.beq (runC AR SD 400 (ckL CFSG.KD.Fi24Alpha.Pc.l408) 2 406 CFSG.KD.Fi24Alpha.Pc.l406) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v408 : Nat := CFSG.KD.Fi24Alpha.KV3 40
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v409 : Nat := CFSG.KD.Fi24Alpha.KV3 41
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l410 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v400, CFSG.KD.Fi24Alpha.Pc.v401, CFSG.KD.Fi24Alpha.Pc.v402, CFSG.KD.Fi24Alpha.Pc.v403, CFSG.KD.Fi24Alpha.Pc.v404, CFSG.KD.Fi24Alpha.Pc.v405, CFSG.KD.Fi24Alpha.Pc.v406, CFSG.KD.Fi24Alpha.Pc.v407, CFSG.KD.Fi24Alpha.Pc.v408, CFSG.KD.Fi24Alpha.Pc.v409]
theorem CFSG.KD.Fi24Alpha.Pc.p408 : Nat.beq (runC AR SD 400 (ckL CFSG.KD.Fi24Alpha.Pc.l410) 2 408 CFSG.KD.Fi24Alpha.Pc.l408) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v410 : Nat := CFSG.KD.Fi24Alpha.KV3 42
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v411 : Nat := CFSG.KD.Fi24Alpha.KV3 43
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l412 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v400, CFSG.KD.Fi24Alpha.Pc.v401, CFSG.KD.Fi24Alpha.Pc.v402, CFSG.KD.Fi24Alpha.Pc.v403, CFSG.KD.Fi24Alpha.Pc.v404, CFSG.KD.Fi24Alpha.Pc.v405, CFSG.KD.Fi24Alpha.Pc.v406, CFSG.KD.Fi24Alpha.Pc.v407, CFSG.KD.Fi24Alpha.Pc.v408, CFSG.KD.Fi24Alpha.Pc.v409, CFSG.KD.Fi24Alpha.Pc.v410, CFSG.KD.Fi24Alpha.Pc.v411]
theorem CFSG.KD.Fi24Alpha.Pc.p410 : Nat.beq (runC AR SD 400 (ckL CFSG.KD.Fi24Alpha.Pc.l412) 2 410 CFSG.KD.Fi24Alpha.Pc.l410) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v412 : Nat := CFSG.KD.Fi24Alpha.KV3 44
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v413 : Nat := CFSG.KD.Fi24Alpha.KV3 45
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l414 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v400, CFSG.KD.Fi24Alpha.Pc.v401, CFSG.KD.Fi24Alpha.Pc.v402, CFSG.KD.Fi24Alpha.Pc.v403, CFSG.KD.Fi24Alpha.Pc.v404, CFSG.KD.Fi24Alpha.Pc.v405, CFSG.KD.Fi24Alpha.Pc.v406, CFSG.KD.Fi24Alpha.Pc.v407, CFSG.KD.Fi24Alpha.Pc.v408, CFSG.KD.Fi24Alpha.Pc.v409, CFSG.KD.Fi24Alpha.Pc.v410, CFSG.KD.Fi24Alpha.Pc.v411, CFSG.KD.Fi24Alpha.Pc.v412, CFSG.KD.Fi24Alpha.Pc.v413]
theorem CFSG.KD.Fi24Alpha.Pc.p412 : Nat.beq (runC AR SD 400 (ckL CFSG.KD.Fi24Alpha.Pc.l414) 2 412 CFSG.KD.Fi24Alpha.Pc.l412) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v414 : Nat := CFSG.KD.Fi24Alpha.KV3 46
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v415 : Nat := CFSG.KD.Fi24Alpha.KV3 47
theorem CFSG.KD.Fi24Alpha.Pc.f32 : Nat.beq (runC AR SD 400 (finC AR SD (nat_lit 32) 400 416) 2 414 CFSG.KD.Fi24Alpha.Pc.l414) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk32 : chk (nat_lit 32) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 32) (lo := 400) (hi := 416) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 402) CFSG.KD.Fi24Alpha.Pc.p400 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 404) CFSG.KD.Fi24Alpha.Pc.p402 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 406) CFSG.KD.Fi24Alpha.Pc.p404 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 408) CFSG.KD.Fi24Alpha.Pc.p406 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 410) CFSG.KD.Fi24Alpha.Pc.p408 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 412) CFSG.KD.Fi24Alpha.Pc.p410 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 414) CFSG.KD.Fi24Alpha.Pc.p412 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f32

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v416 : Nat := CFSG.KD.Fi24Alpha.KV3 48
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v417 : Nat := CFSG.KD.Fi24Alpha.KV3 49
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l418 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v416, CFSG.KD.Fi24Alpha.Pc.v417]
theorem CFSG.KD.Fi24Alpha.Pc.p416 : Nat.beq (runC AR SD 416 (ckL CFSG.KD.Fi24Alpha.Pc.l418) 2 416 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v418 : Nat := CFSG.KD.Fi24Alpha.KV3 50
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v419 : Nat := CFSG.KD.Fi24Alpha.KV3 51
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l420 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v416, CFSG.KD.Fi24Alpha.Pc.v417, CFSG.KD.Fi24Alpha.Pc.v418, CFSG.KD.Fi24Alpha.Pc.v419]
theorem CFSG.KD.Fi24Alpha.Pc.p418 : Nat.beq (runC AR SD 416 (ckL CFSG.KD.Fi24Alpha.Pc.l420) 2 418 CFSG.KD.Fi24Alpha.Pc.l418) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v420 : Nat := CFSG.KD.Fi24Alpha.KV3 52
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v421 : Nat := CFSG.KD.Fi24Alpha.KV3 53
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l422 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v416, CFSG.KD.Fi24Alpha.Pc.v417, CFSG.KD.Fi24Alpha.Pc.v418, CFSG.KD.Fi24Alpha.Pc.v419, CFSG.KD.Fi24Alpha.Pc.v420, CFSG.KD.Fi24Alpha.Pc.v421]
theorem CFSG.KD.Fi24Alpha.Pc.p420 : Nat.beq (runC AR SD 416 (ckL CFSG.KD.Fi24Alpha.Pc.l422) 2 420 CFSG.KD.Fi24Alpha.Pc.l420) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v422 : Nat := CFSG.KD.Fi24Alpha.KV3 54
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v423 : Nat := CFSG.KD.Fi24Alpha.KV3 55
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l424 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v416, CFSG.KD.Fi24Alpha.Pc.v417, CFSG.KD.Fi24Alpha.Pc.v418, CFSG.KD.Fi24Alpha.Pc.v419, CFSG.KD.Fi24Alpha.Pc.v420, CFSG.KD.Fi24Alpha.Pc.v421, CFSG.KD.Fi24Alpha.Pc.v422, CFSG.KD.Fi24Alpha.Pc.v423]
theorem CFSG.KD.Fi24Alpha.Pc.p422 : Nat.beq (runC AR SD 416 (ckL CFSG.KD.Fi24Alpha.Pc.l424) 2 422 CFSG.KD.Fi24Alpha.Pc.l422) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v424 : Nat := CFSG.KD.Fi24Alpha.KV3 56
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v425 : Nat := CFSG.KD.Fi24Alpha.KV3 57
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l426 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v416, CFSG.KD.Fi24Alpha.Pc.v417, CFSG.KD.Fi24Alpha.Pc.v418, CFSG.KD.Fi24Alpha.Pc.v419, CFSG.KD.Fi24Alpha.Pc.v420, CFSG.KD.Fi24Alpha.Pc.v421, CFSG.KD.Fi24Alpha.Pc.v422, CFSG.KD.Fi24Alpha.Pc.v423, CFSG.KD.Fi24Alpha.Pc.v424, CFSG.KD.Fi24Alpha.Pc.v425]
theorem CFSG.KD.Fi24Alpha.Pc.p424 : Nat.beq (runC AR SD 416 (ckL CFSG.KD.Fi24Alpha.Pc.l426) 2 424 CFSG.KD.Fi24Alpha.Pc.l424) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v426 : Nat := CFSG.KD.Fi24Alpha.KV3 58
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v427 : Nat := CFSG.KD.Fi24Alpha.KV3 59
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l428 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v416, CFSG.KD.Fi24Alpha.Pc.v417, CFSG.KD.Fi24Alpha.Pc.v418, CFSG.KD.Fi24Alpha.Pc.v419, CFSG.KD.Fi24Alpha.Pc.v420, CFSG.KD.Fi24Alpha.Pc.v421, CFSG.KD.Fi24Alpha.Pc.v422, CFSG.KD.Fi24Alpha.Pc.v423, CFSG.KD.Fi24Alpha.Pc.v424, CFSG.KD.Fi24Alpha.Pc.v425, CFSG.KD.Fi24Alpha.Pc.v426, CFSG.KD.Fi24Alpha.Pc.v427]
theorem CFSG.KD.Fi24Alpha.Pc.p426 : Nat.beq (runC AR SD 416 (ckL CFSG.KD.Fi24Alpha.Pc.l428) 2 426 CFSG.KD.Fi24Alpha.Pc.l426) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v428 : Nat := CFSG.KD.Fi24Alpha.KV3 60
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v429 : Nat := CFSG.KD.Fi24Alpha.KV3 61
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l430 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v416, CFSG.KD.Fi24Alpha.Pc.v417, CFSG.KD.Fi24Alpha.Pc.v418, CFSG.KD.Fi24Alpha.Pc.v419, CFSG.KD.Fi24Alpha.Pc.v420, CFSG.KD.Fi24Alpha.Pc.v421, CFSG.KD.Fi24Alpha.Pc.v422, CFSG.KD.Fi24Alpha.Pc.v423, CFSG.KD.Fi24Alpha.Pc.v424, CFSG.KD.Fi24Alpha.Pc.v425, CFSG.KD.Fi24Alpha.Pc.v426, CFSG.KD.Fi24Alpha.Pc.v427, CFSG.KD.Fi24Alpha.Pc.v428, CFSG.KD.Fi24Alpha.Pc.v429]
theorem CFSG.KD.Fi24Alpha.Pc.p428 : Nat.beq (runC AR SD 416 (ckL CFSG.KD.Fi24Alpha.Pc.l430) 2 428 CFSG.KD.Fi24Alpha.Pc.l428) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v430 : Nat := CFSG.KD.Fi24Alpha.KV3 62
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v431 : Nat := CFSG.KD.Fi24Alpha.KV3 63
theorem CFSG.KD.Fi24Alpha.Pc.f33 : Nat.beq (runC AR SD 416 (finC AR SD (nat_lit 33) 416 432) 2 430 CFSG.KD.Fi24Alpha.Pc.l430) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk33 : chk (nat_lit 33) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 33) (lo := 416) (hi := 432) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 418) CFSG.KD.Fi24Alpha.Pc.p416 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 420) CFSG.KD.Fi24Alpha.Pc.p418 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 422) CFSG.KD.Fi24Alpha.Pc.p420 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 424) CFSG.KD.Fi24Alpha.Pc.p422 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 426) CFSG.KD.Fi24Alpha.Pc.p424 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 428) CFSG.KD.Fi24Alpha.Pc.p426 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 430) CFSG.KD.Fi24Alpha.Pc.p428 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f33

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v432 : Nat := CFSG.KD.Fi24Alpha.KV3 64
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v433 : Nat := CFSG.KD.Fi24Alpha.KV3 65
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l434 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v432, CFSG.KD.Fi24Alpha.Pc.v433]
theorem CFSG.KD.Fi24Alpha.Pc.p432 : Nat.beq (runC AR SD 432 (ckL CFSG.KD.Fi24Alpha.Pc.l434) 2 432 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v434 : Nat := CFSG.KD.Fi24Alpha.KV3 66
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v435 : Nat := CFSG.KD.Fi24Alpha.KV3 67
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l436 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v432, CFSG.KD.Fi24Alpha.Pc.v433, CFSG.KD.Fi24Alpha.Pc.v434, CFSG.KD.Fi24Alpha.Pc.v435]
theorem CFSG.KD.Fi24Alpha.Pc.p434 : Nat.beq (runC AR SD 432 (ckL CFSG.KD.Fi24Alpha.Pc.l436) 2 434 CFSG.KD.Fi24Alpha.Pc.l434) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v436 : Nat := CFSG.KD.Fi24Alpha.KV3 68
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v437 : Nat := CFSG.KD.Fi24Alpha.KV3 69
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l438 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v432, CFSG.KD.Fi24Alpha.Pc.v433, CFSG.KD.Fi24Alpha.Pc.v434, CFSG.KD.Fi24Alpha.Pc.v435, CFSG.KD.Fi24Alpha.Pc.v436, CFSG.KD.Fi24Alpha.Pc.v437]
theorem CFSG.KD.Fi24Alpha.Pc.p436 : Nat.beq (runC AR SD 432 (ckL CFSG.KD.Fi24Alpha.Pc.l438) 2 436 CFSG.KD.Fi24Alpha.Pc.l436) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v438 : Nat := CFSG.KD.Fi24Alpha.KV3 70
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v439 : Nat := CFSG.KD.Fi24Alpha.KV3 71
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l440 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v432, CFSG.KD.Fi24Alpha.Pc.v433, CFSG.KD.Fi24Alpha.Pc.v434, CFSG.KD.Fi24Alpha.Pc.v435, CFSG.KD.Fi24Alpha.Pc.v436, CFSG.KD.Fi24Alpha.Pc.v437, CFSG.KD.Fi24Alpha.Pc.v438, CFSG.KD.Fi24Alpha.Pc.v439]
theorem CFSG.KD.Fi24Alpha.Pc.p438 : Nat.beq (runC AR SD 432 (ckL CFSG.KD.Fi24Alpha.Pc.l440) 2 438 CFSG.KD.Fi24Alpha.Pc.l438) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v440 : Nat := CFSG.KD.Fi24Alpha.KV3 72
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v441 : Nat := CFSG.KD.Fi24Alpha.KV3 73
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l442 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v432, CFSG.KD.Fi24Alpha.Pc.v433, CFSG.KD.Fi24Alpha.Pc.v434, CFSG.KD.Fi24Alpha.Pc.v435, CFSG.KD.Fi24Alpha.Pc.v436, CFSG.KD.Fi24Alpha.Pc.v437, CFSG.KD.Fi24Alpha.Pc.v438, CFSG.KD.Fi24Alpha.Pc.v439, CFSG.KD.Fi24Alpha.Pc.v440, CFSG.KD.Fi24Alpha.Pc.v441]
theorem CFSG.KD.Fi24Alpha.Pc.p440 : Nat.beq (runC AR SD 432 (ckL CFSG.KD.Fi24Alpha.Pc.l442) 2 440 CFSG.KD.Fi24Alpha.Pc.l440) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v442 : Nat := CFSG.KD.Fi24Alpha.KV3 74
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v443 : Nat := CFSG.KD.Fi24Alpha.KV3 75
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l444 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v432, CFSG.KD.Fi24Alpha.Pc.v433, CFSG.KD.Fi24Alpha.Pc.v434, CFSG.KD.Fi24Alpha.Pc.v435, CFSG.KD.Fi24Alpha.Pc.v436, CFSG.KD.Fi24Alpha.Pc.v437, CFSG.KD.Fi24Alpha.Pc.v438, CFSG.KD.Fi24Alpha.Pc.v439, CFSG.KD.Fi24Alpha.Pc.v440, CFSG.KD.Fi24Alpha.Pc.v441, CFSG.KD.Fi24Alpha.Pc.v442, CFSG.KD.Fi24Alpha.Pc.v443]
theorem CFSG.KD.Fi24Alpha.Pc.p442 : Nat.beq (runC AR SD 432 (ckL CFSG.KD.Fi24Alpha.Pc.l444) 2 442 CFSG.KD.Fi24Alpha.Pc.l442) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v444 : Nat := CFSG.KD.Fi24Alpha.KV3 76
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v445 : Nat := CFSG.KD.Fi24Alpha.KV3 77
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l446 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v432, CFSG.KD.Fi24Alpha.Pc.v433, CFSG.KD.Fi24Alpha.Pc.v434, CFSG.KD.Fi24Alpha.Pc.v435, CFSG.KD.Fi24Alpha.Pc.v436, CFSG.KD.Fi24Alpha.Pc.v437, CFSG.KD.Fi24Alpha.Pc.v438, CFSG.KD.Fi24Alpha.Pc.v439, CFSG.KD.Fi24Alpha.Pc.v440, CFSG.KD.Fi24Alpha.Pc.v441, CFSG.KD.Fi24Alpha.Pc.v442, CFSG.KD.Fi24Alpha.Pc.v443, CFSG.KD.Fi24Alpha.Pc.v444, CFSG.KD.Fi24Alpha.Pc.v445]
theorem CFSG.KD.Fi24Alpha.Pc.p444 : Nat.beq (runC AR SD 432 (ckL CFSG.KD.Fi24Alpha.Pc.l446) 2 444 CFSG.KD.Fi24Alpha.Pc.l444) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v446 : Nat := CFSG.KD.Fi24Alpha.KV3 78
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v447 : Nat := CFSG.KD.Fi24Alpha.KV3 79
theorem CFSG.KD.Fi24Alpha.Pc.f34 : Nat.beq (runC AR SD 432 (finC AR SD (nat_lit 34) 432 448) 2 446 CFSG.KD.Fi24Alpha.Pc.l446) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk34 : chk (nat_lit 34) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 34) (lo := 432) (hi := 448) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 434) CFSG.KD.Fi24Alpha.Pc.p432 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 436) CFSG.KD.Fi24Alpha.Pc.p434 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 438) CFSG.KD.Fi24Alpha.Pc.p436 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 440) CFSG.KD.Fi24Alpha.Pc.p438 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 442) CFSG.KD.Fi24Alpha.Pc.p440 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 444) CFSG.KD.Fi24Alpha.Pc.p442 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 446) CFSG.KD.Fi24Alpha.Pc.p444 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f34

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v448 : Nat := CFSG.KD.Fi24Alpha.KV3 80
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v449 : Nat := CFSG.KD.Fi24Alpha.KV3 81
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l450 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v448, CFSG.KD.Fi24Alpha.Pc.v449]
theorem CFSG.KD.Fi24Alpha.Pc.p448 : Nat.beq (runC AR SD 448 (ckL CFSG.KD.Fi24Alpha.Pc.l450) 2 448 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v450 : Nat := CFSG.KD.Fi24Alpha.KV3 82
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v451 : Nat := CFSG.KD.Fi24Alpha.KV3 83
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l452 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v448, CFSG.KD.Fi24Alpha.Pc.v449, CFSG.KD.Fi24Alpha.Pc.v450, CFSG.KD.Fi24Alpha.Pc.v451]
theorem CFSG.KD.Fi24Alpha.Pc.p450 : Nat.beq (runC AR SD 448 (ckL CFSG.KD.Fi24Alpha.Pc.l452) 2 450 CFSG.KD.Fi24Alpha.Pc.l450) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v452 : Nat := CFSG.KD.Fi24Alpha.KV3 84
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v453 : Nat := CFSG.KD.Fi24Alpha.KV3 85
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l454 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v448, CFSG.KD.Fi24Alpha.Pc.v449, CFSG.KD.Fi24Alpha.Pc.v450, CFSG.KD.Fi24Alpha.Pc.v451, CFSG.KD.Fi24Alpha.Pc.v452, CFSG.KD.Fi24Alpha.Pc.v453]
theorem CFSG.KD.Fi24Alpha.Pc.p452 : Nat.beq (runC AR SD 448 (ckL CFSG.KD.Fi24Alpha.Pc.l454) 2 452 CFSG.KD.Fi24Alpha.Pc.l452) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v454 : Nat := CFSG.KD.Fi24Alpha.KV3 86
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v455 : Nat := CFSG.KD.Fi24Alpha.KV3 87
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l456 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v448, CFSG.KD.Fi24Alpha.Pc.v449, CFSG.KD.Fi24Alpha.Pc.v450, CFSG.KD.Fi24Alpha.Pc.v451, CFSG.KD.Fi24Alpha.Pc.v452, CFSG.KD.Fi24Alpha.Pc.v453, CFSG.KD.Fi24Alpha.Pc.v454, CFSG.KD.Fi24Alpha.Pc.v455]
theorem CFSG.KD.Fi24Alpha.Pc.p454 : Nat.beq (runC AR SD 448 (ckL CFSG.KD.Fi24Alpha.Pc.l456) 2 454 CFSG.KD.Fi24Alpha.Pc.l454) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v456 : Nat := CFSG.KD.Fi24Alpha.KV3 88
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v457 : Nat := CFSG.KD.Fi24Alpha.KV3 89
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l458 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v448, CFSG.KD.Fi24Alpha.Pc.v449, CFSG.KD.Fi24Alpha.Pc.v450, CFSG.KD.Fi24Alpha.Pc.v451, CFSG.KD.Fi24Alpha.Pc.v452, CFSG.KD.Fi24Alpha.Pc.v453, CFSG.KD.Fi24Alpha.Pc.v454, CFSG.KD.Fi24Alpha.Pc.v455, CFSG.KD.Fi24Alpha.Pc.v456, CFSG.KD.Fi24Alpha.Pc.v457]
theorem CFSG.KD.Fi24Alpha.Pc.p456 : Nat.beq (runC AR SD 448 (ckL CFSG.KD.Fi24Alpha.Pc.l458) 2 456 CFSG.KD.Fi24Alpha.Pc.l456) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v458 : Nat := CFSG.KD.Fi24Alpha.KV3 90
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v459 : Nat := CFSG.KD.Fi24Alpha.KV3 91
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l460 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v448, CFSG.KD.Fi24Alpha.Pc.v449, CFSG.KD.Fi24Alpha.Pc.v450, CFSG.KD.Fi24Alpha.Pc.v451, CFSG.KD.Fi24Alpha.Pc.v452, CFSG.KD.Fi24Alpha.Pc.v453, CFSG.KD.Fi24Alpha.Pc.v454, CFSG.KD.Fi24Alpha.Pc.v455, CFSG.KD.Fi24Alpha.Pc.v456, CFSG.KD.Fi24Alpha.Pc.v457, CFSG.KD.Fi24Alpha.Pc.v458, CFSG.KD.Fi24Alpha.Pc.v459]
theorem CFSG.KD.Fi24Alpha.Pc.p458 : Nat.beq (runC AR SD 448 (ckL CFSG.KD.Fi24Alpha.Pc.l460) 2 458 CFSG.KD.Fi24Alpha.Pc.l458) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v460 : Nat := CFSG.KD.Fi24Alpha.KV3 92
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v461 : Nat := CFSG.KD.Fi24Alpha.KV3 93
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l462 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v448, CFSG.KD.Fi24Alpha.Pc.v449, CFSG.KD.Fi24Alpha.Pc.v450, CFSG.KD.Fi24Alpha.Pc.v451, CFSG.KD.Fi24Alpha.Pc.v452, CFSG.KD.Fi24Alpha.Pc.v453, CFSG.KD.Fi24Alpha.Pc.v454, CFSG.KD.Fi24Alpha.Pc.v455, CFSG.KD.Fi24Alpha.Pc.v456, CFSG.KD.Fi24Alpha.Pc.v457, CFSG.KD.Fi24Alpha.Pc.v458, CFSG.KD.Fi24Alpha.Pc.v459, CFSG.KD.Fi24Alpha.Pc.v460, CFSG.KD.Fi24Alpha.Pc.v461]
theorem CFSG.KD.Fi24Alpha.Pc.p460 : Nat.beq (runC AR SD 448 (ckL CFSG.KD.Fi24Alpha.Pc.l462) 2 460 CFSG.KD.Fi24Alpha.Pc.l460) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v462 : Nat := CFSG.KD.Fi24Alpha.KV3 94
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v463 : Nat := CFSG.KD.Fi24Alpha.KV3 95
theorem CFSG.KD.Fi24Alpha.Pc.f35 : Nat.beq (runC AR SD 448 (finC AR SD (nat_lit 35) 448 464) 2 462 CFSG.KD.Fi24Alpha.Pc.l462) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk35 : chk (nat_lit 35) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 35) (lo := 448) (hi := 464) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 450) CFSG.KD.Fi24Alpha.Pc.p448 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 452) CFSG.KD.Fi24Alpha.Pc.p450 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 454) CFSG.KD.Fi24Alpha.Pc.p452 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 456) CFSG.KD.Fi24Alpha.Pc.p454 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 458) CFSG.KD.Fi24Alpha.Pc.p456 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 460) CFSG.KD.Fi24Alpha.Pc.p458 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 462) CFSG.KD.Fi24Alpha.Pc.p460 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f35

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v464 : Nat := CFSG.KD.Fi24Alpha.KV3 96
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v465 : Nat := CFSG.KD.Fi24Alpha.KV3 97
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l466 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v464, CFSG.KD.Fi24Alpha.Pc.v465]
theorem CFSG.KD.Fi24Alpha.Pc.p464 : Nat.beq (runC AR SD 464 (ckL CFSG.KD.Fi24Alpha.Pc.l466) 2 464 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v466 : Nat := CFSG.KD.Fi24Alpha.KV3 98
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v467 : Nat := CFSG.KD.Fi24Alpha.KV3 99
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l468 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v464, CFSG.KD.Fi24Alpha.Pc.v465, CFSG.KD.Fi24Alpha.Pc.v466, CFSG.KD.Fi24Alpha.Pc.v467]
theorem CFSG.KD.Fi24Alpha.Pc.p466 : Nat.beq (runC AR SD 464 (ckL CFSG.KD.Fi24Alpha.Pc.l468) 2 466 CFSG.KD.Fi24Alpha.Pc.l466) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v468 : Nat := CFSG.KD.Fi24Alpha.KV3 100
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v469 : Nat := CFSG.KD.Fi24Alpha.KV3 101
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l470 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v464, CFSG.KD.Fi24Alpha.Pc.v465, CFSG.KD.Fi24Alpha.Pc.v466, CFSG.KD.Fi24Alpha.Pc.v467, CFSG.KD.Fi24Alpha.Pc.v468, CFSG.KD.Fi24Alpha.Pc.v469]
theorem CFSG.KD.Fi24Alpha.Pc.p468 : Nat.beq (runC AR SD 464 (ckL CFSG.KD.Fi24Alpha.Pc.l470) 2 468 CFSG.KD.Fi24Alpha.Pc.l468) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v470 : Nat := CFSG.KD.Fi24Alpha.KV3 102
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v471 : Nat := CFSG.KD.Fi24Alpha.KV3 103
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l472 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v464, CFSG.KD.Fi24Alpha.Pc.v465, CFSG.KD.Fi24Alpha.Pc.v466, CFSG.KD.Fi24Alpha.Pc.v467, CFSG.KD.Fi24Alpha.Pc.v468, CFSG.KD.Fi24Alpha.Pc.v469, CFSG.KD.Fi24Alpha.Pc.v470, CFSG.KD.Fi24Alpha.Pc.v471]
theorem CFSG.KD.Fi24Alpha.Pc.p470 : Nat.beq (runC AR SD 464 (ckL CFSG.KD.Fi24Alpha.Pc.l472) 2 470 CFSG.KD.Fi24Alpha.Pc.l470) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v472 : Nat := CFSG.KD.Fi24Alpha.KV3 104
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v473 : Nat := CFSG.KD.Fi24Alpha.KV3 105
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l474 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v464, CFSG.KD.Fi24Alpha.Pc.v465, CFSG.KD.Fi24Alpha.Pc.v466, CFSG.KD.Fi24Alpha.Pc.v467, CFSG.KD.Fi24Alpha.Pc.v468, CFSG.KD.Fi24Alpha.Pc.v469, CFSG.KD.Fi24Alpha.Pc.v470, CFSG.KD.Fi24Alpha.Pc.v471, CFSG.KD.Fi24Alpha.Pc.v472, CFSG.KD.Fi24Alpha.Pc.v473]
theorem CFSG.KD.Fi24Alpha.Pc.p472 : Nat.beq (runC AR SD 464 (ckL CFSG.KD.Fi24Alpha.Pc.l474) 2 472 CFSG.KD.Fi24Alpha.Pc.l472) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v474 : Nat := CFSG.KD.Fi24Alpha.KV3 106
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v475 : Nat := CFSG.KD.Fi24Alpha.KV3 107
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l476 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v464, CFSG.KD.Fi24Alpha.Pc.v465, CFSG.KD.Fi24Alpha.Pc.v466, CFSG.KD.Fi24Alpha.Pc.v467, CFSG.KD.Fi24Alpha.Pc.v468, CFSG.KD.Fi24Alpha.Pc.v469, CFSG.KD.Fi24Alpha.Pc.v470, CFSG.KD.Fi24Alpha.Pc.v471, CFSG.KD.Fi24Alpha.Pc.v472, CFSG.KD.Fi24Alpha.Pc.v473, CFSG.KD.Fi24Alpha.Pc.v474, CFSG.KD.Fi24Alpha.Pc.v475]
theorem CFSG.KD.Fi24Alpha.Pc.p474 : Nat.beq (runC AR SD 464 (ckL CFSG.KD.Fi24Alpha.Pc.l476) 2 474 CFSG.KD.Fi24Alpha.Pc.l474) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v476 : Nat := CFSG.KD.Fi24Alpha.KV3 108
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v477 : Nat := CFSG.KD.Fi24Alpha.KV3 109
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l478 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v464, CFSG.KD.Fi24Alpha.Pc.v465, CFSG.KD.Fi24Alpha.Pc.v466, CFSG.KD.Fi24Alpha.Pc.v467, CFSG.KD.Fi24Alpha.Pc.v468, CFSG.KD.Fi24Alpha.Pc.v469, CFSG.KD.Fi24Alpha.Pc.v470, CFSG.KD.Fi24Alpha.Pc.v471, CFSG.KD.Fi24Alpha.Pc.v472, CFSG.KD.Fi24Alpha.Pc.v473, CFSG.KD.Fi24Alpha.Pc.v474, CFSG.KD.Fi24Alpha.Pc.v475, CFSG.KD.Fi24Alpha.Pc.v476, CFSG.KD.Fi24Alpha.Pc.v477]
theorem CFSG.KD.Fi24Alpha.Pc.p476 : Nat.beq (runC AR SD 464 (ckL CFSG.KD.Fi24Alpha.Pc.l478) 2 476 CFSG.KD.Fi24Alpha.Pc.l476) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v478 : Nat := CFSG.KD.Fi24Alpha.KV3 110
theorem CFSG.KD.Fi24Alpha.Pc.f36 : Nat.beq (runC AR SD 464 (finC AR SD (nat_lit 36) 464 479) 1 478 CFSG.KD.Fi24Alpha.Pc.l478) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk36 : chk (nat_lit 36) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 36) (lo := 464) (hi := 479) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 466) CFSG.KD.Fi24Alpha.Pc.p464 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 468) CFSG.KD.Fi24Alpha.Pc.p466 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 470) CFSG.KD.Fi24Alpha.Pc.p468 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 472) CFSG.KD.Fi24Alpha.Pc.p470 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 474) CFSG.KD.Fi24Alpha.Pc.p472 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 476) CFSG.KD.Fi24Alpha.Pc.p474 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 478) CFSG.KD.Fi24Alpha.Pc.p476 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f36

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v479 : Nat := CFSG.KD.Fi24Alpha.KV3 111
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v480 : Nat := CFSG.KD.Fi24Alpha.KV3 112
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l481 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v479, CFSG.KD.Fi24Alpha.Pc.v480]
theorem CFSG.KD.Fi24Alpha.Pc.p479 : Nat.beq (runC AR SD 479 (ckL CFSG.KD.Fi24Alpha.Pc.l481) 2 479 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v481 : Nat := CFSG.KD.Fi24Alpha.KV3 113
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v482 : Nat := CFSG.KD.Fi24Alpha.KV3 114
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l483 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v479, CFSG.KD.Fi24Alpha.Pc.v480, CFSG.KD.Fi24Alpha.Pc.v481, CFSG.KD.Fi24Alpha.Pc.v482]
theorem CFSG.KD.Fi24Alpha.Pc.p481 : Nat.beq (runC AR SD 479 (ckL CFSG.KD.Fi24Alpha.Pc.l483) 2 481 CFSG.KD.Fi24Alpha.Pc.l481) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v483 : Nat := CFSG.KD.Fi24Alpha.KV3 115
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v484 : Nat := CFSG.KD.Fi24Alpha.KV3 116
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l485 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v479, CFSG.KD.Fi24Alpha.Pc.v480, CFSG.KD.Fi24Alpha.Pc.v481, CFSG.KD.Fi24Alpha.Pc.v482, CFSG.KD.Fi24Alpha.Pc.v483, CFSG.KD.Fi24Alpha.Pc.v484]
theorem CFSG.KD.Fi24Alpha.Pc.p483 : Nat.beq (runC AR SD 479 (ckL CFSG.KD.Fi24Alpha.Pc.l485) 2 483 CFSG.KD.Fi24Alpha.Pc.l483) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v485 : Nat := CFSG.KD.Fi24Alpha.KV3 117
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v486 : Nat := CFSG.KD.Fi24Alpha.KV3 118
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l487 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v479, CFSG.KD.Fi24Alpha.Pc.v480, CFSG.KD.Fi24Alpha.Pc.v481, CFSG.KD.Fi24Alpha.Pc.v482, CFSG.KD.Fi24Alpha.Pc.v483, CFSG.KD.Fi24Alpha.Pc.v484, CFSG.KD.Fi24Alpha.Pc.v485, CFSG.KD.Fi24Alpha.Pc.v486]
theorem CFSG.KD.Fi24Alpha.Pc.p485 : Nat.beq (runC AR SD 479 (ckL CFSG.KD.Fi24Alpha.Pc.l487) 2 485 CFSG.KD.Fi24Alpha.Pc.l485) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v487 : Nat := CFSG.KD.Fi24Alpha.KV3 119
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v488 : Nat := CFSG.KD.Fi24Alpha.KV3 120
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l489 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v479, CFSG.KD.Fi24Alpha.Pc.v480, CFSG.KD.Fi24Alpha.Pc.v481, CFSG.KD.Fi24Alpha.Pc.v482, CFSG.KD.Fi24Alpha.Pc.v483, CFSG.KD.Fi24Alpha.Pc.v484, CFSG.KD.Fi24Alpha.Pc.v485, CFSG.KD.Fi24Alpha.Pc.v486, CFSG.KD.Fi24Alpha.Pc.v487, CFSG.KD.Fi24Alpha.Pc.v488]
theorem CFSG.KD.Fi24Alpha.Pc.p487 : Nat.beq (runC AR SD 479 (ckL CFSG.KD.Fi24Alpha.Pc.l489) 2 487 CFSG.KD.Fi24Alpha.Pc.l487) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v489 : Nat := CFSG.KD.Fi24Alpha.KV3 121
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v490 : Nat := CFSG.KD.Fi24Alpha.KV3 122
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l491 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v479, CFSG.KD.Fi24Alpha.Pc.v480, CFSG.KD.Fi24Alpha.Pc.v481, CFSG.KD.Fi24Alpha.Pc.v482, CFSG.KD.Fi24Alpha.Pc.v483, CFSG.KD.Fi24Alpha.Pc.v484, CFSG.KD.Fi24Alpha.Pc.v485, CFSG.KD.Fi24Alpha.Pc.v486, CFSG.KD.Fi24Alpha.Pc.v487, CFSG.KD.Fi24Alpha.Pc.v488, CFSG.KD.Fi24Alpha.Pc.v489, CFSG.KD.Fi24Alpha.Pc.v490]
theorem CFSG.KD.Fi24Alpha.Pc.p489 : Nat.beq (runC AR SD 479 (ckL CFSG.KD.Fi24Alpha.Pc.l491) 2 489 CFSG.KD.Fi24Alpha.Pc.l489) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v491 : Nat := CFSG.KD.Fi24Alpha.KV3 123
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v492 : Nat := CFSG.KD.Fi24Alpha.KV3 124
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l493 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v479, CFSG.KD.Fi24Alpha.Pc.v480, CFSG.KD.Fi24Alpha.Pc.v481, CFSG.KD.Fi24Alpha.Pc.v482, CFSG.KD.Fi24Alpha.Pc.v483, CFSG.KD.Fi24Alpha.Pc.v484, CFSG.KD.Fi24Alpha.Pc.v485, CFSG.KD.Fi24Alpha.Pc.v486, CFSG.KD.Fi24Alpha.Pc.v487, CFSG.KD.Fi24Alpha.Pc.v488, CFSG.KD.Fi24Alpha.Pc.v489, CFSG.KD.Fi24Alpha.Pc.v490, CFSG.KD.Fi24Alpha.Pc.v491, CFSG.KD.Fi24Alpha.Pc.v492]
theorem CFSG.KD.Fi24Alpha.Pc.p491 : Nat.beq (runC AR SD 479 (ckL CFSG.KD.Fi24Alpha.Pc.l493) 2 491 CFSG.KD.Fi24Alpha.Pc.l491) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v493 : Nat := CFSG.KD.Fi24Alpha.KV3 125
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v494 : Nat := CFSG.KD.Fi24Alpha.KV3 126
theorem CFSG.KD.Fi24Alpha.Pc.f37 : Nat.beq (runC AR SD 479 (finC AR SD (nat_lit 37) 479 495) 2 493 CFSG.KD.Fi24Alpha.Pc.l493) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk37 : chk (nat_lit 37) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 37) (lo := 479) (hi := 495) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 481) CFSG.KD.Fi24Alpha.Pc.p479 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 483) CFSG.KD.Fi24Alpha.Pc.p481 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 485) CFSG.KD.Fi24Alpha.Pc.p483 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 487) CFSG.KD.Fi24Alpha.Pc.p485 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 489) CFSG.KD.Fi24Alpha.Pc.p487 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 491) CFSG.KD.Fi24Alpha.Pc.p489 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 493) CFSG.KD.Fi24Alpha.Pc.p491 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f37

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v495 : Nat := CFSG.KD.Fi24Alpha.KV3 127
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v496 : Nat := CFSG.KD.Fi24Alpha.KV3 128
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l497 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v495, CFSG.KD.Fi24Alpha.Pc.v496]
theorem CFSG.KD.Fi24Alpha.Pc.p495 : Nat.beq (runC AR SD 495 (ckL CFSG.KD.Fi24Alpha.Pc.l497) 2 495 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v497 : Nat := CFSG.KD.Fi24Alpha.KV3 129
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v498 : Nat := CFSG.KD.Fi24Alpha.KV3 130
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l499 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v495, CFSG.KD.Fi24Alpha.Pc.v496, CFSG.KD.Fi24Alpha.Pc.v497, CFSG.KD.Fi24Alpha.Pc.v498]
theorem CFSG.KD.Fi24Alpha.Pc.p497 : Nat.beq (runC AR SD 495 (ckL CFSG.KD.Fi24Alpha.Pc.l499) 2 497 CFSG.KD.Fi24Alpha.Pc.l497) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v499 : Nat := CFSG.KD.Fi24Alpha.KV3 131
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v500 : Nat := CFSG.KD.Fi24Alpha.KV3 132
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l501 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v495, CFSG.KD.Fi24Alpha.Pc.v496, CFSG.KD.Fi24Alpha.Pc.v497, CFSG.KD.Fi24Alpha.Pc.v498, CFSG.KD.Fi24Alpha.Pc.v499, CFSG.KD.Fi24Alpha.Pc.v500]
theorem CFSG.KD.Fi24Alpha.Pc.p499 : Nat.beq (runC AR SD 495 (ckL CFSG.KD.Fi24Alpha.Pc.l501) 2 499 CFSG.KD.Fi24Alpha.Pc.l499) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v501 : Nat := CFSG.KD.Fi24Alpha.KV3 133
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v502 : Nat := CFSG.KD.Fi24Alpha.KV3 134
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l503 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v495, CFSG.KD.Fi24Alpha.Pc.v496, CFSG.KD.Fi24Alpha.Pc.v497, CFSG.KD.Fi24Alpha.Pc.v498, CFSG.KD.Fi24Alpha.Pc.v499, CFSG.KD.Fi24Alpha.Pc.v500, CFSG.KD.Fi24Alpha.Pc.v501, CFSG.KD.Fi24Alpha.Pc.v502]
theorem CFSG.KD.Fi24Alpha.Pc.p501 : Nat.beq (runC AR SD 495 (ckL CFSG.KD.Fi24Alpha.Pc.l503) 2 501 CFSG.KD.Fi24Alpha.Pc.l501) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v503 : Nat := CFSG.KD.Fi24Alpha.KV3 135
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v504 : Nat := CFSG.KD.Fi24Alpha.KV3 136
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l505 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v495, CFSG.KD.Fi24Alpha.Pc.v496, CFSG.KD.Fi24Alpha.Pc.v497, CFSG.KD.Fi24Alpha.Pc.v498, CFSG.KD.Fi24Alpha.Pc.v499, CFSG.KD.Fi24Alpha.Pc.v500, CFSG.KD.Fi24Alpha.Pc.v501, CFSG.KD.Fi24Alpha.Pc.v502, CFSG.KD.Fi24Alpha.Pc.v503, CFSG.KD.Fi24Alpha.Pc.v504]
theorem CFSG.KD.Fi24Alpha.Pc.p503 : Nat.beq (runC AR SD 495 (ckL CFSG.KD.Fi24Alpha.Pc.l505) 2 503 CFSG.KD.Fi24Alpha.Pc.l503) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v505 : Nat := CFSG.KD.Fi24Alpha.KV3 137
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v506 : Nat := CFSG.KD.Fi24Alpha.KV3 138
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l507 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v495, CFSG.KD.Fi24Alpha.Pc.v496, CFSG.KD.Fi24Alpha.Pc.v497, CFSG.KD.Fi24Alpha.Pc.v498, CFSG.KD.Fi24Alpha.Pc.v499, CFSG.KD.Fi24Alpha.Pc.v500, CFSG.KD.Fi24Alpha.Pc.v501, CFSG.KD.Fi24Alpha.Pc.v502, CFSG.KD.Fi24Alpha.Pc.v503, CFSG.KD.Fi24Alpha.Pc.v504, CFSG.KD.Fi24Alpha.Pc.v505, CFSG.KD.Fi24Alpha.Pc.v506]
theorem CFSG.KD.Fi24Alpha.Pc.p505 : Nat.beq (runC AR SD 495 (ckL CFSG.KD.Fi24Alpha.Pc.l507) 2 505 CFSG.KD.Fi24Alpha.Pc.l505) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v507 : Nat := CFSG.KD.Fi24Alpha.KV3 139
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v508 : Nat := CFSG.KD.Fi24Alpha.KV3 140
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l509 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v495, CFSG.KD.Fi24Alpha.Pc.v496, CFSG.KD.Fi24Alpha.Pc.v497, CFSG.KD.Fi24Alpha.Pc.v498, CFSG.KD.Fi24Alpha.Pc.v499, CFSG.KD.Fi24Alpha.Pc.v500, CFSG.KD.Fi24Alpha.Pc.v501, CFSG.KD.Fi24Alpha.Pc.v502, CFSG.KD.Fi24Alpha.Pc.v503, CFSG.KD.Fi24Alpha.Pc.v504, CFSG.KD.Fi24Alpha.Pc.v505, CFSG.KD.Fi24Alpha.Pc.v506, CFSG.KD.Fi24Alpha.Pc.v507, CFSG.KD.Fi24Alpha.Pc.v508]
theorem CFSG.KD.Fi24Alpha.Pc.p507 : Nat.beq (runC AR SD 495 (ckL CFSG.KD.Fi24Alpha.Pc.l509) 2 507 CFSG.KD.Fi24Alpha.Pc.l507) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v509 : Nat := CFSG.KD.Fi24Alpha.KV3 141
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v510 : Nat := CFSG.KD.Fi24Alpha.KV3 142
theorem CFSG.KD.Fi24Alpha.Pc.f38 : Nat.beq (runC AR SD 495 (finC AR SD (nat_lit 38) 495 511) 2 509 CFSG.KD.Fi24Alpha.Pc.l509) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk38 : chk (nat_lit 38) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 38) (lo := 495) (hi := 511) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 497) CFSG.KD.Fi24Alpha.Pc.p495 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 499) CFSG.KD.Fi24Alpha.Pc.p497 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 501) CFSG.KD.Fi24Alpha.Pc.p499 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 503) CFSG.KD.Fi24Alpha.Pc.p501 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 505) CFSG.KD.Fi24Alpha.Pc.p503 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 507) CFSG.KD.Fi24Alpha.Pc.p505 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 509) CFSG.KD.Fi24Alpha.Pc.p507 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f38

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v511 : Nat := CFSG.KD.Fi24Alpha.KV3 143
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v512 : Nat := CFSG.KD.Fi24Alpha.KV3 144
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l513 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v511, CFSG.KD.Fi24Alpha.Pc.v512]
theorem CFSG.KD.Fi24Alpha.Pc.p511 : Nat.beq (runC AR SD 511 (ckL CFSG.KD.Fi24Alpha.Pc.l513) 2 511 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v513 : Nat := CFSG.KD.Fi24Alpha.KV3 145
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v514 : Nat := CFSG.KD.Fi24Alpha.KV3 146
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l515 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v511, CFSG.KD.Fi24Alpha.Pc.v512, CFSG.KD.Fi24Alpha.Pc.v513, CFSG.KD.Fi24Alpha.Pc.v514]
theorem CFSG.KD.Fi24Alpha.Pc.p513 : Nat.beq (runC AR SD 511 (ckL CFSG.KD.Fi24Alpha.Pc.l515) 2 513 CFSG.KD.Fi24Alpha.Pc.l513) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v515 : Nat := CFSG.KD.Fi24Alpha.KV3 147
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v516 : Nat := CFSG.KD.Fi24Alpha.KV3 148
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l517 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v511, CFSG.KD.Fi24Alpha.Pc.v512, CFSG.KD.Fi24Alpha.Pc.v513, CFSG.KD.Fi24Alpha.Pc.v514, CFSG.KD.Fi24Alpha.Pc.v515, CFSG.KD.Fi24Alpha.Pc.v516]
theorem CFSG.KD.Fi24Alpha.Pc.p515 : Nat.beq (runC AR SD 511 (ckL CFSG.KD.Fi24Alpha.Pc.l517) 2 515 CFSG.KD.Fi24Alpha.Pc.l515) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v517 : Nat := CFSG.KD.Fi24Alpha.KV3 149
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v518 : Nat := CFSG.KD.Fi24Alpha.KV3 150
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l519 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v511, CFSG.KD.Fi24Alpha.Pc.v512, CFSG.KD.Fi24Alpha.Pc.v513, CFSG.KD.Fi24Alpha.Pc.v514, CFSG.KD.Fi24Alpha.Pc.v515, CFSG.KD.Fi24Alpha.Pc.v516, CFSG.KD.Fi24Alpha.Pc.v517, CFSG.KD.Fi24Alpha.Pc.v518]
theorem CFSG.KD.Fi24Alpha.Pc.p517 : Nat.beq (runC AR SD 511 (ckL CFSG.KD.Fi24Alpha.Pc.l519) 2 517 CFSG.KD.Fi24Alpha.Pc.l517) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v519 : Nat := CFSG.KD.Fi24Alpha.KV3 151
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v520 : Nat := CFSG.KD.Fi24Alpha.KV3 152
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l521 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v511, CFSG.KD.Fi24Alpha.Pc.v512, CFSG.KD.Fi24Alpha.Pc.v513, CFSG.KD.Fi24Alpha.Pc.v514, CFSG.KD.Fi24Alpha.Pc.v515, CFSG.KD.Fi24Alpha.Pc.v516, CFSG.KD.Fi24Alpha.Pc.v517, CFSG.KD.Fi24Alpha.Pc.v518, CFSG.KD.Fi24Alpha.Pc.v519, CFSG.KD.Fi24Alpha.Pc.v520]
theorem CFSG.KD.Fi24Alpha.Pc.p519 : Nat.beq (runC AR SD 511 (ckL CFSG.KD.Fi24Alpha.Pc.l521) 2 519 CFSG.KD.Fi24Alpha.Pc.l519) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v521 : Nat := CFSG.KD.Fi24Alpha.KV3 153
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v522 : Nat := CFSG.KD.Fi24Alpha.KV3 154
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l523 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v511, CFSG.KD.Fi24Alpha.Pc.v512, CFSG.KD.Fi24Alpha.Pc.v513, CFSG.KD.Fi24Alpha.Pc.v514, CFSG.KD.Fi24Alpha.Pc.v515, CFSG.KD.Fi24Alpha.Pc.v516, CFSG.KD.Fi24Alpha.Pc.v517, CFSG.KD.Fi24Alpha.Pc.v518, CFSG.KD.Fi24Alpha.Pc.v519, CFSG.KD.Fi24Alpha.Pc.v520, CFSG.KD.Fi24Alpha.Pc.v521, CFSG.KD.Fi24Alpha.Pc.v522]
theorem CFSG.KD.Fi24Alpha.Pc.p521 : Nat.beq (runC AR SD 511 (ckL CFSG.KD.Fi24Alpha.Pc.l523) 2 521 CFSG.KD.Fi24Alpha.Pc.l521) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v523 : Nat := CFSG.KD.Fi24Alpha.KV3 155
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v524 : Nat := CFSG.KD.Fi24Alpha.KV3 156
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l525 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v511, CFSG.KD.Fi24Alpha.Pc.v512, CFSG.KD.Fi24Alpha.Pc.v513, CFSG.KD.Fi24Alpha.Pc.v514, CFSG.KD.Fi24Alpha.Pc.v515, CFSG.KD.Fi24Alpha.Pc.v516, CFSG.KD.Fi24Alpha.Pc.v517, CFSG.KD.Fi24Alpha.Pc.v518, CFSG.KD.Fi24Alpha.Pc.v519, CFSG.KD.Fi24Alpha.Pc.v520, CFSG.KD.Fi24Alpha.Pc.v521, CFSG.KD.Fi24Alpha.Pc.v522, CFSG.KD.Fi24Alpha.Pc.v523, CFSG.KD.Fi24Alpha.Pc.v524]
theorem CFSG.KD.Fi24Alpha.Pc.p523 : Nat.beq (runC AR SD 511 (ckL CFSG.KD.Fi24Alpha.Pc.l525) 2 523 CFSG.KD.Fi24Alpha.Pc.l523) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v525 : Nat := CFSG.KD.Fi24Alpha.KV3 157
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v526 : Nat := CFSG.KD.Fi24Alpha.KV3 158
theorem CFSG.KD.Fi24Alpha.Pc.f39 : Nat.beq (runC AR SD 511 (finC AR SD (nat_lit 39) 511 527) 2 525 CFSG.KD.Fi24Alpha.Pc.l525) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk39 : chk (nat_lit 39) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 39) (lo := 511) (hi := 527) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 513) CFSG.KD.Fi24Alpha.Pc.p511 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 515) CFSG.KD.Fi24Alpha.Pc.p513 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 517) CFSG.KD.Fi24Alpha.Pc.p515 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 519) CFSG.KD.Fi24Alpha.Pc.p517 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 521) CFSG.KD.Fi24Alpha.Pc.p519 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 523) CFSG.KD.Fi24Alpha.Pc.p521 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 525) CFSG.KD.Fi24Alpha.Pc.p523 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f39

end
