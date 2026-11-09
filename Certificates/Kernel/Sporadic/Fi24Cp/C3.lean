module

public import Certificates.Kernel.Sporadic.Fi24Cp.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Cp KV3 "Certificates/Kernel/Sporadic/Fi24Cp/data/v3.bin" 152491 4 21806213 18338992489793777628

public section

open CFSG.KD.Fi24Cp CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v383 : Nat := CFSG.KD.Fi24Cp.KV3 0
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v384 : Nat := CFSG.KD.Fi24Cp.KV3 1
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l385 : List Nat := [CFSG.KD.Fi24Cp.Pc.v383, CFSG.KD.Fi24Cp.Pc.v384]
theorem CFSG.KD.Fi24Cp.Pc.p383 : Nat.beq (runC AR SD 383 (ckL CFSG.KD.Fi24Cp.Pc.l385) 2 383 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v385 : Nat := CFSG.KD.Fi24Cp.KV3 2
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v386 : Nat := CFSG.KD.Fi24Cp.KV3 3
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l387 : List Nat := [CFSG.KD.Fi24Cp.Pc.v383, CFSG.KD.Fi24Cp.Pc.v384, CFSG.KD.Fi24Cp.Pc.v385, CFSG.KD.Fi24Cp.Pc.v386]
theorem CFSG.KD.Fi24Cp.Pc.p385 : Nat.beq (runC AR SD 383 (ckL CFSG.KD.Fi24Cp.Pc.l387) 2 385 CFSG.KD.Fi24Cp.Pc.l385) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v387 : Nat := CFSG.KD.Fi24Cp.KV3 4
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v388 : Nat := CFSG.KD.Fi24Cp.KV3 5
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l389 : List Nat := [CFSG.KD.Fi24Cp.Pc.v383, CFSG.KD.Fi24Cp.Pc.v384, CFSG.KD.Fi24Cp.Pc.v385, CFSG.KD.Fi24Cp.Pc.v386, CFSG.KD.Fi24Cp.Pc.v387, CFSG.KD.Fi24Cp.Pc.v388]
theorem CFSG.KD.Fi24Cp.Pc.p387 : Nat.beq (runC AR SD 383 (ckL CFSG.KD.Fi24Cp.Pc.l389) 2 387 CFSG.KD.Fi24Cp.Pc.l387) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v389 : Nat := CFSG.KD.Fi24Cp.KV3 6
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v390 : Nat := CFSG.KD.Fi24Cp.KV3 7
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l391 : List Nat := [CFSG.KD.Fi24Cp.Pc.v383, CFSG.KD.Fi24Cp.Pc.v384, CFSG.KD.Fi24Cp.Pc.v385, CFSG.KD.Fi24Cp.Pc.v386, CFSG.KD.Fi24Cp.Pc.v387, CFSG.KD.Fi24Cp.Pc.v388, CFSG.KD.Fi24Cp.Pc.v389, CFSG.KD.Fi24Cp.Pc.v390]
theorem CFSG.KD.Fi24Cp.Pc.p389 : Nat.beq (runC AR SD 383 (ckL CFSG.KD.Fi24Cp.Pc.l391) 2 389 CFSG.KD.Fi24Cp.Pc.l389) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v391 : Nat := CFSG.KD.Fi24Cp.KV3 8
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v392 : Nat := CFSG.KD.Fi24Cp.KV3 9
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l393 : List Nat := [CFSG.KD.Fi24Cp.Pc.v383, CFSG.KD.Fi24Cp.Pc.v384, CFSG.KD.Fi24Cp.Pc.v385, CFSG.KD.Fi24Cp.Pc.v386, CFSG.KD.Fi24Cp.Pc.v387, CFSG.KD.Fi24Cp.Pc.v388, CFSG.KD.Fi24Cp.Pc.v389, CFSG.KD.Fi24Cp.Pc.v390, CFSG.KD.Fi24Cp.Pc.v391, CFSG.KD.Fi24Cp.Pc.v392]
theorem CFSG.KD.Fi24Cp.Pc.p391 : Nat.beq (runC AR SD 383 (ckL CFSG.KD.Fi24Cp.Pc.l393) 2 391 CFSG.KD.Fi24Cp.Pc.l391) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v393 : Nat := CFSG.KD.Fi24Cp.KV3 10
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v394 : Nat := CFSG.KD.Fi24Cp.KV3 11
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l395 : List Nat := [CFSG.KD.Fi24Cp.Pc.v383, CFSG.KD.Fi24Cp.Pc.v384, CFSG.KD.Fi24Cp.Pc.v385, CFSG.KD.Fi24Cp.Pc.v386, CFSG.KD.Fi24Cp.Pc.v387, CFSG.KD.Fi24Cp.Pc.v388, CFSG.KD.Fi24Cp.Pc.v389, CFSG.KD.Fi24Cp.Pc.v390, CFSG.KD.Fi24Cp.Pc.v391, CFSG.KD.Fi24Cp.Pc.v392, CFSG.KD.Fi24Cp.Pc.v393, CFSG.KD.Fi24Cp.Pc.v394]
theorem CFSG.KD.Fi24Cp.Pc.p393 : Nat.beq (runC AR SD 383 (ckL CFSG.KD.Fi24Cp.Pc.l395) 2 393 CFSG.KD.Fi24Cp.Pc.l393) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v395 : Nat := CFSG.KD.Fi24Cp.KV3 12
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v396 : Nat := CFSG.KD.Fi24Cp.KV3 13
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l397 : List Nat := [CFSG.KD.Fi24Cp.Pc.v383, CFSG.KD.Fi24Cp.Pc.v384, CFSG.KD.Fi24Cp.Pc.v385, CFSG.KD.Fi24Cp.Pc.v386, CFSG.KD.Fi24Cp.Pc.v387, CFSG.KD.Fi24Cp.Pc.v388, CFSG.KD.Fi24Cp.Pc.v389, CFSG.KD.Fi24Cp.Pc.v390, CFSG.KD.Fi24Cp.Pc.v391, CFSG.KD.Fi24Cp.Pc.v392, CFSG.KD.Fi24Cp.Pc.v393, CFSG.KD.Fi24Cp.Pc.v394, CFSG.KD.Fi24Cp.Pc.v395, CFSG.KD.Fi24Cp.Pc.v396]
theorem CFSG.KD.Fi24Cp.Pc.p395 : Nat.beq (runC AR SD 383 (ckL CFSG.KD.Fi24Cp.Pc.l397) 2 395 CFSG.KD.Fi24Cp.Pc.l395) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v397 : Nat := CFSG.KD.Fi24Cp.KV3 14
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v398 : Nat := CFSG.KD.Fi24Cp.KV3 15
theorem CFSG.KD.Fi24Cp.Pc.f30 : Nat.beq (runC AR SD 383 (finC AR SD (nat_lit 30) 383 399) 2 397 CFSG.KD.Fi24Cp.Pc.l397) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk30 : chk (nat_lit 30) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 30) (lo := 383) (hi := 399) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 385) CFSG.KD.Fi24Cp.Pc.p383 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 387) CFSG.KD.Fi24Cp.Pc.p385 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 389) CFSG.KD.Fi24Cp.Pc.p387 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 391) CFSG.KD.Fi24Cp.Pc.p389 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 393) CFSG.KD.Fi24Cp.Pc.p391 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 395) CFSG.KD.Fi24Cp.Pc.p393 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 397) CFSG.KD.Fi24Cp.Pc.p395 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f30

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v399 : Nat := CFSG.KD.Fi24Cp.KV3 16
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v400 : Nat := CFSG.KD.Fi24Cp.KV3 17
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l401 : List Nat := [CFSG.KD.Fi24Cp.Pc.v399, CFSG.KD.Fi24Cp.Pc.v400]
theorem CFSG.KD.Fi24Cp.Pc.p399 : Nat.beq (runC AR SD 399 (ckL CFSG.KD.Fi24Cp.Pc.l401) 2 399 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v401 : Nat := CFSG.KD.Fi24Cp.KV3 18
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v402 : Nat := CFSG.KD.Fi24Cp.KV3 19
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l403 : List Nat := [CFSG.KD.Fi24Cp.Pc.v399, CFSG.KD.Fi24Cp.Pc.v400, CFSG.KD.Fi24Cp.Pc.v401, CFSG.KD.Fi24Cp.Pc.v402]
theorem CFSG.KD.Fi24Cp.Pc.p401 : Nat.beq (runC AR SD 399 (ckL CFSG.KD.Fi24Cp.Pc.l403) 2 401 CFSG.KD.Fi24Cp.Pc.l401) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v403 : Nat := CFSG.KD.Fi24Cp.KV3 20
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v404 : Nat := CFSG.KD.Fi24Cp.KV3 21
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l405 : List Nat := [CFSG.KD.Fi24Cp.Pc.v399, CFSG.KD.Fi24Cp.Pc.v400, CFSG.KD.Fi24Cp.Pc.v401, CFSG.KD.Fi24Cp.Pc.v402, CFSG.KD.Fi24Cp.Pc.v403, CFSG.KD.Fi24Cp.Pc.v404]
theorem CFSG.KD.Fi24Cp.Pc.p403 : Nat.beq (runC AR SD 399 (ckL CFSG.KD.Fi24Cp.Pc.l405) 2 403 CFSG.KD.Fi24Cp.Pc.l403) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v405 : Nat := CFSG.KD.Fi24Cp.KV3 22
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l406 : List Nat := [CFSG.KD.Fi24Cp.Pc.v399, CFSG.KD.Fi24Cp.Pc.v400, CFSG.KD.Fi24Cp.Pc.v401, CFSG.KD.Fi24Cp.Pc.v402, CFSG.KD.Fi24Cp.Pc.v403, CFSG.KD.Fi24Cp.Pc.v404, CFSG.KD.Fi24Cp.Pc.v405]
theorem CFSG.KD.Fi24Cp.Pc.p405 : Nat.beq (runC AR SD 399 (ckL CFSG.KD.Fi24Cp.Pc.l406) 1 405 CFSG.KD.Fi24Cp.Pc.l405) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v406 : Nat := CFSG.KD.Fi24Cp.KV3 23
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l407 : List Nat := [CFSG.KD.Fi24Cp.Pc.v399, CFSG.KD.Fi24Cp.Pc.v400, CFSG.KD.Fi24Cp.Pc.v401, CFSG.KD.Fi24Cp.Pc.v402, CFSG.KD.Fi24Cp.Pc.v403, CFSG.KD.Fi24Cp.Pc.v404, CFSG.KD.Fi24Cp.Pc.v405, CFSG.KD.Fi24Cp.Pc.v406]
theorem CFSG.KD.Fi24Cp.Pc.p406 : Nat.beq (runC AR SD 399 (ckL CFSG.KD.Fi24Cp.Pc.l407) 1 406 CFSG.KD.Fi24Cp.Pc.l406) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v407 : Nat := CFSG.KD.Fi24Cp.KV3 24
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v408 : Nat := CFSG.KD.Fi24Cp.KV3 25
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l409 : List Nat := [CFSG.KD.Fi24Cp.Pc.v399, CFSG.KD.Fi24Cp.Pc.v400, CFSG.KD.Fi24Cp.Pc.v401, CFSG.KD.Fi24Cp.Pc.v402, CFSG.KD.Fi24Cp.Pc.v403, CFSG.KD.Fi24Cp.Pc.v404, CFSG.KD.Fi24Cp.Pc.v405, CFSG.KD.Fi24Cp.Pc.v406, CFSG.KD.Fi24Cp.Pc.v407, CFSG.KD.Fi24Cp.Pc.v408]
theorem CFSG.KD.Fi24Cp.Pc.p407 : Nat.beq (runC AR SD 399 (ckL CFSG.KD.Fi24Cp.Pc.l409) 2 407 CFSG.KD.Fi24Cp.Pc.l407) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v409 : Nat := CFSG.KD.Fi24Cp.KV3 26
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v410 : Nat := CFSG.KD.Fi24Cp.KV3 27
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l411 : List Nat := [CFSG.KD.Fi24Cp.Pc.v399, CFSG.KD.Fi24Cp.Pc.v400, CFSG.KD.Fi24Cp.Pc.v401, CFSG.KD.Fi24Cp.Pc.v402, CFSG.KD.Fi24Cp.Pc.v403, CFSG.KD.Fi24Cp.Pc.v404, CFSG.KD.Fi24Cp.Pc.v405, CFSG.KD.Fi24Cp.Pc.v406, CFSG.KD.Fi24Cp.Pc.v407, CFSG.KD.Fi24Cp.Pc.v408, CFSG.KD.Fi24Cp.Pc.v409, CFSG.KD.Fi24Cp.Pc.v410]
theorem CFSG.KD.Fi24Cp.Pc.p409 : Nat.beq (runC AR SD 399 (ckL CFSG.KD.Fi24Cp.Pc.l411) 2 409 CFSG.KD.Fi24Cp.Pc.l409) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v411 : Nat := CFSG.KD.Fi24Cp.KV3 28
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v412 : Nat := CFSG.KD.Fi24Cp.KV3 29
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l413 : List Nat := [CFSG.KD.Fi24Cp.Pc.v399, CFSG.KD.Fi24Cp.Pc.v400, CFSG.KD.Fi24Cp.Pc.v401, CFSG.KD.Fi24Cp.Pc.v402, CFSG.KD.Fi24Cp.Pc.v403, CFSG.KD.Fi24Cp.Pc.v404, CFSG.KD.Fi24Cp.Pc.v405, CFSG.KD.Fi24Cp.Pc.v406, CFSG.KD.Fi24Cp.Pc.v407, CFSG.KD.Fi24Cp.Pc.v408, CFSG.KD.Fi24Cp.Pc.v409, CFSG.KD.Fi24Cp.Pc.v410, CFSG.KD.Fi24Cp.Pc.v411, CFSG.KD.Fi24Cp.Pc.v412]
theorem CFSG.KD.Fi24Cp.Pc.p411 : Nat.beq (runC AR SD 399 (ckL CFSG.KD.Fi24Cp.Pc.l413) 2 411 CFSG.KD.Fi24Cp.Pc.l411) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v413 : Nat := CFSG.KD.Fi24Cp.KV3 30
theorem CFSG.KD.Fi24Cp.Pc.f31 : Nat.beq (runC AR SD 399 (finC AR SD (nat_lit 31) 399 414) 1 413 CFSG.KD.Fi24Cp.Pc.l413) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk31 : chk (nat_lit 31) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 31) (lo := 399) (hi := 414) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 401) CFSG.KD.Fi24Cp.Pc.p399 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 403) CFSG.KD.Fi24Cp.Pc.p401 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 405) CFSG.KD.Fi24Cp.Pc.p403 rfl rfl).trans ((runC_seq (m := 9) (m2 := 8) (j2 := 406) CFSG.KD.Fi24Cp.Pc.p405 rfl rfl).trans ((runC_seq (m := 8) (m2 := 7) (j2 := 407) CFSG.KD.Fi24Cp.Pc.p406 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 409) CFSG.KD.Fi24Cp.Pc.p407 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 411) CFSG.KD.Fi24Cp.Pc.p409 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 413) CFSG.KD.Fi24Cp.Pc.p411 rfl rfl)))))))))).trans CFSG.KD.Fi24Cp.Pc.f31

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v414 : Nat := CFSG.KD.Fi24Cp.KV3 31
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v415 : Nat := CFSG.KD.Fi24Cp.KV3 32
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l416 : List Nat := [CFSG.KD.Fi24Cp.Pc.v414, CFSG.KD.Fi24Cp.Pc.v415]
theorem CFSG.KD.Fi24Cp.Pc.p414 : Nat.beq (runC AR SD 414 (ckL CFSG.KD.Fi24Cp.Pc.l416) 2 414 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v416 : Nat := CFSG.KD.Fi24Cp.KV3 33
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v417 : Nat := CFSG.KD.Fi24Cp.KV3 34
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l418 : List Nat := [CFSG.KD.Fi24Cp.Pc.v414, CFSG.KD.Fi24Cp.Pc.v415, CFSG.KD.Fi24Cp.Pc.v416, CFSG.KD.Fi24Cp.Pc.v417]
theorem CFSG.KD.Fi24Cp.Pc.p416 : Nat.beq (runC AR SD 414 (ckL CFSG.KD.Fi24Cp.Pc.l418) 2 416 CFSG.KD.Fi24Cp.Pc.l416) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v418 : Nat := CFSG.KD.Fi24Cp.KV3 35
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v419 : Nat := CFSG.KD.Fi24Cp.KV3 36
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l420 : List Nat := [CFSG.KD.Fi24Cp.Pc.v414, CFSG.KD.Fi24Cp.Pc.v415, CFSG.KD.Fi24Cp.Pc.v416, CFSG.KD.Fi24Cp.Pc.v417, CFSG.KD.Fi24Cp.Pc.v418, CFSG.KD.Fi24Cp.Pc.v419]
theorem CFSG.KD.Fi24Cp.Pc.p418 : Nat.beq (runC AR SD 414 (ckL CFSG.KD.Fi24Cp.Pc.l420) 2 418 CFSG.KD.Fi24Cp.Pc.l418) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v420 : Nat := CFSG.KD.Fi24Cp.KV3 37
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v421 : Nat := CFSG.KD.Fi24Cp.KV3 38
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l422 : List Nat := [CFSG.KD.Fi24Cp.Pc.v414, CFSG.KD.Fi24Cp.Pc.v415, CFSG.KD.Fi24Cp.Pc.v416, CFSG.KD.Fi24Cp.Pc.v417, CFSG.KD.Fi24Cp.Pc.v418, CFSG.KD.Fi24Cp.Pc.v419, CFSG.KD.Fi24Cp.Pc.v420, CFSG.KD.Fi24Cp.Pc.v421]
theorem CFSG.KD.Fi24Cp.Pc.p420 : Nat.beq (runC AR SD 414 (ckL CFSG.KD.Fi24Cp.Pc.l422) 2 420 CFSG.KD.Fi24Cp.Pc.l420) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v422 : Nat := CFSG.KD.Fi24Cp.KV3 39
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v423 : Nat := CFSG.KD.Fi24Cp.KV3 40
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l424 : List Nat := [CFSG.KD.Fi24Cp.Pc.v414, CFSG.KD.Fi24Cp.Pc.v415, CFSG.KD.Fi24Cp.Pc.v416, CFSG.KD.Fi24Cp.Pc.v417, CFSG.KD.Fi24Cp.Pc.v418, CFSG.KD.Fi24Cp.Pc.v419, CFSG.KD.Fi24Cp.Pc.v420, CFSG.KD.Fi24Cp.Pc.v421, CFSG.KD.Fi24Cp.Pc.v422, CFSG.KD.Fi24Cp.Pc.v423]
theorem CFSG.KD.Fi24Cp.Pc.p422 : Nat.beq (runC AR SD 414 (ckL CFSG.KD.Fi24Cp.Pc.l424) 2 422 CFSG.KD.Fi24Cp.Pc.l422) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v424 : Nat := CFSG.KD.Fi24Cp.KV3 41
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v425 : Nat := CFSG.KD.Fi24Cp.KV3 42
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l426 : List Nat := [CFSG.KD.Fi24Cp.Pc.v414, CFSG.KD.Fi24Cp.Pc.v415, CFSG.KD.Fi24Cp.Pc.v416, CFSG.KD.Fi24Cp.Pc.v417, CFSG.KD.Fi24Cp.Pc.v418, CFSG.KD.Fi24Cp.Pc.v419, CFSG.KD.Fi24Cp.Pc.v420, CFSG.KD.Fi24Cp.Pc.v421, CFSG.KD.Fi24Cp.Pc.v422, CFSG.KD.Fi24Cp.Pc.v423, CFSG.KD.Fi24Cp.Pc.v424, CFSG.KD.Fi24Cp.Pc.v425]
theorem CFSG.KD.Fi24Cp.Pc.p424 : Nat.beq (runC AR SD 414 (ckL CFSG.KD.Fi24Cp.Pc.l426) 2 424 CFSG.KD.Fi24Cp.Pc.l424) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v426 : Nat := CFSG.KD.Fi24Cp.KV3 43
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v427 : Nat := CFSG.KD.Fi24Cp.KV3 44
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l428 : List Nat := [CFSG.KD.Fi24Cp.Pc.v414, CFSG.KD.Fi24Cp.Pc.v415, CFSG.KD.Fi24Cp.Pc.v416, CFSG.KD.Fi24Cp.Pc.v417, CFSG.KD.Fi24Cp.Pc.v418, CFSG.KD.Fi24Cp.Pc.v419, CFSG.KD.Fi24Cp.Pc.v420, CFSG.KD.Fi24Cp.Pc.v421, CFSG.KD.Fi24Cp.Pc.v422, CFSG.KD.Fi24Cp.Pc.v423, CFSG.KD.Fi24Cp.Pc.v424, CFSG.KD.Fi24Cp.Pc.v425, CFSG.KD.Fi24Cp.Pc.v426, CFSG.KD.Fi24Cp.Pc.v427]
theorem CFSG.KD.Fi24Cp.Pc.p426 : Nat.beq (runC AR SD 414 (ckL CFSG.KD.Fi24Cp.Pc.l428) 2 426 CFSG.KD.Fi24Cp.Pc.l426) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v428 : Nat := CFSG.KD.Fi24Cp.KV3 45
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v429 : Nat := CFSG.KD.Fi24Cp.KV3 46
theorem CFSG.KD.Fi24Cp.Pc.f32 : Nat.beq (runC AR SD 414 (finC AR SD (nat_lit 32) 414 430) 2 428 CFSG.KD.Fi24Cp.Pc.l428) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk32 : chk (nat_lit 32) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 32) (lo := 414) (hi := 430) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 416) CFSG.KD.Fi24Cp.Pc.p414 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 418) CFSG.KD.Fi24Cp.Pc.p416 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 420) CFSG.KD.Fi24Cp.Pc.p418 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 422) CFSG.KD.Fi24Cp.Pc.p420 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 424) CFSG.KD.Fi24Cp.Pc.p422 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 426) CFSG.KD.Fi24Cp.Pc.p424 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 428) CFSG.KD.Fi24Cp.Pc.p426 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f32

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v430 : Nat := CFSG.KD.Fi24Cp.KV3 47
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v431 : Nat := CFSG.KD.Fi24Cp.KV3 48
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l432 : List Nat := [CFSG.KD.Fi24Cp.Pc.v430, CFSG.KD.Fi24Cp.Pc.v431]
theorem CFSG.KD.Fi24Cp.Pc.p430 : Nat.beq (runC AR SD 430 (ckL CFSG.KD.Fi24Cp.Pc.l432) 2 430 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v432 : Nat := CFSG.KD.Fi24Cp.KV3 49
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v433 : Nat := CFSG.KD.Fi24Cp.KV3 50
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l434 : List Nat := [CFSG.KD.Fi24Cp.Pc.v430, CFSG.KD.Fi24Cp.Pc.v431, CFSG.KD.Fi24Cp.Pc.v432, CFSG.KD.Fi24Cp.Pc.v433]
theorem CFSG.KD.Fi24Cp.Pc.p432 : Nat.beq (runC AR SD 430 (ckL CFSG.KD.Fi24Cp.Pc.l434) 2 432 CFSG.KD.Fi24Cp.Pc.l432) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v434 : Nat := CFSG.KD.Fi24Cp.KV3 51
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v435 : Nat := CFSG.KD.Fi24Cp.KV3 52
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l436 : List Nat := [CFSG.KD.Fi24Cp.Pc.v430, CFSG.KD.Fi24Cp.Pc.v431, CFSG.KD.Fi24Cp.Pc.v432, CFSG.KD.Fi24Cp.Pc.v433, CFSG.KD.Fi24Cp.Pc.v434, CFSG.KD.Fi24Cp.Pc.v435]
theorem CFSG.KD.Fi24Cp.Pc.p434 : Nat.beq (runC AR SD 430 (ckL CFSG.KD.Fi24Cp.Pc.l436) 2 434 CFSG.KD.Fi24Cp.Pc.l434) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v436 : Nat := CFSG.KD.Fi24Cp.KV3 53
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v437 : Nat := CFSG.KD.Fi24Cp.KV3 54
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l438 : List Nat := [CFSG.KD.Fi24Cp.Pc.v430, CFSG.KD.Fi24Cp.Pc.v431, CFSG.KD.Fi24Cp.Pc.v432, CFSG.KD.Fi24Cp.Pc.v433, CFSG.KD.Fi24Cp.Pc.v434, CFSG.KD.Fi24Cp.Pc.v435, CFSG.KD.Fi24Cp.Pc.v436, CFSG.KD.Fi24Cp.Pc.v437]
theorem CFSG.KD.Fi24Cp.Pc.p436 : Nat.beq (runC AR SD 430 (ckL CFSG.KD.Fi24Cp.Pc.l438) 2 436 CFSG.KD.Fi24Cp.Pc.l436) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v438 : Nat := CFSG.KD.Fi24Cp.KV3 55
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v439 : Nat := CFSG.KD.Fi24Cp.KV3 56
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l440 : List Nat := [CFSG.KD.Fi24Cp.Pc.v430, CFSG.KD.Fi24Cp.Pc.v431, CFSG.KD.Fi24Cp.Pc.v432, CFSG.KD.Fi24Cp.Pc.v433, CFSG.KD.Fi24Cp.Pc.v434, CFSG.KD.Fi24Cp.Pc.v435, CFSG.KD.Fi24Cp.Pc.v436, CFSG.KD.Fi24Cp.Pc.v437, CFSG.KD.Fi24Cp.Pc.v438, CFSG.KD.Fi24Cp.Pc.v439]
theorem CFSG.KD.Fi24Cp.Pc.p438 : Nat.beq (runC AR SD 430 (ckL CFSG.KD.Fi24Cp.Pc.l440) 2 438 CFSG.KD.Fi24Cp.Pc.l438) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v440 : Nat := CFSG.KD.Fi24Cp.KV3 57
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v441 : Nat := CFSG.KD.Fi24Cp.KV3 58
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l442 : List Nat := [CFSG.KD.Fi24Cp.Pc.v430, CFSG.KD.Fi24Cp.Pc.v431, CFSG.KD.Fi24Cp.Pc.v432, CFSG.KD.Fi24Cp.Pc.v433, CFSG.KD.Fi24Cp.Pc.v434, CFSG.KD.Fi24Cp.Pc.v435, CFSG.KD.Fi24Cp.Pc.v436, CFSG.KD.Fi24Cp.Pc.v437, CFSG.KD.Fi24Cp.Pc.v438, CFSG.KD.Fi24Cp.Pc.v439, CFSG.KD.Fi24Cp.Pc.v440, CFSG.KD.Fi24Cp.Pc.v441]
theorem CFSG.KD.Fi24Cp.Pc.p440 : Nat.beq (runC AR SD 430 (ckL CFSG.KD.Fi24Cp.Pc.l442) 2 440 CFSG.KD.Fi24Cp.Pc.l440) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v442 : Nat := CFSG.KD.Fi24Cp.KV3 59
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v443 : Nat := CFSG.KD.Fi24Cp.KV3 60
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l444 : List Nat := [CFSG.KD.Fi24Cp.Pc.v430, CFSG.KD.Fi24Cp.Pc.v431, CFSG.KD.Fi24Cp.Pc.v432, CFSG.KD.Fi24Cp.Pc.v433, CFSG.KD.Fi24Cp.Pc.v434, CFSG.KD.Fi24Cp.Pc.v435, CFSG.KD.Fi24Cp.Pc.v436, CFSG.KD.Fi24Cp.Pc.v437, CFSG.KD.Fi24Cp.Pc.v438, CFSG.KD.Fi24Cp.Pc.v439, CFSG.KD.Fi24Cp.Pc.v440, CFSG.KD.Fi24Cp.Pc.v441, CFSG.KD.Fi24Cp.Pc.v442, CFSG.KD.Fi24Cp.Pc.v443]
theorem CFSG.KD.Fi24Cp.Pc.p442 : Nat.beq (runC AR SD 430 (ckL CFSG.KD.Fi24Cp.Pc.l444) 2 442 CFSG.KD.Fi24Cp.Pc.l442) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v444 : Nat := CFSG.KD.Fi24Cp.KV3 61
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v445 : Nat := CFSG.KD.Fi24Cp.KV3 62
theorem CFSG.KD.Fi24Cp.Pc.f33 : Nat.beq (runC AR SD 430 (finC AR SD (nat_lit 33) 430 446) 2 444 CFSG.KD.Fi24Cp.Pc.l444) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk33 : chk (nat_lit 33) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 33) (lo := 430) (hi := 446) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 432) CFSG.KD.Fi24Cp.Pc.p430 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 434) CFSG.KD.Fi24Cp.Pc.p432 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 436) CFSG.KD.Fi24Cp.Pc.p434 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 438) CFSG.KD.Fi24Cp.Pc.p436 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 440) CFSG.KD.Fi24Cp.Pc.p438 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 442) CFSG.KD.Fi24Cp.Pc.p440 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 444) CFSG.KD.Fi24Cp.Pc.p442 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f33

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v446 : Nat := CFSG.KD.Fi24Cp.KV3 63
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v447 : Nat := CFSG.KD.Fi24Cp.KV3 64
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l448 : List Nat := [CFSG.KD.Fi24Cp.Pc.v446, CFSG.KD.Fi24Cp.Pc.v447]
theorem CFSG.KD.Fi24Cp.Pc.p446 : Nat.beq (runC AR SD 446 (ckL CFSG.KD.Fi24Cp.Pc.l448) 2 446 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v448 : Nat := CFSG.KD.Fi24Cp.KV3 65
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v449 : Nat := CFSG.KD.Fi24Cp.KV3 66
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l450 : List Nat := [CFSG.KD.Fi24Cp.Pc.v446, CFSG.KD.Fi24Cp.Pc.v447, CFSG.KD.Fi24Cp.Pc.v448, CFSG.KD.Fi24Cp.Pc.v449]
theorem CFSG.KD.Fi24Cp.Pc.p448 : Nat.beq (runC AR SD 446 (ckL CFSG.KD.Fi24Cp.Pc.l450) 2 448 CFSG.KD.Fi24Cp.Pc.l448) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v450 : Nat := CFSG.KD.Fi24Cp.KV3 67
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v451 : Nat := CFSG.KD.Fi24Cp.KV3 68
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l452 : List Nat := [CFSG.KD.Fi24Cp.Pc.v446, CFSG.KD.Fi24Cp.Pc.v447, CFSG.KD.Fi24Cp.Pc.v448, CFSG.KD.Fi24Cp.Pc.v449, CFSG.KD.Fi24Cp.Pc.v450, CFSG.KD.Fi24Cp.Pc.v451]
theorem CFSG.KD.Fi24Cp.Pc.p450 : Nat.beq (runC AR SD 446 (ckL CFSG.KD.Fi24Cp.Pc.l452) 2 450 CFSG.KD.Fi24Cp.Pc.l450) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v452 : Nat := CFSG.KD.Fi24Cp.KV3 69
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v453 : Nat := CFSG.KD.Fi24Cp.KV3 70
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l454 : List Nat := [CFSG.KD.Fi24Cp.Pc.v446, CFSG.KD.Fi24Cp.Pc.v447, CFSG.KD.Fi24Cp.Pc.v448, CFSG.KD.Fi24Cp.Pc.v449, CFSG.KD.Fi24Cp.Pc.v450, CFSG.KD.Fi24Cp.Pc.v451, CFSG.KD.Fi24Cp.Pc.v452, CFSG.KD.Fi24Cp.Pc.v453]
theorem CFSG.KD.Fi24Cp.Pc.p452 : Nat.beq (runC AR SD 446 (ckL CFSG.KD.Fi24Cp.Pc.l454) 2 452 CFSG.KD.Fi24Cp.Pc.l452) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v454 : Nat := CFSG.KD.Fi24Cp.KV3 71
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v455 : Nat := CFSG.KD.Fi24Cp.KV3 72
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l456 : List Nat := [CFSG.KD.Fi24Cp.Pc.v446, CFSG.KD.Fi24Cp.Pc.v447, CFSG.KD.Fi24Cp.Pc.v448, CFSG.KD.Fi24Cp.Pc.v449, CFSG.KD.Fi24Cp.Pc.v450, CFSG.KD.Fi24Cp.Pc.v451, CFSG.KD.Fi24Cp.Pc.v452, CFSG.KD.Fi24Cp.Pc.v453, CFSG.KD.Fi24Cp.Pc.v454, CFSG.KD.Fi24Cp.Pc.v455]
theorem CFSG.KD.Fi24Cp.Pc.p454 : Nat.beq (runC AR SD 446 (ckL CFSG.KD.Fi24Cp.Pc.l456) 2 454 CFSG.KD.Fi24Cp.Pc.l454) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v456 : Nat := CFSG.KD.Fi24Cp.KV3 73
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v457 : Nat := CFSG.KD.Fi24Cp.KV3 74
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l458 : List Nat := [CFSG.KD.Fi24Cp.Pc.v446, CFSG.KD.Fi24Cp.Pc.v447, CFSG.KD.Fi24Cp.Pc.v448, CFSG.KD.Fi24Cp.Pc.v449, CFSG.KD.Fi24Cp.Pc.v450, CFSG.KD.Fi24Cp.Pc.v451, CFSG.KD.Fi24Cp.Pc.v452, CFSG.KD.Fi24Cp.Pc.v453, CFSG.KD.Fi24Cp.Pc.v454, CFSG.KD.Fi24Cp.Pc.v455, CFSG.KD.Fi24Cp.Pc.v456, CFSG.KD.Fi24Cp.Pc.v457]
theorem CFSG.KD.Fi24Cp.Pc.p456 : Nat.beq (runC AR SD 446 (ckL CFSG.KD.Fi24Cp.Pc.l458) 2 456 CFSG.KD.Fi24Cp.Pc.l456) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v458 : Nat := CFSG.KD.Fi24Cp.KV3 75
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v459 : Nat := CFSG.KD.Fi24Cp.KV3 76
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l460 : List Nat := [CFSG.KD.Fi24Cp.Pc.v446, CFSG.KD.Fi24Cp.Pc.v447, CFSG.KD.Fi24Cp.Pc.v448, CFSG.KD.Fi24Cp.Pc.v449, CFSG.KD.Fi24Cp.Pc.v450, CFSG.KD.Fi24Cp.Pc.v451, CFSG.KD.Fi24Cp.Pc.v452, CFSG.KD.Fi24Cp.Pc.v453, CFSG.KD.Fi24Cp.Pc.v454, CFSG.KD.Fi24Cp.Pc.v455, CFSG.KD.Fi24Cp.Pc.v456, CFSG.KD.Fi24Cp.Pc.v457, CFSG.KD.Fi24Cp.Pc.v458, CFSG.KD.Fi24Cp.Pc.v459]
theorem CFSG.KD.Fi24Cp.Pc.p458 : Nat.beq (runC AR SD 446 (ckL CFSG.KD.Fi24Cp.Pc.l460) 2 458 CFSG.KD.Fi24Cp.Pc.l458) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v460 : Nat := CFSG.KD.Fi24Cp.KV3 77
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v461 : Nat := CFSG.KD.Fi24Cp.KV3 78
theorem CFSG.KD.Fi24Cp.Pc.f34 : Nat.beq (runC AR SD 446 (finC AR SD (nat_lit 34) 446 462) 2 460 CFSG.KD.Fi24Cp.Pc.l460) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk34 : chk (nat_lit 34) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 34) (lo := 446) (hi := 462) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 448) CFSG.KD.Fi24Cp.Pc.p446 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 450) CFSG.KD.Fi24Cp.Pc.p448 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 452) CFSG.KD.Fi24Cp.Pc.p450 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 454) CFSG.KD.Fi24Cp.Pc.p452 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 456) CFSG.KD.Fi24Cp.Pc.p454 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 458) CFSG.KD.Fi24Cp.Pc.p456 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 460) CFSG.KD.Fi24Cp.Pc.p458 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f34

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v462 : Nat := CFSG.KD.Fi24Cp.KV3 79
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v463 : Nat := CFSG.KD.Fi24Cp.KV3 80
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l464 : List Nat := [CFSG.KD.Fi24Cp.Pc.v462, CFSG.KD.Fi24Cp.Pc.v463]
theorem CFSG.KD.Fi24Cp.Pc.p462 : Nat.beq (runC AR SD 462 (ckL CFSG.KD.Fi24Cp.Pc.l464) 2 462 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v464 : Nat := CFSG.KD.Fi24Cp.KV3 81
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v465 : Nat := CFSG.KD.Fi24Cp.KV3 82
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l466 : List Nat := [CFSG.KD.Fi24Cp.Pc.v462, CFSG.KD.Fi24Cp.Pc.v463, CFSG.KD.Fi24Cp.Pc.v464, CFSG.KD.Fi24Cp.Pc.v465]
theorem CFSG.KD.Fi24Cp.Pc.p464 : Nat.beq (runC AR SD 462 (ckL CFSG.KD.Fi24Cp.Pc.l466) 2 464 CFSG.KD.Fi24Cp.Pc.l464) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v466 : Nat := CFSG.KD.Fi24Cp.KV3 83
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v467 : Nat := CFSG.KD.Fi24Cp.KV3 84
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l468 : List Nat := [CFSG.KD.Fi24Cp.Pc.v462, CFSG.KD.Fi24Cp.Pc.v463, CFSG.KD.Fi24Cp.Pc.v464, CFSG.KD.Fi24Cp.Pc.v465, CFSG.KD.Fi24Cp.Pc.v466, CFSG.KD.Fi24Cp.Pc.v467]
theorem CFSG.KD.Fi24Cp.Pc.p466 : Nat.beq (runC AR SD 462 (ckL CFSG.KD.Fi24Cp.Pc.l468) 2 466 CFSG.KD.Fi24Cp.Pc.l466) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v468 : Nat := CFSG.KD.Fi24Cp.KV3 85
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v469 : Nat := CFSG.KD.Fi24Cp.KV3 86
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l470 : List Nat := [CFSG.KD.Fi24Cp.Pc.v462, CFSG.KD.Fi24Cp.Pc.v463, CFSG.KD.Fi24Cp.Pc.v464, CFSG.KD.Fi24Cp.Pc.v465, CFSG.KD.Fi24Cp.Pc.v466, CFSG.KD.Fi24Cp.Pc.v467, CFSG.KD.Fi24Cp.Pc.v468, CFSG.KD.Fi24Cp.Pc.v469]
theorem CFSG.KD.Fi24Cp.Pc.p468 : Nat.beq (runC AR SD 462 (ckL CFSG.KD.Fi24Cp.Pc.l470) 2 468 CFSG.KD.Fi24Cp.Pc.l468) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v470 : Nat := CFSG.KD.Fi24Cp.KV3 87
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v471 : Nat := CFSG.KD.Fi24Cp.KV3 88
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l472 : List Nat := [CFSG.KD.Fi24Cp.Pc.v462, CFSG.KD.Fi24Cp.Pc.v463, CFSG.KD.Fi24Cp.Pc.v464, CFSG.KD.Fi24Cp.Pc.v465, CFSG.KD.Fi24Cp.Pc.v466, CFSG.KD.Fi24Cp.Pc.v467, CFSG.KD.Fi24Cp.Pc.v468, CFSG.KD.Fi24Cp.Pc.v469, CFSG.KD.Fi24Cp.Pc.v470, CFSG.KD.Fi24Cp.Pc.v471]
theorem CFSG.KD.Fi24Cp.Pc.p470 : Nat.beq (runC AR SD 462 (ckL CFSG.KD.Fi24Cp.Pc.l472) 2 470 CFSG.KD.Fi24Cp.Pc.l470) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v472 : Nat := CFSG.KD.Fi24Cp.KV3 89
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v473 : Nat := CFSG.KD.Fi24Cp.KV3 90
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l474 : List Nat := [CFSG.KD.Fi24Cp.Pc.v462, CFSG.KD.Fi24Cp.Pc.v463, CFSG.KD.Fi24Cp.Pc.v464, CFSG.KD.Fi24Cp.Pc.v465, CFSG.KD.Fi24Cp.Pc.v466, CFSG.KD.Fi24Cp.Pc.v467, CFSG.KD.Fi24Cp.Pc.v468, CFSG.KD.Fi24Cp.Pc.v469, CFSG.KD.Fi24Cp.Pc.v470, CFSG.KD.Fi24Cp.Pc.v471, CFSG.KD.Fi24Cp.Pc.v472, CFSG.KD.Fi24Cp.Pc.v473]
theorem CFSG.KD.Fi24Cp.Pc.p472 : Nat.beq (runC AR SD 462 (ckL CFSG.KD.Fi24Cp.Pc.l474) 2 472 CFSG.KD.Fi24Cp.Pc.l472) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v474 : Nat := CFSG.KD.Fi24Cp.KV3 91
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v475 : Nat := CFSG.KD.Fi24Cp.KV3 92
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l476 : List Nat := [CFSG.KD.Fi24Cp.Pc.v462, CFSG.KD.Fi24Cp.Pc.v463, CFSG.KD.Fi24Cp.Pc.v464, CFSG.KD.Fi24Cp.Pc.v465, CFSG.KD.Fi24Cp.Pc.v466, CFSG.KD.Fi24Cp.Pc.v467, CFSG.KD.Fi24Cp.Pc.v468, CFSG.KD.Fi24Cp.Pc.v469, CFSG.KD.Fi24Cp.Pc.v470, CFSG.KD.Fi24Cp.Pc.v471, CFSG.KD.Fi24Cp.Pc.v472, CFSG.KD.Fi24Cp.Pc.v473, CFSG.KD.Fi24Cp.Pc.v474, CFSG.KD.Fi24Cp.Pc.v475]
theorem CFSG.KD.Fi24Cp.Pc.p474 : Nat.beq (runC AR SD 462 (ckL CFSG.KD.Fi24Cp.Pc.l476) 2 474 CFSG.KD.Fi24Cp.Pc.l474) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v476 : Nat := CFSG.KD.Fi24Cp.KV3 93
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v477 : Nat := CFSG.KD.Fi24Cp.KV3 94
theorem CFSG.KD.Fi24Cp.Pc.f35 : Nat.beq (runC AR SD 462 (finC AR SD (nat_lit 35) 462 478) 2 476 CFSG.KD.Fi24Cp.Pc.l476) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk35 : chk (nat_lit 35) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 35) (lo := 462) (hi := 478) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 464) CFSG.KD.Fi24Cp.Pc.p462 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 466) CFSG.KD.Fi24Cp.Pc.p464 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 468) CFSG.KD.Fi24Cp.Pc.p466 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 470) CFSG.KD.Fi24Cp.Pc.p468 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 472) CFSG.KD.Fi24Cp.Pc.p470 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 474) CFSG.KD.Fi24Cp.Pc.p472 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 476) CFSG.KD.Fi24Cp.Pc.p474 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f35

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v478 : Nat := CFSG.KD.Fi24Cp.KV3 95
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v479 : Nat := CFSG.KD.Fi24Cp.KV3 96
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l480 : List Nat := [CFSG.KD.Fi24Cp.Pc.v478, CFSG.KD.Fi24Cp.Pc.v479]
theorem CFSG.KD.Fi24Cp.Pc.p478 : Nat.beq (runC AR SD 478 (ckL CFSG.KD.Fi24Cp.Pc.l480) 2 478 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v480 : Nat := CFSG.KD.Fi24Cp.KV3 97
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v481 : Nat := CFSG.KD.Fi24Cp.KV3 98
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l482 : List Nat := [CFSG.KD.Fi24Cp.Pc.v478, CFSG.KD.Fi24Cp.Pc.v479, CFSG.KD.Fi24Cp.Pc.v480, CFSG.KD.Fi24Cp.Pc.v481]
theorem CFSG.KD.Fi24Cp.Pc.p480 : Nat.beq (runC AR SD 478 (ckL CFSG.KD.Fi24Cp.Pc.l482) 2 480 CFSG.KD.Fi24Cp.Pc.l480) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v482 : Nat := CFSG.KD.Fi24Cp.KV3 99
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v483 : Nat := CFSG.KD.Fi24Cp.KV3 100
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l484 : List Nat := [CFSG.KD.Fi24Cp.Pc.v478, CFSG.KD.Fi24Cp.Pc.v479, CFSG.KD.Fi24Cp.Pc.v480, CFSG.KD.Fi24Cp.Pc.v481, CFSG.KD.Fi24Cp.Pc.v482, CFSG.KD.Fi24Cp.Pc.v483]
theorem CFSG.KD.Fi24Cp.Pc.p482 : Nat.beq (runC AR SD 478 (ckL CFSG.KD.Fi24Cp.Pc.l484) 2 482 CFSG.KD.Fi24Cp.Pc.l482) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v484 : Nat := CFSG.KD.Fi24Cp.KV3 101
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v485 : Nat := CFSG.KD.Fi24Cp.KV3 102
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l486 : List Nat := [CFSG.KD.Fi24Cp.Pc.v478, CFSG.KD.Fi24Cp.Pc.v479, CFSG.KD.Fi24Cp.Pc.v480, CFSG.KD.Fi24Cp.Pc.v481, CFSG.KD.Fi24Cp.Pc.v482, CFSG.KD.Fi24Cp.Pc.v483, CFSG.KD.Fi24Cp.Pc.v484, CFSG.KD.Fi24Cp.Pc.v485]
theorem CFSG.KD.Fi24Cp.Pc.p484 : Nat.beq (runC AR SD 478 (ckL CFSG.KD.Fi24Cp.Pc.l486) 2 484 CFSG.KD.Fi24Cp.Pc.l484) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a486_3 : Nat := CFSG.KD.Fi24Cp.KV3 103
theorem CFSG.KD.Fi24Cp.Pc.q486_3 : Nat.beq (powTop AR.mul (getV AR SD 478 CFSG.KD.Fi24Cp.Pc.l486 (SD.na.getD 486 0)) (SD.nk.getD 486 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a486_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a486_2 : Nat := CFSG.KD.Fi24Cp.KV3 104
theorem CFSG.KD.Fi24Cp.Pc.q486_2 : Nat.beq (powTop AR.mul (getV AR SD 478 CFSG.KD.Fi24Cp.Pc.l486 (SD.na.getD 486 0)) (SD.nk.getD 486 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a486_2) 1 CFSG.KD.Fi24Cp.Pc.a486_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a486_1 : Nat := CFSG.KD.Fi24Cp.KV3 105
theorem CFSG.KD.Fi24Cp.Pc.q486_1 : Nat.beq (powTop AR.mul (getV AR SD 478 CFSG.KD.Fi24Cp.Pc.l486 (SD.na.getD 486 0)) (SD.nk.getD 486 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a486_1) 1 CFSG.KD.Fi24Cp.Pc.a486_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v486 : Nat := CFSG.KD.Fi24Cp.KV3 106
theorem CFSG.KD.Fi24Cp.Pc.r486 : Nat.beq (powR AR.mul AR.one (getV AR SD 478 CFSG.KD.Fi24Cp.Pc.l486 (SD.na.getD 486 0)) (SD.nk.getD 486 1) 1 CFSG.KD.Fi24Cp.Pc.a486_1 true) CFSG.KD.Fi24Cp.Pc.v486 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l487 : List Nat := [CFSG.KD.Fi24Cp.Pc.v478, CFSG.KD.Fi24Cp.Pc.v479, CFSG.KD.Fi24Cp.Pc.v480, CFSG.KD.Fi24Cp.Pc.v481, CFSG.KD.Fi24Cp.Pc.v482, CFSG.KD.Fi24Cp.Pc.v483, CFSG.KD.Fi24Cp.Pc.v484, CFSG.KD.Fi24Cp.Pc.v485, CFSG.KD.Fi24Cp.Pc.v486]
theorem CFSG.KD.Fi24Cp.Pc.f36 : Nat.beq (runC AR SD 478 (finC AR SD (nat_lit 36) 478 487) 0 487 CFSG.KD.Fi24Cp.Pc.l487) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk36 : chk (nat_lit 36) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 36) (lo := 478) (hi := 487) (m := 9) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 9) (m2 := 7) (j2 := 480) CFSG.KD.Fi24Cp.Pc.p478 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 482) CFSG.KD.Fi24Cp.Pc.p480 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 484) CFSG.KD.Fi24Cp.Pc.p482 rfl rfl).trans ((runC_seq (m := 3) (m2 := 1) (j2 := 486) CFSG.KD.Fi24Cp.Pc.p484 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 487) (Lr := CFSG.KD.Fi24Cp.Pc.l487) ((nodeV_pow (R := AR) (D := SD) (lo := 478) (L := CFSG.KD.Fi24Cp.Pc.l486) (j := 486) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 478 CFSG.KD.Fi24Cp.Pc.l486 (SD.na.getD 486 0)) (SD.nk.getD 486 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q486_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q486_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q486_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r486)))))) (by quickRfl) rfl rfl rfl))))))).trans CFSG.KD.Fi24Cp.Pc.f36

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a487_3 : Nat := CFSG.KD.Fi24Cp.KV3 107
theorem CFSG.KD.Fi24Cp.Pc.q487_3 : Nat.beq (powTop AR.mul (getV AR SD 487 [] (SD.na.getD 487 0)) (SD.nk.getD 487 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a487_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a487_2 : Nat := CFSG.KD.Fi24Cp.KV3 108
theorem CFSG.KD.Fi24Cp.Pc.q487_2 : Nat.beq (powTop AR.mul (getV AR SD 487 [] (SD.na.getD 487 0)) (SD.nk.getD 487 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a487_2) 1 CFSG.KD.Fi24Cp.Pc.a487_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a487_1 : Nat := CFSG.KD.Fi24Cp.KV3 109
theorem CFSG.KD.Fi24Cp.Pc.q487_1 : Nat.beq (powTop AR.mul (getV AR SD 487 [] (SD.na.getD 487 0)) (SD.nk.getD 487 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a487_1) 1 CFSG.KD.Fi24Cp.Pc.a487_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v487 : Nat := CFSG.KD.Fi24Cp.KV3 110
theorem CFSG.KD.Fi24Cp.Pc.r487 : Nat.beq (powR AR.mul AR.one (getV AR SD 487 [] (SD.na.getD 487 0)) (SD.nk.getD 487 1) 1 CFSG.KD.Fi24Cp.Pc.a487_1 true) CFSG.KD.Fi24Cp.Pc.v487 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l488 : List Nat := [CFSG.KD.Fi24Cp.Pc.v487]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a488_2 : Nat := CFSG.KD.Fi24Cp.KV3 111
theorem CFSG.KD.Fi24Cp.Pc.q488_2 : Nat.beq (powTop AR.mul (getV AR SD 487 CFSG.KD.Fi24Cp.Pc.l488 (SD.na.getD 488 0)) (SD.nk.getD 488 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a488_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a488_1 : Nat := CFSG.KD.Fi24Cp.KV3 112
theorem CFSG.KD.Fi24Cp.Pc.q488_1 : Nat.beq (powTop AR.mul (getV AR SD 487 CFSG.KD.Fi24Cp.Pc.l488 (SD.na.getD 488 0)) (SD.nk.getD 488 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a488_1) 1 CFSG.KD.Fi24Cp.Pc.a488_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v488 : Nat := CFSG.KD.Fi24Cp.KV3 113
theorem CFSG.KD.Fi24Cp.Pc.r488 : Nat.beq (powR AR.mul AR.one (getV AR SD 487 CFSG.KD.Fi24Cp.Pc.l488 (SD.na.getD 488 0)) (SD.nk.getD 488 1) 1 CFSG.KD.Fi24Cp.Pc.a488_1 true) CFSG.KD.Fi24Cp.Pc.v488 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l489 : List Nat := [CFSG.KD.Fi24Cp.Pc.v487, CFSG.KD.Fi24Cp.Pc.v488]
theorem CFSG.KD.Fi24Cp.Pc.f37 : Nat.beq (runC AR SD 487 (finC AR SD (nat_lit 37) 487 489) 0 489 CFSG.KD.Fi24Cp.Pc.l489) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk37 : chk (nat_lit 37) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 37) (lo := 487) (hi := 489) (m := 2) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 2) (m2 := 1) (j2 := 488) (Lr := CFSG.KD.Fi24Cp.Pc.l488) ((nodeV_pow (R := AR) (D := SD) (lo := 487) (L := []) (j := 487) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 487 [] (SD.na.getD 487 0)) (SD.nk.getD 487 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q487_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q487_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q487_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r487)))))) (by quickRfl) rfl rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 489) (Lr := CFSG.KD.Fi24Cp.Pc.l489) ((nodeV_pow (R := AR) (D := SD) (lo := 487) (L := CFSG.KD.Fi24Cp.Pc.l488) (j := 488) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 487 CFSG.KD.Fi24Cp.Pc.l488 (SD.na.getD 488 0)) (SD.nk.getD 488 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q488_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q488_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r488))))) (by quickRfl) rfl rfl rfl)))).trans CFSG.KD.Fi24Cp.Pc.f37

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a489_3 : Nat := CFSG.KD.Fi24Cp.KV3 114
theorem CFSG.KD.Fi24Cp.Pc.q489_3 : Nat.beq (powTop AR.mul (getV AR SD 489 [] (SD.na.getD 489 0)) (SD.nk.getD 489 1) 3 (ckP CFSG.KD.Fi24Cp.Pc.a489_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a489_1 : Nat := CFSG.KD.Fi24Cp.KV3 115
theorem CFSG.KD.Fi24Cp.Pc.q489_1 : Nat.beq (powTop AR.mul (getV AR SD 489 [] (SD.na.getD 489 0)) (SD.nk.getD 489 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a489_1) 2 CFSG.KD.Fi24Cp.Pc.a489_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v489 : Nat := CFSG.KD.Fi24Cp.KV3 116
theorem CFSG.KD.Fi24Cp.Pc.r489 : Nat.beq (powR AR.mul AR.one (getV AR SD 489 [] (SD.na.getD 489 0)) (SD.nk.getD 489 1) 1 CFSG.KD.Fi24Cp.Pc.a489_1 true) CFSG.KD.Fi24Cp.Pc.v489 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v490 : Nat := CFSG.KD.Fi24Cp.KV3 117
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v491 : Nat := CFSG.KD.Fi24Cp.KV3 118
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l490 : List Nat := [CFSG.KD.Fi24Cp.Pc.v489]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l492 : List Nat := [CFSG.KD.Fi24Cp.Pc.v489, CFSG.KD.Fi24Cp.Pc.v490, CFSG.KD.Fi24Cp.Pc.v491]
theorem CFSG.KD.Fi24Cp.Pc.p490 : Nat.beq (runC AR SD 489 (ckL CFSG.KD.Fi24Cp.Pc.l492) 2 490 CFSG.KD.Fi24Cp.Pc.l490) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v492 : Nat := CFSG.KD.Fi24Cp.KV3 119
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v493 : Nat := CFSG.KD.Fi24Cp.KV3 120
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l494 : List Nat := [CFSG.KD.Fi24Cp.Pc.v489, CFSG.KD.Fi24Cp.Pc.v490, CFSG.KD.Fi24Cp.Pc.v491, CFSG.KD.Fi24Cp.Pc.v492, CFSG.KD.Fi24Cp.Pc.v493]
theorem CFSG.KD.Fi24Cp.Pc.p492 : Nat.beq (runC AR SD 489 (ckL CFSG.KD.Fi24Cp.Pc.l494) 2 492 CFSG.KD.Fi24Cp.Pc.l492) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v494 : Nat := CFSG.KD.Fi24Cp.KV3 121
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v495 : Nat := CFSG.KD.Fi24Cp.KV3 122
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l496 : List Nat := [CFSG.KD.Fi24Cp.Pc.v489, CFSG.KD.Fi24Cp.Pc.v490, CFSG.KD.Fi24Cp.Pc.v491, CFSG.KD.Fi24Cp.Pc.v492, CFSG.KD.Fi24Cp.Pc.v493, CFSG.KD.Fi24Cp.Pc.v494, CFSG.KD.Fi24Cp.Pc.v495]
theorem CFSG.KD.Fi24Cp.Pc.p494 : Nat.beq (runC AR SD 489 (ckL CFSG.KD.Fi24Cp.Pc.l496) 2 494 CFSG.KD.Fi24Cp.Pc.l494) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v496 : Nat := CFSG.KD.Fi24Cp.KV3 123
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v497 : Nat := CFSG.KD.Fi24Cp.KV3 124
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l498 : List Nat := [CFSG.KD.Fi24Cp.Pc.v489, CFSG.KD.Fi24Cp.Pc.v490, CFSG.KD.Fi24Cp.Pc.v491, CFSG.KD.Fi24Cp.Pc.v492, CFSG.KD.Fi24Cp.Pc.v493, CFSG.KD.Fi24Cp.Pc.v494, CFSG.KD.Fi24Cp.Pc.v495, CFSG.KD.Fi24Cp.Pc.v496, CFSG.KD.Fi24Cp.Pc.v497]
theorem CFSG.KD.Fi24Cp.Pc.p496 : Nat.beq (runC AR SD 489 (ckL CFSG.KD.Fi24Cp.Pc.l498) 2 496 CFSG.KD.Fi24Cp.Pc.l496) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v498 : Nat := CFSG.KD.Fi24Cp.KV3 125
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v499 : Nat := CFSG.KD.Fi24Cp.KV3 126
theorem CFSG.KD.Fi24Cp.Pc.f38 : Nat.beq (runC AR SD 489 (finC AR SD (nat_lit 38) 489 500) 2 498 CFSG.KD.Fi24Cp.Pc.l498) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk38 : chk (nat_lit 38) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 38) (lo := 489) (hi := 500) (m := 11) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_node (m := 11) (m2 := 10) (j2 := 490) (Lr := CFSG.KD.Fi24Cp.Pc.l490) ((nodeV_pow (R := AR) (D := SD) (lo := 489) (L := []) (j := 489) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 489 [] (SD.na.getD 489 0)) (SD.nk.getD 489 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q489_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Cp.Pc.q489_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r489))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 492) CFSG.KD.Fi24Cp.Pc.p490 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 494) CFSG.KD.Fi24Cp.Pc.p492 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 496) CFSG.KD.Fi24Cp.Pc.p494 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 498) CFSG.KD.Fi24Cp.Pc.p496 rfl rfl))))))).trans CFSG.KD.Fi24Cp.Pc.f38

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v500 : Nat := CFSG.KD.Fi24Cp.KV3 127
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v501 : Nat := CFSG.KD.Fi24Cp.KV3 128
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l502 : List Nat := [CFSG.KD.Fi24Cp.Pc.v500, CFSG.KD.Fi24Cp.Pc.v501]
theorem CFSG.KD.Fi24Cp.Pc.p500 : Nat.beq (runC AR SD 500 (ckL CFSG.KD.Fi24Cp.Pc.l502) 2 500 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v502 : Nat := CFSG.KD.Fi24Cp.KV3 129
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v503 : Nat := CFSG.KD.Fi24Cp.KV3 130
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l504 : List Nat := [CFSG.KD.Fi24Cp.Pc.v500, CFSG.KD.Fi24Cp.Pc.v501, CFSG.KD.Fi24Cp.Pc.v502, CFSG.KD.Fi24Cp.Pc.v503]
theorem CFSG.KD.Fi24Cp.Pc.p502 : Nat.beq (runC AR SD 500 (ckL CFSG.KD.Fi24Cp.Pc.l504) 2 502 CFSG.KD.Fi24Cp.Pc.l502) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v504 : Nat := CFSG.KD.Fi24Cp.KV3 131
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v505 : Nat := CFSG.KD.Fi24Cp.KV3 132
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l506 : List Nat := [CFSG.KD.Fi24Cp.Pc.v500, CFSG.KD.Fi24Cp.Pc.v501, CFSG.KD.Fi24Cp.Pc.v502, CFSG.KD.Fi24Cp.Pc.v503, CFSG.KD.Fi24Cp.Pc.v504, CFSG.KD.Fi24Cp.Pc.v505]
theorem CFSG.KD.Fi24Cp.Pc.p504 : Nat.beq (runC AR SD 500 (ckL CFSG.KD.Fi24Cp.Pc.l506) 2 504 CFSG.KD.Fi24Cp.Pc.l504) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v506 : Nat := CFSG.KD.Fi24Cp.KV3 133
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v507 : Nat := CFSG.KD.Fi24Cp.KV3 134
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l508 : List Nat := [CFSG.KD.Fi24Cp.Pc.v500, CFSG.KD.Fi24Cp.Pc.v501, CFSG.KD.Fi24Cp.Pc.v502, CFSG.KD.Fi24Cp.Pc.v503, CFSG.KD.Fi24Cp.Pc.v504, CFSG.KD.Fi24Cp.Pc.v505, CFSG.KD.Fi24Cp.Pc.v506, CFSG.KD.Fi24Cp.Pc.v507]
theorem CFSG.KD.Fi24Cp.Pc.p506 : Nat.beq (runC AR SD 500 (ckL CFSG.KD.Fi24Cp.Pc.l508) 2 506 CFSG.KD.Fi24Cp.Pc.l506) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v508 : Nat := CFSG.KD.Fi24Cp.KV3 135
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v509 : Nat := CFSG.KD.Fi24Cp.KV3 136
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l510 : List Nat := [CFSG.KD.Fi24Cp.Pc.v500, CFSG.KD.Fi24Cp.Pc.v501, CFSG.KD.Fi24Cp.Pc.v502, CFSG.KD.Fi24Cp.Pc.v503, CFSG.KD.Fi24Cp.Pc.v504, CFSG.KD.Fi24Cp.Pc.v505, CFSG.KD.Fi24Cp.Pc.v506, CFSG.KD.Fi24Cp.Pc.v507, CFSG.KD.Fi24Cp.Pc.v508, CFSG.KD.Fi24Cp.Pc.v509]
theorem CFSG.KD.Fi24Cp.Pc.p508 : Nat.beq (runC AR SD 500 (ckL CFSG.KD.Fi24Cp.Pc.l510) 2 508 CFSG.KD.Fi24Cp.Pc.l508) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v510 : Nat := CFSG.KD.Fi24Cp.KV3 137
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v511 : Nat := CFSG.KD.Fi24Cp.KV3 138
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l512 : List Nat := [CFSG.KD.Fi24Cp.Pc.v500, CFSG.KD.Fi24Cp.Pc.v501, CFSG.KD.Fi24Cp.Pc.v502, CFSG.KD.Fi24Cp.Pc.v503, CFSG.KD.Fi24Cp.Pc.v504, CFSG.KD.Fi24Cp.Pc.v505, CFSG.KD.Fi24Cp.Pc.v506, CFSG.KD.Fi24Cp.Pc.v507, CFSG.KD.Fi24Cp.Pc.v508, CFSG.KD.Fi24Cp.Pc.v509, CFSG.KD.Fi24Cp.Pc.v510, CFSG.KD.Fi24Cp.Pc.v511]
theorem CFSG.KD.Fi24Cp.Pc.p510 : Nat.beq (runC AR SD 500 (ckL CFSG.KD.Fi24Cp.Pc.l512) 2 510 CFSG.KD.Fi24Cp.Pc.l510) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v512 : Nat := CFSG.KD.Fi24Cp.KV3 139
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v513 : Nat := CFSG.KD.Fi24Cp.KV3 140
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l514 : List Nat := [CFSG.KD.Fi24Cp.Pc.v500, CFSG.KD.Fi24Cp.Pc.v501, CFSG.KD.Fi24Cp.Pc.v502, CFSG.KD.Fi24Cp.Pc.v503, CFSG.KD.Fi24Cp.Pc.v504, CFSG.KD.Fi24Cp.Pc.v505, CFSG.KD.Fi24Cp.Pc.v506, CFSG.KD.Fi24Cp.Pc.v507, CFSG.KD.Fi24Cp.Pc.v508, CFSG.KD.Fi24Cp.Pc.v509, CFSG.KD.Fi24Cp.Pc.v510, CFSG.KD.Fi24Cp.Pc.v511, CFSG.KD.Fi24Cp.Pc.v512, CFSG.KD.Fi24Cp.Pc.v513]
theorem CFSG.KD.Fi24Cp.Pc.p512 : Nat.beq (runC AR SD 500 (ckL CFSG.KD.Fi24Cp.Pc.l514) 2 512 CFSG.KD.Fi24Cp.Pc.l512) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v514 : Nat := CFSG.KD.Fi24Cp.KV3 141
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v515 : Nat := CFSG.KD.Fi24Cp.KV3 142
theorem CFSG.KD.Fi24Cp.Pc.f39 : Nat.beq (runC AR SD 500 (finC AR SD (nat_lit 39) 500 516) 2 514 CFSG.KD.Fi24Cp.Pc.l514) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk39 : chk (nat_lit 39) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 39) (lo := 500) (hi := 516) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 502) CFSG.KD.Fi24Cp.Pc.p500 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 504) CFSG.KD.Fi24Cp.Pc.p502 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 506) CFSG.KD.Fi24Cp.Pc.p504 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 508) CFSG.KD.Fi24Cp.Pc.p506 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 510) CFSG.KD.Fi24Cp.Pc.p508 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 512) CFSG.KD.Fi24Cp.Pc.p510 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 514) CFSG.KD.Fi24Cp.Pc.p512 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f39

end
