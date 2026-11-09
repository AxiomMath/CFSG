module

public import Certificates.Kernel.Sporadic.Fi24Tc.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Tc KV3 "Certificates/Kernel/Sporadic/Fi24Tc/data/v3.bin" 152491 4 18298920 11717955978541524880

public section

open CFSG.KD.Fi24Tc CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v376 : Nat := CFSG.KD.Fi24Tc.KV3 0
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v377 : Nat := CFSG.KD.Fi24Tc.KV3 1
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l378 : List Nat := [CFSG.KD.Fi24Tc.Pc.v376, CFSG.KD.Fi24Tc.Pc.v377]
theorem CFSG.KD.Fi24Tc.Pc.p376 : Nat.beq (runC AR SD 376 (ckL CFSG.KD.Fi24Tc.Pc.l378) 2 376 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v378 : Nat := CFSG.KD.Fi24Tc.KV3 2
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v379 : Nat := CFSG.KD.Fi24Tc.KV3 3
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l380 : List Nat := [CFSG.KD.Fi24Tc.Pc.v376, CFSG.KD.Fi24Tc.Pc.v377, CFSG.KD.Fi24Tc.Pc.v378, CFSG.KD.Fi24Tc.Pc.v379]
theorem CFSG.KD.Fi24Tc.Pc.p378 : Nat.beq (runC AR SD 376 (ckL CFSG.KD.Fi24Tc.Pc.l380) 2 378 CFSG.KD.Fi24Tc.Pc.l378) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v380 : Nat := CFSG.KD.Fi24Tc.KV3 4
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v381 : Nat := CFSG.KD.Fi24Tc.KV3 5
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l382 : List Nat := [CFSG.KD.Fi24Tc.Pc.v376, CFSG.KD.Fi24Tc.Pc.v377, CFSG.KD.Fi24Tc.Pc.v378, CFSG.KD.Fi24Tc.Pc.v379, CFSG.KD.Fi24Tc.Pc.v380, CFSG.KD.Fi24Tc.Pc.v381]
theorem CFSG.KD.Fi24Tc.Pc.p380 : Nat.beq (runC AR SD 376 (ckL CFSG.KD.Fi24Tc.Pc.l382) 2 380 CFSG.KD.Fi24Tc.Pc.l380) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f60 : Nat.beq (runC AR SD 376 (finC AR SD (nat_lit 60) 376 384) 2 382 CFSG.KD.Fi24Tc.Pc.l382) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk60 : chk (nat_lit 60) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 60) (lo := 376) (hi := 384) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 378) CFSG.KD.Fi24Tc.Pc.p376 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 380) CFSG.KD.Fi24Tc.Pc.p378 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 382) CFSG.KD.Fi24Tc.Pc.p380 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f60

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v384 : Nat := CFSG.KD.Fi24Tc.KV3 6
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v385 : Nat := CFSG.KD.Fi24Tc.KV3 7
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l386 : List Nat := [CFSG.KD.Fi24Tc.Pc.v384, CFSG.KD.Fi24Tc.Pc.v385]
theorem CFSG.KD.Fi24Tc.Pc.p384 : Nat.beq (runC AR SD 384 (ckL CFSG.KD.Fi24Tc.Pc.l386) 2 384 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v386 : Nat := CFSG.KD.Fi24Tc.KV3 8
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v387 : Nat := CFSG.KD.Fi24Tc.KV3 9
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l388 : List Nat := [CFSG.KD.Fi24Tc.Pc.v384, CFSG.KD.Fi24Tc.Pc.v385, CFSG.KD.Fi24Tc.Pc.v386, CFSG.KD.Fi24Tc.Pc.v387]
theorem CFSG.KD.Fi24Tc.Pc.p386 : Nat.beq (runC AR SD 384 (ckL CFSG.KD.Fi24Tc.Pc.l388) 2 386 CFSG.KD.Fi24Tc.Pc.l386) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v388 : Nat := CFSG.KD.Fi24Tc.KV3 10
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v389 : Nat := CFSG.KD.Fi24Tc.KV3 11
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l390 : List Nat := [CFSG.KD.Fi24Tc.Pc.v384, CFSG.KD.Fi24Tc.Pc.v385, CFSG.KD.Fi24Tc.Pc.v386, CFSG.KD.Fi24Tc.Pc.v387, CFSG.KD.Fi24Tc.Pc.v388, CFSG.KD.Fi24Tc.Pc.v389]
theorem CFSG.KD.Fi24Tc.Pc.p388 : Nat.beq (runC AR SD 384 (ckL CFSG.KD.Fi24Tc.Pc.l390) 2 388 CFSG.KD.Fi24Tc.Pc.l388) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f61 : Nat.beq (runC AR SD 384 (finC AR SD (nat_lit 61) 384 392) 2 390 CFSG.KD.Fi24Tc.Pc.l390) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk61 : chk (nat_lit 61) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 61) (lo := 384) (hi := 392) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 386) CFSG.KD.Fi24Tc.Pc.p384 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 388) CFSG.KD.Fi24Tc.Pc.p386 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 390) CFSG.KD.Fi24Tc.Pc.p388 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f61

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v392 : Nat := CFSG.KD.Fi24Tc.KV3 12
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v393 : Nat := CFSG.KD.Fi24Tc.KV3 13
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l394 : List Nat := [CFSG.KD.Fi24Tc.Pc.v392, CFSG.KD.Fi24Tc.Pc.v393]
theorem CFSG.KD.Fi24Tc.Pc.p392 : Nat.beq (runC AR SD 392 (ckL CFSG.KD.Fi24Tc.Pc.l394) 2 392 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v394 : Nat := CFSG.KD.Fi24Tc.KV3 14
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v395 : Nat := CFSG.KD.Fi24Tc.KV3 15
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l396 : List Nat := [CFSG.KD.Fi24Tc.Pc.v392, CFSG.KD.Fi24Tc.Pc.v393, CFSG.KD.Fi24Tc.Pc.v394, CFSG.KD.Fi24Tc.Pc.v395]
theorem CFSG.KD.Fi24Tc.Pc.p394 : Nat.beq (runC AR SD 392 (ckL CFSG.KD.Fi24Tc.Pc.l396) 2 394 CFSG.KD.Fi24Tc.Pc.l394) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v396 : Nat := CFSG.KD.Fi24Tc.KV3 16
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v397 : Nat := CFSG.KD.Fi24Tc.KV3 17
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l398 : List Nat := [CFSG.KD.Fi24Tc.Pc.v392, CFSG.KD.Fi24Tc.Pc.v393, CFSG.KD.Fi24Tc.Pc.v394, CFSG.KD.Fi24Tc.Pc.v395, CFSG.KD.Fi24Tc.Pc.v396, CFSG.KD.Fi24Tc.Pc.v397]
theorem CFSG.KD.Fi24Tc.Pc.p396 : Nat.beq (runC AR SD 392 (ckL CFSG.KD.Fi24Tc.Pc.l398) 2 396 CFSG.KD.Fi24Tc.Pc.l396) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f62 : Nat.beq (runC AR SD 392 (finC AR SD (nat_lit 62) 392 400) 2 398 CFSG.KD.Fi24Tc.Pc.l398) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk62 : chk (nat_lit 62) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 62) (lo := 392) (hi := 400) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 394) CFSG.KD.Fi24Tc.Pc.p392 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 396) CFSG.KD.Fi24Tc.Pc.p394 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 398) CFSG.KD.Fi24Tc.Pc.p396 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f62

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v400 : Nat := CFSG.KD.Fi24Tc.KV3 18
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v401 : Nat := CFSG.KD.Fi24Tc.KV3 19
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l402 : List Nat := [CFSG.KD.Fi24Tc.Pc.v400, CFSG.KD.Fi24Tc.Pc.v401]
theorem CFSG.KD.Fi24Tc.Pc.p400 : Nat.beq (runC AR SD 400 (ckL CFSG.KD.Fi24Tc.Pc.l402) 2 400 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v402 : Nat := CFSG.KD.Fi24Tc.KV3 20
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v403 : Nat := CFSG.KD.Fi24Tc.KV3 21
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l404 : List Nat := [CFSG.KD.Fi24Tc.Pc.v400, CFSG.KD.Fi24Tc.Pc.v401, CFSG.KD.Fi24Tc.Pc.v402, CFSG.KD.Fi24Tc.Pc.v403]
theorem CFSG.KD.Fi24Tc.Pc.p402 : Nat.beq (runC AR SD 400 (ckL CFSG.KD.Fi24Tc.Pc.l404) 2 402 CFSG.KD.Fi24Tc.Pc.l402) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v404 : Nat := CFSG.KD.Fi24Tc.KV3 22
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v405 : Nat := CFSG.KD.Fi24Tc.KV3 23
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l406 : List Nat := [CFSG.KD.Fi24Tc.Pc.v400, CFSG.KD.Fi24Tc.Pc.v401, CFSG.KD.Fi24Tc.Pc.v402, CFSG.KD.Fi24Tc.Pc.v403, CFSG.KD.Fi24Tc.Pc.v404, CFSG.KD.Fi24Tc.Pc.v405]
theorem CFSG.KD.Fi24Tc.Pc.p404 : Nat.beq (runC AR SD 400 (ckL CFSG.KD.Fi24Tc.Pc.l406) 2 404 CFSG.KD.Fi24Tc.Pc.l404) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f63 : Nat.beq (runC AR SD 400 (finC AR SD (nat_lit 63) 400 408) 2 406 CFSG.KD.Fi24Tc.Pc.l406) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk63 : chk (nat_lit 63) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 63) (lo := 400) (hi := 408) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 402) CFSG.KD.Fi24Tc.Pc.p400 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 404) CFSG.KD.Fi24Tc.Pc.p402 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 406) CFSG.KD.Fi24Tc.Pc.p404 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f63

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v408 : Nat := CFSG.KD.Fi24Tc.KV3 24
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v409 : Nat := CFSG.KD.Fi24Tc.KV3 25
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l410 : List Nat := [CFSG.KD.Fi24Tc.Pc.v408, CFSG.KD.Fi24Tc.Pc.v409]
theorem CFSG.KD.Fi24Tc.Pc.p408 : Nat.beq (runC AR SD 408 (ckL CFSG.KD.Fi24Tc.Pc.l410) 2 408 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v410 : Nat := CFSG.KD.Fi24Tc.KV3 26
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v411 : Nat := CFSG.KD.Fi24Tc.KV3 27
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l412 : List Nat := [CFSG.KD.Fi24Tc.Pc.v408, CFSG.KD.Fi24Tc.Pc.v409, CFSG.KD.Fi24Tc.Pc.v410, CFSG.KD.Fi24Tc.Pc.v411]
theorem CFSG.KD.Fi24Tc.Pc.p410 : Nat.beq (runC AR SD 408 (ckL CFSG.KD.Fi24Tc.Pc.l412) 2 410 CFSG.KD.Fi24Tc.Pc.l410) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v412 : Nat := CFSG.KD.Fi24Tc.KV3 28
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v413 : Nat := CFSG.KD.Fi24Tc.KV3 29
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l414 : List Nat := [CFSG.KD.Fi24Tc.Pc.v408, CFSG.KD.Fi24Tc.Pc.v409, CFSG.KD.Fi24Tc.Pc.v410, CFSG.KD.Fi24Tc.Pc.v411, CFSG.KD.Fi24Tc.Pc.v412, CFSG.KD.Fi24Tc.Pc.v413]
theorem CFSG.KD.Fi24Tc.Pc.p412 : Nat.beq (runC AR SD 408 (ckL CFSG.KD.Fi24Tc.Pc.l414) 2 412 CFSG.KD.Fi24Tc.Pc.l412) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f64 : Nat.beq (runC AR SD 408 (finC AR SD (nat_lit 64) 408 416) 2 414 CFSG.KD.Fi24Tc.Pc.l414) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk64 : chk (nat_lit 64) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 64) (lo := 408) (hi := 416) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 410) CFSG.KD.Fi24Tc.Pc.p408 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 412) CFSG.KD.Fi24Tc.Pc.p410 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 414) CFSG.KD.Fi24Tc.Pc.p412 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f64

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v416 : Nat := CFSG.KD.Fi24Tc.KV3 30
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v417 : Nat := CFSG.KD.Fi24Tc.KV3 31
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l418 : List Nat := [CFSG.KD.Fi24Tc.Pc.v416, CFSG.KD.Fi24Tc.Pc.v417]
theorem CFSG.KD.Fi24Tc.Pc.p416 : Nat.beq (runC AR SD 416 (ckL CFSG.KD.Fi24Tc.Pc.l418) 2 416 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v418 : Nat := CFSG.KD.Fi24Tc.KV3 32
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v419 : Nat := CFSG.KD.Fi24Tc.KV3 33
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l420 : List Nat := [CFSG.KD.Fi24Tc.Pc.v416, CFSG.KD.Fi24Tc.Pc.v417, CFSG.KD.Fi24Tc.Pc.v418, CFSG.KD.Fi24Tc.Pc.v419]
theorem CFSG.KD.Fi24Tc.Pc.p418 : Nat.beq (runC AR SD 416 (ckL CFSG.KD.Fi24Tc.Pc.l420) 2 418 CFSG.KD.Fi24Tc.Pc.l418) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v420 : Nat := CFSG.KD.Fi24Tc.KV3 34
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v421 : Nat := CFSG.KD.Fi24Tc.KV3 35
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l422 : List Nat := [CFSG.KD.Fi24Tc.Pc.v416, CFSG.KD.Fi24Tc.Pc.v417, CFSG.KD.Fi24Tc.Pc.v418, CFSG.KD.Fi24Tc.Pc.v419, CFSG.KD.Fi24Tc.Pc.v420, CFSG.KD.Fi24Tc.Pc.v421]
theorem CFSG.KD.Fi24Tc.Pc.p420 : Nat.beq (runC AR SD 416 (ckL CFSG.KD.Fi24Tc.Pc.l422) 2 420 CFSG.KD.Fi24Tc.Pc.l420) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f65 : Nat.beq (runC AR SD 416 (finC AR SD (nat_lit 65) 416 424) 2 422 CFSG.KD.Fi24Tc.Pc.l422) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk65 : chk (nat_lit 65) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 65) (lo := 416) (hi := 424) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 418) CFSG.KD.Fi24Tc.Pc.p416 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 420) CFSG.KD.Fi24Tc.Pc.p418 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 422) CFSG.KD.Fi24Tc.Pc.p420 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f65

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v424 : Nat := CFSG.KD.Fi24Tc.KV3 36
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v425 : Nat := CFSG.KD.Fi24Tc.KV3 37
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l426 : List Nat := [CFSG.KD.Fi24Tc.Pc.v424, CFSG.KD.Fi24Tc.Pc.v425]
theorem CFSG.KD.Fi24Tc.Pc.p424 : Nat.beq (runC AR SD 424 (ckL CFSG.KD.Fi24Tc.Pc.l426) 2 424 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v426 : Nat := CFSG.KD.Fi24Tc.KV3 38
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v427 : Nat := CFSG.KD.Fi24Tc.KV3 39
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l428 : List Nat := [CFSG.KD.Fi24Tc.Pc.v424, CFSG.KD.Fi24Tc.Pc.v425, CFSG.KD.Fi24Tc.Pc.v426, CFSG.KD.Fi24Tc.Pc.v427]
theorem CFSG.KD.Fi24Tc.Pc.p426 : Nat.beq (runC AR SD 424 (ckL CFSG.KD.Fi24Tc.Pc.l428) 2 426 CFSG.KD.Fi24Tc.Pc.l426) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v428 : Nat := CFSG.KD.Fi24Tc.KV3 40
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v429 : Nat := CFSG.KD.Fi24Tc.KV3 41
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l430 : List Nat := [CFSG.KD.Fi24Tc.Pc.v424, CFSG.KD.Fi24Tc.Pc.v425, CFSG.KD.Fi24Tc.Pc.v426, CFSG.KD.Fi24Tc.Pc.v427, CFSG.KD.Fi24Tc.Pc.v428, CFSG.KD.Fi24Tc.Pc.v429]
theorem CFSG.KD.Fi24Tc.Pc.p428 : Nat.beq (runC AR SD 424 (ckL CFSG.KD.Fi24Tc.Pc.l430) 2 428 CFSG.KD.Fi24Tc.Pc.l428) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f66 : Nat.beq (runC AR SD 424 (finC AR SD (nat_lit 66) 424 432) 2 430 CFSG.KD.Fi24Tc.Pc.l430) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk66 : chk (nat_lit 66) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 66) (lo := 424) (hi := 432) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 426) CFSG.KD.Fi24Tc.Pc.p424 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 428) CFSG.KD.Fi24Tc.Pc.p426 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 430) CFSG.KD.Fi24Tc.Pc.p428 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f66

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v432 : Nat := CFSG.KD.Fi24Tc.KV3 42
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v433 : Nat := CFSG.KD.Fi24Tc.KV3 43
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l434 : List Nat := [CFSG.KD.Fi24Tc.Pc.v432, CFSG.KD.Fi24Tc.Pc.v433]
theorem CFSG.KD.Fi24Tc.Pc.p432 : Nat.beq (runC AR SD 432 (ckL CFSG.KD.Fi24Tc.Pc.l434) 2 432 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v434 : Nat := CFSG.KD.Fi24Tc.KV3 44
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v435 : Nat := CFSG.KD.Fi24Tc.KV3 45
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l436 : List Nat := [CFSG.KD.Fi24Tc.Pc.v432, CFSG.KD.Fi24Tc.Pc.v433, CFSG.KD.Fi24Tc.Pc.v434, CFSG.KD.Fi24Tc.Pc.v435]
theorem CFSG.KD.Fi24Tc.Pc.p434 : Nat.beq (runC AR SD 432 (ckL CFSG.KD.Fi24Tc.Pc.l436) 2 434 CFSG.KD.Fi24Tc.Pc.l434) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v436 : Nat := CFSG.KD.Fi24Tc.KV3 46
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v437 : Nat := CFSG.KD.Fi24Tc.KV3 47
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l438 : List Nat := [CFSG.KD.Fi24Tc.Pc.v432, CFSG.KD.Fi24Tc.Pc.v433, CFSG.KD.Fi24Tc.Pc.v434, CFSG.KD.Fi24Tc.Pc.v435, CFSG.KD.Fi24Tc.Pc.v436, CFSG.KD.Fi24Tc.Pc.v437]
theorem CFSG.KD.Fi24Tc.Pc.p436 : Nat.beq (runC AR SD 432 (ckL CFSG.KD.Fi24Tc.Pc.l438) 2 436 CFSG.KD.Fi24Tc.Pc.l436) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f67 : Nat.beq (runC AR SD 432 (finC AR SD (nat_lit 67) 432 440) 2 438 CFSG.KD.Fi24Tc.Pc.l438) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk67 : chk (nat_lit 67) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 67) (lo := 432) (hi := 440) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 434) CFSG.KD.Fi24Tc.Pc.p432 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 436) CFSG.KD.Fi24Tc.Pc.p434 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 438) CFSG.KD.Fi24Tc.Pc.p436 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f67

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v440 : Nat := CFSG.KD.Fi24Tc.KV3 48
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v441 : Nat := CFSG.KD.Fi24Tc.KV3 49
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l442 : List Nat := [CFSG.KD.Fi24Tc.Pc.v440, CFSG.KD.Fi24Tc.Pc.v441]
theorem CFSG.KD.Fi24Tc.Pc.p440 : Nat.beq (runC AR SD 440 (ckL CFSG.KD.Fi24Tc.Pc.l442) 2 440 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v442 : Nat := CFSG.KD.Fi24Tc.KV3 50
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v443 : Nat := CFSG.KD.Fi24Tc.KV3 51
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l444 : List Nat := [CFSG.KD.Fi24Tc.Pc.v440, CFSG.KD.Fi24Tc.Pc.v441, CFSG.KD.Fi24Tc.Pc.v442, CFSG.KD.Fi24Tc.Pc.v443]
theorem CFSG.KD.Fi24Tc.Pc.p442 : Nat.beq (runC AR SD 440 (ckL CFSG.KD.Fi24Tc.Pc.l444) 2 442 CFSG.KD.Fi24Tc.Pc.l442) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v444 : Nat := CFSG.KD.Fi24Tc.KV3 52
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v445 : Nat := CFSG.KD.Fi24Tc.KV3 53
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l446 : List Nat := [CFSG.KD.Fi24Tc.Pc.v440, CFSG.KD.Fi24Tc.Pc.v441, CFSG.KD.Fi24Tc.Pc.v442, CFSG.KD.Fi24Tc.Pc.v443, CFSG.KD.Fi24Tc.Pc.v444, CFSG.KD.Fi24Tc.Pc.v445]
theorem CFSG.KD.Fi24Tc.Pc.p444 : Nat.beq (runC AR SD 440 (ckL CFSG.KD.Fi24Tc.Pc.l446) 2 444 CFSG.KD.Fi24Tc.Pc.l444) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f68 : Nat.beq (runC AR SD 440 (finC AR SD (nat_lit 68) 440 448) 2 446 CFSG.KD.Fi24Tc.Pc.l446) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk68 : chk (nat_lit 68) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 68) (lo := 440) (hi := 448) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 442) CFSG.KD.Fi24Tc.Pc.p440 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 444) CFSG.KD.Fi24Tc.Pc.p442 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 446) CFSG.KD.Fi24Tc.Pc.p444 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f68

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v448 : Nat := CFSG.KD.Fi24Tc.KV3 54
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v449 : Nat := CFSG.KD.Fi24Tc.KV3 55
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l450 : List Nat := [CFSG.KD.Fi24Tc.Pc.v448, CFSG.KD.Fi24Tc.Pc.v449]
theorem CFSG.KD.Fi24Tc.Pc.p448 : Nat.beq (runC AR SD 448 (ckL CFSG.KD.Fi24Tc.Pc.l450) 2 448 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v450 : Nat := CFSG.KD.Fi24Tc.KV3 56
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v451 : Nat := CFSG.KD.Fi24Tc.KV3 57
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l452 : List Nat := [CFSG.KD.Fi24Tc.Pc.v448, CFSG.KD.Fi24Tc.Pc.v449, CFSG.KD.Fi24Tc.Pc.v450, CFSG.KD.Fi24Tc.Pc.v451]
theorem CFSG.KD.Fi24Tc.Pc.p450 : Nat.beq (runC AR SD 448 (ckL CFSG.KD.Fi24Tc.Pc.l452) 2 450 CFSG.KD.Fi24Tc.Pc.l450) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v452 : Nat := CFSG.KD.Fi24Tc.KV3 58
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v453 : Nat := CFSG.KD.Fi24Tc.KV3 59
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l454 : List Nat := [CFSG.KD.Fi24Tc.Pc.v448, CFSG.KD.Fi24Tc.Pc.v449, CFSG.KD.Fi24Tc.Pc.v450, CFSG.KD.Fi24Tc.Pc.v451, CFSG.KD.Fi24Tc.Pc.v452, CFSG.KD.Fi24Tc.Pc.v453]
theorem CFSG.KD.Fi24Tc.Pc.p452 : Nat.beq (runC AR SD 448 (ckL CFSG.KD.Fi24Tc.Pc.l454) 2 452 CFSG.KD.Fi24Tc.Pc.l452) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f69 : Nat.beq (runC AR SD 448 (finC AR SD (nat_lit 69) 448 456) 2 454 CFSG.KD.Fi24Tc.Pc.l454) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk69 : chk (nat_lit 69) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 69) (lo := 448) (hi := 456) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 450) CFSG.KD.Fi24Tc.Pc.p448 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 452) CFSG.KD.Fi24Tc.Pc.p450 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 454) CFSG.KD.Fi24Tc.Pc.p452 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f69

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v456 : Nat := CFSG.KD.Fi24Tc.KV3 60
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v457 : Nat := CFSG.KD.Fi24Tc.KV3 61
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l458 : List Nat := [CFSG.KD.Fi24Tc.Pc.v456, CFSG.KD.Fi24Tc.Pc.v457]
theorem CFSG.KD.Fi24Tc.Pc.p456 : Nat.beq (runC AR SD 456 (ckL CFSG.KD.Fi24Tc.Pc.l458) 2 456 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v458 : Nat := CFSG.KD.Fi24Tc.KV3 62
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v459 : Nat := CFSG.KD.Fi24Tc.KV3 63
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l460 : List Nat := [CFSG.KD.Fi24Tc.Pc.v456, CFSG.KD.Fi24Tc.Pc.v457, CFSG.KD.Fi24Tc.Pc.v458, CFSG.KD.Fi24Tc.Pc.v459]
theorem CFSG.KD.Fi24Tc.Pc.p458 : Nat.beq (runC AR SD 456 (ckL CFSG.KD.Fi24Tc.Pc.l460) 2 458 CFSG.KD.Fi24Tc.Pc.l458) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v460 : Nat := CFSG.KD.Fi24Tc.KV3 64
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v461 : Nat := CFSG.KD.Fi24Tc.KV3 65
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l462 : List Nat := [CFSG.KD.Fi24Tc.Pc.v456, CFSG.KD.Fi24Tc.Pc.v457, CFSG.KD.Fi24Tc.Pc.v458, CFSG.KD.Fi24Tc.Pc.v459, CFSG.KD.Fi24Tc.Pc.v460, CFSG.KD.Fi24Tc.Pc.v461]
theorem CFSG.KD.Fi24Tc.Pc.p460 : Nat.beq (runC AR SD 456 (ckL CFSG.KD.Fi24Tc.Pc.l462) 2 460 CFSG.KD.Fi24Tc.Pc.l460) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f70 : Nat.beq (runC AR SD 456 (finC AR SD (nat_lit 70) 456 464) 2 462 CFSG.KD.Fi24Tc.Pc.l462) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk70 : chk (nat_lit 70) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 70) (lo := 456) (hi := 464) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 458) CFSG.KD.Fi24Tc.Pc.p456 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 460) CFSG.KD.Fi24Tc.Pc.p458 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 462) CFSG.KD.Fi24Tc.Pc.p460 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f70

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v464 : Nat := CFSG.KD.Fi24Tc.KV3 66
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v465 : Nat := CFSG.KD.Fi24Tc.KV3 67
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l466 : List Nat := [CFSG.KD.Fi24Tc.Pc.v464, CFSG.KD.Fi24Tc.Pc.v465]
theorem CFSG.KD.Fi24Tc.Pc.p464 : Nat.beq (runC AR SD 464 (ckL CFSG.KD.Fi24Tc.Pc.l466) 2 464 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v466 : Nat := CFSG.KD.Fi24Tc.KV3 68
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v467 : Nat := CFSG.KD.Fi24Tc.KV3 69
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l468 : List Nat := [CFSG.KD.Fi24Tc.Pc.v464, CFSG.KD.Fi24Tc.Pc.v465, CFSG.KD.Fi24Tc.Pc.v466, CFSG.KD.Fi24Tc.Pc.v467]
theorem CFSG.KD.Fi24Tc.Pc.p466 : Nat.beq (runC AR SD 464 (ckL CFSG.KD.Fi24Tc.Pc.l468) 2 466 CFSG.KD.Fi24Tc.Pc.l466) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v468 : Nat := CFSG.KD.Fi24Tc.KV3 70
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v469 : Nat := CFSG.KD.Fi24Tc.KV3 71
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l470 : List Nat := [CFSG.KD.Fi24Tc.Pc.v464, CFSG.KD.Fi24Tc.Pc.v465, CFSG.KD.Fi24Tc.Pc.v466, CFSG.KD.Fi24Tc.Pc.v467, CFSG.KD.Fi24Tc.Pc.v468, CFSG.KD.Fi24Tc.Pc.v469]
theorem CFSG.KD.Fi24Tc.Pc.p468 : Nat.beq (runC AR SD 464 (ckL CFSG.KD.Fi24Tc.Pc.l470) 2 468 CFSG.KD.Fi24Tc.Pc.l468) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f71 : Nat.beq (runC AR SD 464 (finC AR SD (nat_lit 71) 464 472) 2 470 CFSG.KD.Fi24Tc.Pc.l470) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk71 : chk (nat_lit 71) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 71) (lo := 464) (hi := 472) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 466) CFSG.KD.Fi24Tc.Pc.p464 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 468) CFSG.KD.Fi24Tc.Pc.p466 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 470) CFSG.KD.Fi24Tc.Pc.p468 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f71

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v472 : Nat := CFSG.KD.Fi24Tc.KV3 72
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v473 : Nat := CFSG.KD.Fi24Tc.KV3 73
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l474 : List Nat := [CFSG.KD.Fi24Tc.Pc.v472, CFSG.KD.Fi24Tc.Pc.v473]
theorem CFSG.KD.Fi24Tc.Pc.p472 : Nat.beq (runC AR SD 472 (ckL CFSG.KD.Fi24Tc.Pc.l474) 2 472 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v474 : Nat := CFSG.KD.Fi24Tc.KV3 74
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v475 : Nat := CFSG.KD.Fi24Tc.KV3 75
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l476 : List Nat := [CFSG.KD.Fi24Tc.Pc.v472, CFSG.KD.Fi24Tc.Pc.v473, CFSG.KD.Fi24Tc.Pc.v474, CFSG.KD.Fi24Tc.Pc.v475]
theorem CFSG.KD.Fi24Tc.Pc.p474 : Nat.beq (runC AR SD 472 (ckL CFSG.KD.Fi24Tc.Pc.l476) 2 474 CFSG.KD.Fi24Tc.Pc.l474) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v476 : Nat := CFSG.KD.Fi24Tc.KV3 76
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v477 : Nat := CFSG.KD.Fi24Tc.KV3 77
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l478 : List Nat := [CFSG.KD.Fi24Tc.Pc.v472, CFSG.KD.Fi24Tc.Pc.v473, CFSG.KD.Fi24Tc.Pc.v474, CFSG.KD.Fi24Tc.Pc.v475, CFSG.KD.Fi24Tc.Pc.v476, CFSG.KD.Fi24Tc.Pc.v477]
theorem CFSG.KD.Fi24Tc.Pc.p476 : Nat.beq (runC AR SD 472 (ckL CFSG.KD.Fi24Tc.Pc.l478) 2 476 CFSG.KD.Fi24Tc.Pc.l476) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f72 : Nat.beq (runC AR SD 472 (finC AR SD (nat_lit 72) 472 480) 2 478 CFSG.KD.Fi24Tc.Pc.l478) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk72 : chk (nat_lit 72) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 72) (lo := 472) (hi := 480) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 474) CFSG.KD.Fi24Tc.Pc.p472 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 476) CFSG.KD.Fi24Tc.Pc.p474 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 478) CFSG.KD.Fi24Tc.Pc.p476 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f72

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v480 : Nat := CFSG.KD.Fi24Tc.KV3 78
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v481 : Nat := CFSG.KD.Fi24Tc.KV3 79
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l482 : List Nat := [CFSG.KD.Fi24Tc.Pc.v480, CFSG.KD.Fi24Tc.Pc.v481]
theorem CFSG.KD.Fi24Tc.Pc.p480 : Nat.beq (runC AR SD 480 (ckL CFSG.KD.Fi24Tc.Pc.l482) 2 480 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v482 : Nat := CFSG.KD.Fi24Tc.KV3 80
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v483 : Nat := CFSG.KD.Fi24Tc.KV3 81
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l484 : List Nat := [CFSG.KD.Fi24Tc.Pc.v480, CFSG.KD.Fi24Tc.Pc.v481, CFSG.KD.Fi24Tc.Pc.v482, CFSG.KD.Fi24Tc.Pc.v483]
theorem CFSG.KD.Fi24Tc.Pc.p482 : Nat.beq (runC AR SD 480 (ckL CFSG.KD.Fi24Tc.Pc.l484) 2 482 CFSG.KD.Fi24Tc.Pc.l482) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v484 : Nat := CFSG.KD.Fi24Tc.KV3 82
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v485 : Nat := CFSG.KD.Fi24Tc.KV3 83
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l486 : List Nat := [CFSG.KD.Fi24Tc.Pc.v480, CFSG.KD.Fi24Tc.Pc.v481, CFSG.KD.Fi24Tc.Pc.v482, CFSG.KD.Fi24Tc.Pc.v483, CFSG.KD.Fi24Tc.Pc.v484, CFSG.KD.Fi24Tc.Pc.v485]
theorem CFSG.KD.Fi24Tc.Pc.p484 : Nat.beq (runC AR SD 480 (ckL CFSG.KD.Fi24Tc.Pc.l486) 2 484 CFSG.KD.Fi24Tc.Pc.l484) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f73 : Nat.beq (runC AR SD 480 (finC AR SD (nat_lit 73) 480 487) 1 486 CFSG.KD.Fi24Tc.Pc.l486) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk73 : chk (nat_lit 73) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 73) (lo := 480) (hi := 487) (m := 7) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 7) (m2 := 5) (j2 := 482) CFSG.KD.Fi24Tc.Pc.p480 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 484) CFSG.KD.Fi24Tc.Pc.p482 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 486) CFSG.KD.Fi24Tc.Pc.p484 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f73

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v487 : Nat := CFSG.KD.Fi24Tc.KV3 84
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v488 : Nat := CFSG.KD.Fi24Tc.KV3 85
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l489 : List Nat := [CFSG.KD.Fi24Tc.Pc.v487, CFSG.KD.Fi24Tc.Pc.v488]
theorem CFSG.KD.Fi24Tc.Pc.p487 : Nat.beq (runC AR SD 487 (ckL CFSG.KD.Fi24Tc.Pc.l489) 2 487 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v489 : Nat := CFSG.KD.Fi24Tc.KV3 86
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v490 : Nat := CFSG.KD.Fi24Tc.KV3 87
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l491 : List Nat := [CFSG.KD.Fi24Tc.Pc.v487, CFSG.KD.Fi24Tc.Pc.v488, CFSG.KD.Fi24Tc.Pc.v489, CFSG.KD.Fi24Tc.Pc.v490]
theorem CFSG.KD.Fi24Tc.Pc.p489 : Nat.beq (runC AR SD 487 (ckL CFSG.KD.Fi24Tc.Pc.l491) 2 489 CFSG.KD.Fi24Tc.Pc.l489) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v491 : Nat := CFSG.KD.Fi24Tc.KV3 88
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v492 : Nat := CFSG.KD.Fi24Tc.KV3 89
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l493 : List Nat := [CFSG.KD.Fi24Tc.Pc.v487, CFSG.KD.Fi24Tc.Pc.v488, CFSG.KD.Fi24Tc.Pc.v489, CFSG.KD.Fi24Tc.Pc.v490, CFSG.KD.Fi24Tc.Pc.v491, CFSG.KD.Fi24Tc.Pc.v492]
theorem CFSG.KD.Fi24Tc.Pc.p491 : Nat.beq (runC AR SD 487 (ckL CFSG.KD.Fi24Tc.Pc.l493) 2 491 CFSG.KD.Fi24Tc.Pc.l491) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f74 : Nat.beq (runC AR SD 487 (finC AR SD (nat_lit 74) 487 495) 2 493 CFSG.KD.Fi24Tc.Pc.l493) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk74 : chk (nat_lit 74) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 74) (lo := 487) (hi := 495) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 489) CFSG.KD.Fi24Tc.Pc.p487 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 491) CFSG.KD.Fi24Tc.Pc.p489 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 493) CFSG.KD.Fi24Tc.Pc.p491 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f74

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v495 : Nat := CFSG.KD.Fi24Tc.KV3 90
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v496 : Nat := CFSG.KD.Fi24Tc.KV3 91
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l497 : List Nat := [CFSG.KD.Fi24Tc.Pc.v495, CFSG.KD.Fi24Tc.Pc.v496]
theorem CFSG.KD.Fi24Tc.Pc.p495 : Nat.beq (runC AR SD 495 (ckL CFSG.KD.Fi24Tc.Pc.l497) 2 495 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v497 : Nat := CFSG.KD.Fi24Tc.KV3 92
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v498 : Nat := CFSG.KD.Fi24Tc.KV3 93
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l499 : List Nat := [CFSG.KD.Fi24Tc.Pc.v495, CFSG.KD.Fi24Tc.Pc.v496, CFSG.KD.Fi24Tc.Pc.v497, CFSG.KD.Fi24Tc.Pc.v498]
theorem CFSG.KD.Fi24Tc.Pc.p497 : Nat.beq (runC AR SD 495 (ckL CFSG.KD.Fi24Tc.Pc.l499) 2 497 CFSG.KD.Fi24Tc.Pc.l497) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v499 : Nat := CFSG.KD.Fi24Tc.KV3 94
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v500 : Nat := CFSG.KD.Fi24Tc.KV3 95
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l501 : List Nat := [CFSG.KD.Fi24Tc.Pc.v495, CFSG.KD.Fi24Tc.Pc.v496, CFSG.KD.Fi24Tc.Pc.v497, CFSG.KD.Fi24Tc.Pc.v498, CFSG.KD.Fi24Tc.Pc.v499, CFSG.KD.Fi24Tc.Pc.v500]
theorem CFSG.KD.Fi24Tc.Pc.p499 : Nat.beq (runC AR SD 495 (ckL CFSG.KD.Fi24Tc.Pc.l501) 2 499 CFSG.KD.Fi24Tc.Pc.l499) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f75 : Nat.beq (runC AR SD 495 (finC AR SD (nat_lit 75) 495 503) 2 501 CFSG.KD.Fi24Tc.Pc.l501) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk75 : chk (nat_lit 75) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 75) (lo := 495) (hi := 503) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 497) CFSG.KD.Fi24Tc.Pc.p495 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 499) CFSG.KD.Fi24Tc.Pc.p497 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 501) CFSG.KD.Fi24Tc.Pc.p499 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f75

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v503 : Nat := CFSG.KD.Fi24Tc.KV3 96
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v504 : Nat := CFSG.KD.Fi24Tc.KV3 97
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l505 : List Nat := [CFSG.KD.Fi24Tc.Pc.v503, CFSG.KD.Fi24Tc.Pc.v504]
theorem CFSG.KD.Fi24Tc.Pc.p503 : Nat.beq (runC AR SD 503 (ckL CFSG.KD.Fi24Tc.Pc.l505) 2 503 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v505 : Nat := CFSG.KD.Fi24Tc.KV3 98
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v506 : Nat := CFSG.KD.Fi24Tc.KV3 99
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l507 : List Nat := [CFSG.KD.Fi24Tc.Pc.v503, CFSG.KD.Fi24Tc.Pc.v504, CFSG.KD.Fi24Tc.Pc.v505, CFSG.KD.Fi24Tc.Pc.v506]
theorem CFSG.KD.Fi24Tc.Pc.p505 : Nat.beq (runC AR SD 503 (ckL CFSG.KD.Fi24Tc.Pc.l507) 2 505 CFSG.KD.Fi24Tc.Pc.l505) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v507 : Nat := CFSG.KD.Fi24Tc.KV3 100
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v508 : Nat := CFSG.KD.Fi24Tc.KV3 101
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l509 : List Nat := [CFSG.KD.Fi24Tc.Pc.v503, CFSG.KD.Fi24Tc.Pc.v504, CFSG.KD.Fi24Tc.Pc.v505, CFSG.KD.Fi24Tc.Pc.v506, CFSG.KD.Fi24Tc.Pc.v507, CFSG.KD.Fi24Tc.Pc.v508]
theorem CFSG.KD.Fi24Tc.Pc.p507 : Nat.beq (runC AR SD 503 (ckL CFSG.KD.Fi24Tc.Pc.l509) 2 507 CFSG.KD.Fi24Tc.Pc.l507) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f76 : Nat.beq (runC AR SD 503 (finC AR SD (nat_lit 76) 503 511) 2 509 CFSG.KD.Fi24Tc.Pc.l509) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk76 : chk (nat_lit 76) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 76) (lo := 503) (hi := 511) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 505) CFSG.KD.Fi24Tc.Pc.p503 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 507) CFSG.KD.Fi24Tc.Pc.p505 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 509) CFSG.KD.Fi24Tc.Pc.p507 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f76

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v511 : Nat := CFSG.KD.Fi24Tc.KV3 102
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v512 : Nat := CFSG.KD.Fi24Tc.KV3 103
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l513 : List Nat := [CFSG.KD.Fi24Tc.Pc.v511, CFSG.KD.Fi24Tc.Pc.v512]
theorem CFSG.KD.Fi24Tc.Pc.p511 : Nat.beq (runC AR SD 511 (ckL CFSG.KD.Fi24Tc.Pc.l513) 2 511 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v513 : Nat := CFSG.KD.Fi24Tc.KV3 104
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v514 : Nat := CFSG.KD.Fi24Tc.KV3 105
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l515 : List Nat := [CFSG.KD.Fi24Tc.Pc.v511, CFSG.KD.Fi24Tc.Pc.v512, CFSG.KD.Fi24Tc.Pc.v513, CFSG.KD.Fi24Tc.Pc.v514]
theorem CFSG.KD.Fi24Tc.Pc.p513 : Nat.beq (runC AR SD 511 (ckL CFSG.KD.Fi24Tc.Pc.l515) 2 513 CFSG.KD.Fi24Tc.Pc.l513) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v515 : Nat := CFSG.KD.Fi24Tc.KV3 106
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v516 : Nat := CFSG.KD.Fi24Tc.KV3 107
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l517 : List Nat := [CFSG.KD.Fi24Tc.Pc.v511, CFSG.KD.Fi24Tc.Pc.v512, CFSG.KD.Fi24Tc.Pc.v513, CFSG.KD.Fi24Tc.Pc.v514, CFSG.KD.Fi24Tc.Pc.v515, CFSG.KD.Fi24Tc.Pc.v516]
theorem CFSG.KD.Fi24Tc.Pc.p515 : Nat.beq (runC AR SD 511 (ckL CFSG.KD.Fi24Tc.Pc.l517) 2 515 CFSG.KD.Fi24Tc.Pc.l515) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f77 : Nat.beq (runC AR SD 511 (finC AR SD (nat_lit 77) 511 519) 2 517 CFSG.KD.Fi24Tc.Pc.l517) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk77 : chk (nat_lit 77) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 77) (lo := 511) (hi := 519) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 513) CFSG.KD.Fi24Tc.Pc.p511 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 515) CFSG.KD.Fi24Tc.Pc.p513 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 517) CFSG.KD.Fi24Tc.Pc.p515 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f77

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v519 : Nat := CFSG.KD.Fi24Tc.KV3 108
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v520 : Nat := CFSG.KD.Fi24Tc.KV3 109
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l521 : List Nat := [CFSG.KD.Fi24Tc.Pc.v519, CFSG.KD.Fi24Tc.Pc.v520]
theorem CFSG.KD.Fi24Tc.Pc.p519 : Nat.beq (runC AR SD 519 (ckL CFSG.KD.Fi24Tc.Pc.l521) 2 519 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v521 : Nat := CFSG.KD.Fi24Tc.KV3 110
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v522 : Nat := CFSG.KD.Fi24Tc.KV3 111
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l523 : List Nat := [CFSG.KD.Fi24Tc.Pc.v519, CFSG.KD.Fi24Tc.Pc.v520, CFSG.KD.Fi24Tc.Pc.v521, CFSG.KD.Fi24Tc.Pc.v522]
theorem CFSG.KD.Fi24Tc.Pc.p521 : Nat.beq (runC AR SD 519 (ckL CFSG.KD.Fi24Tc.Pc.l523) 2 521 CFSG.KD.Fi24Tc.Pc.l521) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v523 : Nat := CFSG.KD.Fi24Tc.KV3 112
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v524 : Nat := CFSG.KD.Fi24Tc.KV3 113
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l525 : List Nat := [CFSG.KD.Fi24Tc.Pc.v519, CFSG.KD.Fi24Tc.Pc.v520, CFSG.KD.Fi24Tc.Pc.v521, CFSG.KD.Fi24Tc.Pc.v522, CFSG.KD.Fi24Tc.Pc.v523, CFSG.KD.Fi24Tc.Pc.v524]
theorem CFSG.KD.Fi24Tc.Pc.p523 : Nat.beq (runC AR SD 519 (ckL CFSG.KD.Fi24Tc.Pc.l525) 2 523 CFSG.KD.Fi24Tc.Pc.l523) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f78 : Nat.beq (runC AR SD 519 (finC AR SD (nat_lit 78) 519 527) 2 525 CFSG.KD.Fi24Tc.Pc.l525) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk78 : chk (nat_lit 78) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 78) (lo := 519) (hi := 527) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 521) CFSG.KD.Fi24Tc.Pc.p519 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 523) CFSG.KD.Fi24Tc.Pc.p521 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 525) CFSG.KD.Fi24Tc.Pc.p523 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f78

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v527 : Nat := CFSG.KD.Fi24Tc.KV3 114
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v528 : Nat := CFSG.KD.Fi24Tc.KV3 115
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l529 : List Nat := [CFSG.KD.Fi24Tc.Pc.v527, CFSG.KD.Fi24Tc.Pc.v528]
theorem CFSG.KD.Fi24Tc.Pc.p527 : Nat.beq (runC AR SD 527 (ckL CFSG.KD.Fi24Tc.Pc.l529) 2 527 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v529 : Nat := CFSG.KD.Fi24Tc.KV3 116
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v530 : Nat := CFSG.KD.Fi24Tc.KV3 117
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l531 : List Nat := [CFSG.KD.Fi24Tc.Pc.v527, CFSG.KD.Fi24Tc.Pc.v528, CFSG.KD.Fi24Tc.Pc.v529, CFSG.KD.Fi24Tc.Pc.v530]
theorem CFSG.KD.Fi24Tc.Pc.p529 : Nat.beq (runC AR SD 527 (ckL CFSG.KD.Fi24Tc.Pc.l531) 2 529 CFSG.KD.Fi24Tc.Pc.l529) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v531 : Nat := CFSG.KD.Fi24Tc.KV3 118
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v532 : Nat := CFSG.KD.Fi24Tc.KV3 119
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l533 : List Nat := [CFSG.KD.Fi24Tc.Pc.v527, CFSG.KD.Fi24Tc.Pc.v528, CFSG.KD.Fi24Tc.Pc.v529, CFSG.KD.Fi24Tc.Pc.v530, CFSG.KD.Fi24Tc.Pc.v531, CFSG.KD.Fi24Tc.Pc.v532]
theorem CFSG.KD.Fi24Tc.Pc.p531 : Nat.beq (runC AR SD 527 (ckL CFSG.KD.Fi24Tc.Pc.l533) 2 531 CFSG.KD.Fi24Tc.Pc.l531) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f79 : Nat.beq (runC AR SD 527 (finC AR SD (nat_lit 79) 527 535) 2 533 CFSG.KD.Fi24Tc.Pc.l533) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk79 : chk (nat_lit 79) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 79) (lo := 527) (hi := 535) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 529) CFSG.KD.Fi24Tc.Pc.p527 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 531) CFSG.KD.Fi24Tc.Pc.p529 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 533) CFSG.KD.Fi24Tc.Pc.p531 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f79

end
