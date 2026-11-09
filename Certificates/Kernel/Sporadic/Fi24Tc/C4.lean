module

public import Certificates.Kernel.Sporadic.Fi24Tc.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Tc KV4 "Certificates/Kernel/Sporadic/Fi24Tc/data/v4.bin" 152491 4 18298920 14864402890524302908

public section

open CFSG.KD.Fi24Tc CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v535 : Nat := CFSG.KD.Fi24Tc.KV4 0
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v536 : Nat := CFSG.KD.Fi24Tc.KV4 1
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l537 : List Nat := [CFSG.KD.Fi24Tc.Pc.v535, CFSG.KD.Fi24Tc.Pc.v536]
theorem CFSG.KD.Fi24Tc.Pc.p535 : Nat.beq (runC AR SD 535 (ckL CFSG.KD.Fi24Tc.Pc.l537) 2 535 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v537 : Nat := CFSG.KD.Fi24Tc.KV4 2
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v538 : Nat := CFSG.KD.Fi24Tc.KV4 3
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l539 : List Nat := [CFSG.KD.Fi24Tc.Pc.v535, CFSG.KD.Fi24Tc.Pc.v536, CFSG.KD.Fi24Tc.Pc.v537, CFSG.KD.Fi24Tc.Pc.v538]
theorem CFSG.KD.Fi24Tc.Pc.p537 : Nat.beq (runC AR SD 535 (ckL CFSG.KD.Fi24Tc.Pc.l539) 2 537 CFSG.KD.Fi24Tc.Pc.l537) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v539 : Nat := CFSG.KD.Fi24Tc.KV4 4
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v540 : Nat := CFSG.KD.Fi24Tc.KV4 5
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l541 : List Nat := [CFSG.KD.Fi24Tc.Pc.v535, CFSG.KD.Fi24Tc.Pc.v536, CFSG.KD.Fi24Tc.Pc.v537, CFSG.KD.Fi24Tc.Pc.v538, CFSG.KD.Fi24Tc.Pc.v539, CFSG.KD.Fi24Tc.Pc.v540]
theorem CFSG.KD.Fi24Tc.Pc.p539 : Nat.beq (runC AR SD 535 (ckL CFSG.KD.Fi24Tc.Pc.l541) 2 539 CFSG.KD.Fi24Tc.Pc.l539) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f80 : Nat.beq (runC AR SD 535 (finC AR SD (nat_lit 80) 535 543) 2 541 CFSG.KD.Fi24Tc.Pc.l541) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk80 : chk (nat_lit 80) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 80) (lo := 535) (hi := 543) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 537) CFSG.KD.Fi24Tc.Pc.p535 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 539) CFSG.KD.Fi24Tc.Pc.p537 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 541) CFSG.KD.Fi24Tc.Pc.p539 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f80

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v543 : Nat := CFSG.KD.Fi24Tc.KV4 6
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v544 : Nat := CFSG.KD.Fi24Tc.KV4 7
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l545 : List Nat := [CFSG.KD.Fi24Tc.Pc.v543, CFSG.KD.Fi24Tc.Pc.v544]
theorem CFSG.KD.Fi24Tc.Pc.p543 : Nat.beq (runC AR SD 543 (ckL CFSG.KD.Fi24Tc.Pc.l545) 2 543 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v545 : Nat := CFSG.KD.Fi24Tc.KV4 8
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v546 : Nat := CFSG.KD.Fi24Tc.KV4 9
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l547 : List Nat := [CFSG.KD.Fi24Tc.Pc.v543, CFSG.KD.Fi24Tc.Pc.v544, CFSG.KD.Fi24Tc.Pc.v545, CFSG.KD.Fi24Tc.Pc.v546]
theorem CFSG.KD.Fi24Tc.Pc.p545 : Nat.beq (runC AR SD 543 (ckL CFSG.KD.Fi24Tc.Pc.l547) 2 545 CFSG.KD.Fi24Tc.Pc.l545) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v547 : Nat := CFSG.KD.Fi24Tc.KV4 10
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v548 : Nat := CFSG.KD.Fi24Tc.KV4 11
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l549 : List Nat := [CFSG.KD.Fi24Tc.Pc.v543, CFSG.KD.Fi24Tc.Pc.v544, CFSG.KD.Fi24Tc.Pc.v545, CFSG.KD.Fi24Tc.Pc.v546, CFSG.KD.Fi24Tc.Pc.v547, CFSG.KD.Fi24Tc.Pc.v548]
theorem CFSG.KD.Fi24Tc.Pc.p547 : Nat.beq (runC AR SD 543 (ckL CFSG.KD.Fi24Tc.Pc.l549) 2 547 CFSG.KD.Fi24Tc.Pc.l547) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f81 : Nat.beq (runC AR SD 543 (finC AR SD (nat_lit 81) 543 551) 2 549 CFSG.KD.Fi24Tc.Pc.l549) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk81 : chk (nat_lit 81) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 81) (lo := 543) (hi := 551) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 545) CFSG.KD.Fi24Tc.Pc.p543 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 547) CFSG.KD.Fi24Tc.Pc.p545 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 549) CFSG.KD.Fi24Tc.Pc.p547 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f81

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v551 : Nat := CFSG.KD.Fi24Tc.KV4 12
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v552 : Nat := CFSG.KD.Fi24Tc.KV4 13
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l553 : List Nat := [CFSG.KD.Fi24Tc.Pc.v551, CFSG.KD.Fi24Tc.Pc.v552]
theorem CFSG.KD.Fi24Tc.Pc.p551 : Nat.beq (runC AR SD 551 (ckL CFSG.KD.Fi24Tc.Pc.l553) 2 551 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v553 : Nat := CFSG.KD.Fi24Tc.KV4 14
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v554 : Nat := CFSG.KD.Fi24Tc.KV4 15
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l555 : List Nat := [CFSG.KD.Fi24Tc.Pc.v551, CFSG.KD.Fi24Tc.Pc.v552, CFSG.KD.Fi24Tc.Pc.v553, CFSG.KD.Fi24Tc.Pc.v554]
theorem CFSG.KD.Fi24Tc.Pc.p553 : Nat.beq (runC AR SD 551 (ckL CFSG.KD.Fi24Tc.Pc.l555) 2 553 CFSG.KD.Fi24Tc.Pc.l553) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v555 : Nat := CFSG.KD.Fi24Tc.KV4 16
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v556 : Nat := CFSG.KD.Fi24Tc.KV4 17
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l557 : List Nat := [CFSG.KD.Fi24Tc.Pc.v551, CFSG.KD.Fi24Tc.Pc.v552, CFSG.KD.Fi24Tc.Pc.v553, CFSG.KD.Fi24Tc.Pc.v554, CFSG.KD.Fi24Tc.Pc.v555, CFSG.KD.Fi24Tc.Pc.v556]
theorem CFSG.KD.Fi24Tc.Pc.p555 : Nat.beq (runC AR SD 551 (ckL CFSG.KD.Fi24Tc.Pc.l557) 2 555 CFSG.KD.Fi24Tc.Pc.l555) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f82 : Nat.beq (runC AR SD 551 (finC AR SD (nat_lit 82) 551 559) 2 557 CFSG.KD.Fi24Tc.Pc.l557) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk82 : chk (nat_lit 82) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 82) (lo := 551) (hi := 559) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 553) CFSG.KD.Fi24Tc.Pc.p551 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 555) CFSG.KD.Fi24Tc.Pc.p553 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 557) CFSG.KD.Fi24Tc.Pc.p555 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f82

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v559 : Nat := CFSG.KD.Fi24Tc.KV4 18
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v560 : Nat := CFSG.KD.Fi24Tc.KV4 19
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l561 : List Nat := [CFSG.KD.Fi24Tc.Pc.v559, CFSG.KD.Fi24Tc.Pc.v560]
theorem CFSG.KD.Fi24Tc.Pc.p559 : Nat.beq (runC AR SD 559 (ckL CFSG.KD.Fi24Tc.Pc.l561) 2 559 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v561 : Nat := CFSG.KD.Fi24Tc.KV4 20
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v562 : Nat := CFSG.KD.Fi24Tc.KV4 21
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l563 : List Nat := [CFSG.KD.Fi24Tc.Pc.v559, CFSG.KD.Fi24Tc.Pc.v560, CFSG.KD.Fi24Tc.Pc.v561, CFSG.KD.Fi24Tc.Pc.v562]
theorem CFSG.KD.Fi24Tc.Pc.p561 : Nat.beq (runC AR SD 559 (ckL CFSG.KD.Fi24Tc.Pc.l563) 2 561 CFSG.KD.Fi24Tc.Pc.l561) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v563 : Nat := CFSG.KD.Fi24Tc.KV4 22
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v564 : Nat := CFSG.KD.Fi24Tc.KV4 23
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l565 : List Nat := [CFSG.KD.Fi24Tc.Pc.v559, CFSG.KD.Fi24Tc.Pc.v560, CFSG.KD.Fi24Tc.Pc.v561, CFSG.KD.Fi24Tc.Pc.v562, CFSG.KD.Fi24Tc.Pc.v563, CFSG.KD.Fi24Tc.Pc.v564]
theorem CFSG.KD.Fi24Tc.Pc.p563 : Nat.beq (runC AR SD 559 (ckL CFSG.KD.Fi24Tc.Pc.l565) 2 563 CFSG.KD.Fi24Tc.Pc.l563) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f83 : Nat.beq (runC AR SD 559 (finC AR SD (nat_lit 83) 559 567) 2 565 CFSG.KD.Fi24Tc.Pc.l565) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk83 : chk (nat_lit 83) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 83) (lo := 559) (hi := 567) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 561) CFSG.KD.Fi24Tc.Pc.p559 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 563) CFSG.KD.Fi24Tc.Pc.p561 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 565) CFSG.KD.Fi24Tc.Pc.p563 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f83

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v567 : Nat := CFSG.KD.Fi24Tc.KV4 24
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v568 : Nat := CFSG.KD.Fi24Tc.KV4 25
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l569 : List Nat := [CFSG.KD.Fi24Tc.Pc.v567, CFSG.KD.Fi24Tc.Pc.v568]
theorem CFSG.KD.Fi24Tc.Pc.p567 : Nat.beq (runC AR SD 567 (ckL CFSG.KD.Fi24Tc.Pc.l569) 2 567 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v569 : Nat := CFSG.KD.Fi24Tc.KV4 26
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v570 : Nat := CFSG.KD.Fi24Tc.KV4 27
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l571 : List Nat := [CFSG.KD.Fi24Tc.Pc.v567, CFSG.KD.Fi24Tc.Pc.v568, CFSG.KD.Fi24Tc.Pc.v569, CFSG.KD.Fi24Tc.Pc.v570]
theorem CFSG.KD.Fi24Tc.Pc.p569 : Nat.beq (runC AR SD 567 (ckL CFSG.KD.Fi24Tc.Pc.l571) 2 569 CFSG.KD.Fi24Tc.Pc.l569) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v571 : Nat := CFSG.KD.Fi24Tc.KV4 28
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v572 : Nat := CFSG.KD.Fi24Tc.KV4 29
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l573 : List Nat := [CFSG.KD.Fi24Tc.Pc.v567, CFSG.KD.Fi24Tc.Pc.v568, CFSG.KD.Fi24Tc.Pc.v569, CFSG.KD.Fi24Tc.Pc.v570, CFSG.KD.Fi24Tc.Pc.v571, CFSG.KD.Fi24Tc.Pc.v572]
theorem CFSG.KD.Fi24Tc.Pc.p571 : Nat.beq (runC AR SD 567 (ckL CFSG.KD.Fi24Tc.Pc.l573) 2 571 CFSG.KD.Fi24Tc.Pc.l571) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f84 : Nat.beq (runC AR SD 567 (finC AR SD (nat_lit 84) 567 575) 2 573 CFSG.KD.Fi24Tc.Pc.l573) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk84 : chk (nat_lit 84) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 84) (lo := 567) (hi := 575) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 569) CFSG.KD.Fi24Tc.Pc.p567 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 571) CFSG.KD.Fi24Tc.Pc.p569 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 573) CFSG.KD.Fi24Tc.Pc.p571 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f84

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v575 : Nat := CFSG.KD.Fi24Tc.KV4 30
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v576 : Nat := CFSG.KD.Fi24Tc.KV4 31
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l577 : List Nat := [CFSG.KD.Fi24Tc.Pc.v575, CFSG.KD.Fi24Tc.Pc.v576]
theorem CFSG.KD.Fi24Tc.Pc.p575 : Nat.beq (runC AR SD 575 (ckL CFSG.KD.Fi24Tc.Pc.l577) 2 575 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v577 : Nat := CFSG.KD.Fi24Tc.KV4 32
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v578 : Nat := CFSG.KD.Fi24Tc.KV4 33
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l579 : List Nat := [CFSG.KD.Fi24Tc.Pc.v575, CFSG.KD.Fi24Tc.Pc.v576, CFSG.KD.Fi24Tc.Pc.v577, CFSG.KD.Fi24Tc.Pc.v578]
theorem CFSG.KD.Fi24Tc.Pc.p577 : Nat.beq (runC AR SD 575 (ckL CFSG.KD.Fi24Tc.Pc.l579) 2 577 CFSG.KD.Fi24Tc.Pc.l577) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v579 : Nat := CFSG.KD.Fi24Tc.KV4 34
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v580 : Nat := CFSG.KD.Fi24Tc.KV4 35
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l581 : List Nat := [CFSG.KD.Fi24Tc.Pc.v575, CFSG.KD.Fi24Tc.Pc.v576, CFSG.KD.Fi24Tc.Pc.v577, CFSG.KD.Fi24Tc.Pc.v578, CFSG.KD.Fi24Tc.Pc.v579, CFSG.KD.Fi24Tc.Pc.v580]
theorem CFSG.KD.Fi24Tc.Pc.p579 : Nat.beq (runC AR SD 575 (ckL CFSG.KD.Fi24Tc.Pc.l581) 2 579 CFSG.KD.Fi24Tc.Pc.l579) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f85 : Nat.beq (runC AR SD 575 (finC AR SD (nat_lit 85) 575 583) 2 581 CFSG.KD.Fi24Tc.Pc.l581) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk85 : chk (nat_lit 85) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 85) (lo := 575) (hi := 583) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 577) CFSG.KD.Fi24Tc.Pc.p575 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 579) CFSG.KD.Fi24Tc.Pc.p577 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 581) CFSG.KD.Fi24Tc.Pc.p579 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f85

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v583 : Nat := CFSG.KD.Fi24Tc.KV4 36
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v584 : Nat := CFSG.KD.Fi24Tc.KV4 37
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l585 : List Nat := [CFSG.KD.Fi24Tc.Pc.v583, CFSG.KD.Fi24Tc.Pc.v584]
theorem CFSG.KD.Fi24Tc.Pc.p583 : Nat.beq (runC AR SD 583 (ckL CFSG.KD.Fi24Tc.Pc.l585) 2 583 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v585 : Nat := CFSG.KD.Fi24Tc.KV4 38
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v586 : Nat := CFSG.KD.Fi24Tc.KV4 39
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l587 : List Nat := [CFSG.KD.Fi24Tc.Pc.v583, CFSG.KD.Fi24Tc.Pc.v584, CFSG.KD.Fi24Tc.Pc.v585, CFSG.KD.Fi24Tc.Pc.v586]
theorem CFSG.KD.Fi24Tc.Pc.p585 : Nat.beq (runC AR SD 583 (ckL CFSG.KD.Fi24Tc.Pc.l587) 2 585 CFSG.KD.Fi24Tc.Pc.l585) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v587 : Nat := CFSG.KD.Fi24Tc.KV4 40
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v588 : Nat := CFSG.KD.Fi24Tc.KV4 41
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l589 : List Nat := [CFSG.KD.Fi24Tc.Pc.v583, CFSG.KD.Fi24Tc.Pc.v584, CFSG.KD.Fi24Tc.Pc.v585, CFSG.KD.Fi24Tc.Pc.v586, CFSG.KD.Fi24Tc.Pc.v587, CFSG.KD.Fi24Tc.Pc.v588]
theorem CFSG.KD.Fi24Tc.Pc.p587 : Nat.beq (runC AR SD 583 (ckL CFSG.KD.Fi24Tc.Pc.l589) 2 587 CFSG.KD.Fi24Tc.Pc.l587) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f86 : Nat.beq (runC AR SD 583 (finC AR SD (nat_lit 86) 583 591) 2 589 CFSG.KD.Fi24Tc.Pc.l589) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk86 : chk (nat_lit 86) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 86) (lo := 583) (hi := 591) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 585) CFSG.KD.Fi24Tc.Pc.p583 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 587) CFSG.KD.Fi24Tc.Pc.p585 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 589) CFSG.KD.Fi24Tc.Pc.p587 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f86

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v591 : Nat := CFSG.KD.Fi24Tc.KV4 42
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v592 : Nat := CFSG.KD.Fi24Tc.KV4 43
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l593 : List Nat := [CFSG.KD.Fi24Tc.Pc.v591, CFSG.KD.Fi24Tc.Pc.v592]
theorem CFSG.KD.Fi24Tc.Pc.p591 : Nat.beq (runC AR SD 591 (ckL CFSG.KD.Fi24Tc.Pc.l593) 2 591 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v593 : Nat := CFSG.KD.Fi24Tc.KV4 44
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v594 : Nat := CFSG.KD.Fi24Tc.KV4 45
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l595 : List Nat := [CFSG.KD.Fi24Tc.Pc.v591, CFSG.KD.Fi24Tc.Pc.v592, CFSG.KD.Fi24Tc.Pc.v593, CFSG.KD.Fi24Tc.Pc.v594]
theorem CFSG.KD.Fi24Tc.Pc.p593 : Nat.beq (runC AR SD 591 (ckL CFSG.KD.Fi24Tc.Pc.l595) 2 593 CFSG.KD.Fi24Tc.Pc.l593) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v595 : Nat := CFSG.KD.Fi24Tc.KV4 46
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v596 : Nat := CFSG.KD.Fi24Tc.KV4 47
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l597 : List Nat := [CFSG.KD.Fi24Tc.Pc.v591, CFSG.KD.Fi24Tc.Pc.v592, CFSG.KD.Fi24Tc.Pc.v593, CFSG.KD.Fi24Tc.Pc.v594, CFSG.KD.Fi24Tc.Pc.v595, CFSG.KD.Fi24Tc.Pc.v596]
theorem CFSG.KD.Fi24Tc.Pc.p595 : Nat.beq (runC AR SD 591 (ckL CFSG.KD.Fi24Tc.Pc.l597) 2 595 CFSG.KD.Fi24Tc.Pc.l595) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f87 : Nat.beq (runC AR SD 591 (finC AR SD (nat_lit 87) 591 599) 2 597 CFSG.KD.Fi24Tc.Pc.l597) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk87 : chk (nat_lit 87) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 87) (lo := 591) (hi := 599) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 593) CFSG.KD.Fi24Tc.Pc.p591 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 595) CFSG.KD.Fi24Tc.Pc.p593 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 597) CFSG.KD.Fi24Tc.Pc.p595 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f87

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v599 : Nat := CFSG.KD.Fi24Tc.KV4 48
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v600 : Nat := CFSG.KD.Fi24Tc.KV4 49
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l601 : List Nat := [CFSG.KD.Fi24Tc.Pc.v599, CFSG.KD.Fi24Tc.Pc.v600]
theorem CFSG.KD.Fi24Tc.Pc.p599 : Nat.beq (runC AR SD 599 (ckL CFSG.KD.Fi24Tc.Pc.l601) 2 599 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v601 : Nat := CFSG.KD.Fi24Tc.KV4 50
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v602 : Nat := CFSG.KD.Fi24Tc.KV4 51
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l603 : List Nat := [CFSG.KD.Fi24Tc.Pc.v599, CFSG.KD.Fi24Tc.Pc.v600, CFSG.KD.Fi24Tc.Pc.v601, CFSG.KD.Fi24Tc.Pc.v602]
theorem CFSG.KD.Fi24Tc.Pc.p601 : Nat.beq (runC AR SD 599 (ckL CFSG.KD.Fi24Tc.Pc.l603) 2 601 CFSG.KD.Fi24Tc.Pc.l601) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v603 : Nat := CFSG.KD.Fi24Tc.KV4 52
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v604 : Nat := CFSG.KD.Fi24Tc.KV4 53
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l605 : List Nat := [CFSG.KD.Fi24Tc.Pc.v599, CFSG.KD.Fi24Tc.Pc.v600, CFSG.KD.Fi24Tc.Pc.v601, CFSG.KD.Fi24Tc.Pc.v602, CFSG.KD.Fi24Tc.Pc.v603, CFSG.KD.Fi24Tc.Pc.v604]
theorem CFSG.KD.Fi24Tc.Pc.p603 : Nat.beq (runC AR SD 599 (ckL CFSG.KD.Fi24Tc.Pc.l605) 2 603 CFSG.KD.Fi24Tc.Pc.l603) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f88 : Nat.beq (runC AR SD 599 (finC AR SD (nat_lit 88) 599 607) 2 605 CFSG.KD.Fi24Tc.Pc.l605) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk88 : chk (nat_lit 88) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 88) (lo := 599) (hi := 607) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 601) CFSG.KD.Fi24Tc.Pc.p599 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 603) CFSG.KD.Fi24Tc.Pc.p601 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 605) CFSG.KD.Fi24Tc.Pc.p603 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f88

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v607 : Nat := CFSG.KD.Fi24Tc.KV4 54
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v608 : Nat := CFSG.KD.Fi24Tc.KV4 55
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l609 : List Nat := [CFSG.KD.Fi24Tc.Pc.v607, CFSG.KD.Fi24Tc.Pc.v608]
theorem CFSG.KD.Fi24Tc.Pc.p607 : Nat.beq (runC AR SD 607 (ckL CFSG.KD.Fi24Tc.Pc.l609) 2 607 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v609 : Nat := CFSG.KD.Fi24Tc.KV4 56
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v610 : Nat := CFSG.KD.Fi24Tc.KV4 57
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l611 : List Nat := [CFSG.KD.Fi24Tc.Pc.v607, CFSG.KD.Fi24Tc.Pc.v608, CFSG.KD.Fi24Tc.Pc.v609, CFSG.KD.Fi24Tc.Pc.v610]
theorem CFSG.KD.Fi24Tc.Pc.p609 : Nat.beq (runC AR SD 607 (ckL CFSG.KD.Fi24Tc.Pc.l611) 2 609 CFSG.KD.Fi24Tc.Pc.l609) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v611 : Nat := CFSG.KD.Fi24Tc.KV4 58
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v612 : Nat := CFSG.KD.Fi24Tc.KV4 59
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l613 : List Nat := [CFSG.KD.Fi24Tc.Pc.v607, CFSG.KD.Fi24Tc.Pc.v608, CFSG.KD.Fi24Tc.Pc.v609, CFSG.KD.Fi24Tc.Pc.v610, CFSG.KD.Fi24Tc.Pc.v611, CFSG.KD.Fi24Tc.Pc.v612]
theorem CFSG.KD.Fi24Tc.Pc.p611 : Nat.beq (runC AR SD 607 (ckL CFSG.KD.Fi24Tc.Pc.l613) 2 611 CFSG.KD.Fi24Tc.Pc.l611) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f89 : Nat.beq (runC AR SD 607 (finC AR SD (nat_lit 89) 607 615) 2 613 CFSG.KD.Fi24Tc.Pc.l613) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk89 : chk (nat_lit 89) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 89) (lo := 607) (hi := 615) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 609) CFSG.KD.Fi24Tc.Pc.p607 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 611) CFSG.KD.Fi24Tc.Pc.p609 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 613) CFSG.KD.Fi24Tc.Pc.p611 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f89

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v615 : Nat := CFSG.KD.Fi24Tc.KV4 60
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v616 : Nat := CFSG.KD.Fi24Tc.KV4 61
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l617 : List Nat := [CFSG.KD.Fi24Tc.Pc.v615, CFSG.KD.Fi24Tc.Pc.v616]
theorem CFSG.KD.Fi24Tc.Pc.p615 : Nat.beq (runC AR SD 615 (ckL CFSG.KD.Fi24Tc.Pc.l617) 2 615 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v617 : Nat := CFSG.KD.Fi24Tc.KV4 62
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v618 : Nat := CFSG.KD.Fi24Tc.KV4 63
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l619 : List Nat := [CFSG.KD.Fi24Tc.Pc.v615, CFSG.KD.Fi24Tc.Pc.v616, CFSG.KD.Fi24Tc.Pc.v617, CFSG.KD.Fi24Tc.Pc.v618]
theorem CFSG.KD.Fi24Tc.Pc.p617 : Nat.beq (runC AR SD 615 (ckL CFSG.KD.Fi24Tc.Pc.l619) 2 617 CFSG.KD.Fi24Tc.Pc.l617) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v619 : Nat := CFSG.KD.Fi24Tc.KV4 64
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v620 : Nat := CFSG.KD.Fi24Tc.KV4 65
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l621 : List Nat := [CFSG.KD.Fi24Tc.Pc.v615, CFSG.KD.Fi24Tc.Pc.v616, CFSG.KD.Fi24Tc.Pc.v617, CFSG.KD.Fi24Tc.Pc.v618, CFSG.KD.Fi24Tc.Pc.v619, CFSG.KD.Fi24Tc.Pc.v620]
theorem CFSG.KD.Fi24Tc.Pc.p619 : Nat.beq (runC AR SD 615 (ckL CFSG.KD.Fi24Tc.Pc.l621) 2 619 CFSG.KD.Fi24Tc.Pc.l619) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f90 : Nat.beq (runC AR SD 615 (finC AR SD (nat_lit 90) 615 623) 2 621 CFSG.KD.Fi24Tc.Pc.l621) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk90 : chk (nat_lit 90) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 90) (lo := 615) (hi := 623) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 617) CFSG.KD.Fi24Tc.Pc.p615 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 619) CFSG.KD.Fi24Tc.Pc.p617 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 621) CFSG.KD.Fi24Tc.Pc.p619 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f90

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v623 : Nat := CFSG.KD.Fi24Tc.KV4 66
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v624 : Nat := CFSG.KD.Fi24Tc.KV4 67
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l625 : List Nat := [CFSG.KD.Fi24Tc.Pc.v623, CFSG.KD.Fi24Tc.Pc.v624]
theorem CFSG.KD.Fi24Tc.Pc.p623 : Nat.beq (runC AR SD 623 (ckL CFSG.KD.Fi24Tc.Pc.l625) 2 623 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v625 : Nat := CFSG.KD.Fi24Tc.KV4 68
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v626 : Nat := CFSG.KD.Fi24Tc.KV4 69
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l627 : List Nat := [CFSG.KD.Fi24Tc.Pc.v623, CFSG.KD.Fi24Tc.Pc.v624, CFSG.KD.Fi24Tc.Pc.v625, CFSG.KD.Fi24Tc.Pc.v626]
theorem CFSG.KD.Fi24Tc.Pc.p625 : Nat.beq (runC AR SD 623 (ckL CFSG.KD.Fi24Tc.Pc.l627) 2 625 CFSG.KD.Fi24Tc.Pc.l625) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v627 : Nat := CFSG.KD.Fi24Tc.KV4 70
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v628 : Nat := CFSG.KD.Fi24Tc.KV4 71
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l629 : List Nat := [CFSG.KD.Fi24Tc.Pc.v623, CFSG.KD.Fi24Tc.Pc.v624, CFSG.KD.Fi24Tc.Pc.v625, CFSG.KD.Fi24Tc.Pc.v626, CFSG.KD.Fi24Tc.Pc.v627, CFSG.KD.Fi24Tc.Pc.v628]
theorem CFSG.KD.Fi24Tc.Pc.p627 : Nat.beq (runC AR SD 623 (ckL CFSG.KD.Fi24Tc.Pc.l629) 2 627 CFSG.KD.Fi24Tc.Pc.l627) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f91 : Nat.beq (runC AR SD 623 (finC AR SD (nat_lit 91) 623 631) 2 629 CFSG.KD.Fi24Tc.Pc.l629) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk91 : chk (nat_lit 91) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 91) (lo := 623) (hi := 631) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 625) CFSG.KD.Fi24Tc.Pc.p623 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 627) CFSG.KD.Fi24Tc.Pc.p625 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 629) CFSG.KD.Fi24Tc.Pc.p627 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f91

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v631 : Nat := CFSG.KD.Fi24Tc.KV4 72
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v632 : Nat := CFSG.KD.Fi24Tc.KV4 73
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l633 : List Nat := [CFSG.KD.Fi24Tc.Pc.v631, CFSG.KD.Fi24Tc.Pc.v632]
theorem CFSG.KD.Fi24Tc.Pc.p631 : Nat.beq (runC AR SD 631 (ckL CFSG.KD.Fi24Tc.Pc.l633) 2 631 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v633 : Nat := CFSG.KD.Fi24Tc.KV4 74
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v634 : Nat := CFSG.KD.Fi24Tc.KV4 75
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l635 : List Nat := [CFSG.KD.Fi24Tc.Pc.v631, CFSG.KD.Fi24Tc.Pc.v632, CFSG.KD.Fi24Tc.Pc.v633, CFSG.KD.Fi24Tc.Pc.v634]
theorem CFSG.KD.Fi24Tc.Pc.p633 : Nat.beq (runC AR SD 631 (ckL CFSG.KD.Fi24Tc.Pc.l635) 2 633 CFSG.KD.Fi24Tc.Pc.l633) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v635 : Nat := CFSG.KD.Fi24Tc.KV4 76
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v636 : Nat := CFSG.KD.Fi24Tc.KV4 77
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l637 : List Nat := [CFSG.KD.Fi24Tc.Pc.v631, CFSG.KD.Fi24Tc.Pc.v632, CFSG.KD.Fi24Tc.Pc.v633, CFSG.KD.Fi24Tc.Pc.v634, CFSG.KD.Fi24Tc.Pc.v635, CFSG.KD.Fi24Tc.Pc.v636]
theorem CFSG.KD.Fi24Tc.Pc.p635 : Nat.beq (runC AR SD 631 (ckL CFSG.KD.Fi24Tc.Pc.l637) 2 635 CFSG.KD.Fi24Tc.Pc.l635) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f92 : Nat.beq (runC AR SD 631 (finC AR SD (nat_lit 92) 631 639) 2 637 CFSG.KD.Fi24Tc.Pc.l637) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk92 : chk (nat_lit 92) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 92) (lo := 631) (hi := 639) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 633) CFSG.KD.Fi24Tc.Pc.p631 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 635) CFSG.KD.Fi24Tc.Pc.p633 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 637) CFSG.KD.Fi24Tc.Pc.p635 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f92

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v639 : Nat := CFSG.KD.Fi24Tc.KV4 78
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v640 : Nat := CFSG.KD.Fi24Tc.KV4 79
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l641 : List Nat := [CFSG.KD.Fi24Tc.Pc.v639, CFSG.KD.Fi24Tc.Pc.v640]
theorem CFSG.KD.Fi24Tc.Pc.p639 : Nat.beq (runC AR SD 639 (ckL CFSG.KD.Fi24Tc.Pc.l641) 2 639 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v641 : Nat := CFSG.KD.Fi24Tc.KV4 80
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v642 : Nat := CFSG.KD.Fi24Tc.KV4 81
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l643 : List Nat := [CFSG.KD.Fi24Tc.Pc.v639, CFSG.KD.Fi24Tc.Pc.v640, CFSG.KD.Fi24Tc.Pc.v641, CFSG.KD.Fi24Tc.Pc.v642]
theorem CFSG.KD.Fi24Tc.Pc.p641 : Nat.beq (runC AR SD 639 (ckL CFSG.KD.Fi24Tc.Pc.l643) 2 641 CFSG.KD.Fi24Tc.Pc.l641) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v643 : Nat := CFSG.KD.Fi24Tc.KV4 82
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v644 : Nat := CFSG.KD.Fi24Tc.KV4 83
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l645 : List Nat := [CFSG.KD.Fi24Tc.Pc.v639, CFSG.KD.Fi24Tc.Pc.v640, CFSG.KD.Fi24Tc.Pc.v641, CFSG.KD.Fi24Tc.Pc.v642, CFSG.KD.Fi24Tc.Pc.v643, CFSG.KD.Fi24Tc.Pc.v644]
theorem CFSG.KD.Fi24Tc.Pc.p643 : Nat.beq (runC AR SD 639 (ckL CFSG.KD.Fi24Tc.Pc.l645) 2 643 CFSG.KD.Fi24Tc.Pc.l643) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f93 : Nat.beq (runC AR SD 639 (finC AR SD (nat_lit 93) 639 647) 2 645 CFSG.KD.Fi24Tc.Pc.l645) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk93 : chk (nat_lit 93) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 93) (lo := 639) (hi := 647) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 641) CFSG.KD.Fi24Tc.Pc.p639 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 643) CFSG.KD.Fi24Tc.Pc.p641 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 645) CFSG.KD.Fi24Tc.Pc.p643 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f93

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v647 : Nat := CFSG.KD.Fi24Tc.KV4 84
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v648 : Nat := CFSG.KD.Fi24Tc.KV4 85
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l649 : List Nat := [CFSG.KD.Fi24Tc.Pc.v647, CFSG.KD.Fi24Tc.Pc.v648]
theorem CFSG.KD.Fi24Tc.Pc.p647 : Nat.beq (runC AR SD 647 (ckL CFSG.KD.Fi24Tc.Pc.l649) 2 647 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v649 : Nat := CFSG.KD.Fi24Tc.KV4 86
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v650 : Nat := CFSG.KD.Fi24Tc.KV4 87
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l651 : List Nat := [CFSG.KD.Fi24Tc.Pc.v647, CFSG.KD.Fi24Tc.Pc.v648, CFSG.KD.Fi24Tc.Pc.v649, CFSG.KD.Fi24Tc.Pc.v650]
theorem CFSG.KD.Fi24Tc.Pc.p649 : Nat.beq (runC AR SD 647 (ckL CFSG.KD.Fi24Tc.Pc.l651) 2 649 CFSG.KD.Fi24Tc.Pc.l649) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v651 : Nat := CFSG.KD.Fi24Tc.KV4 88
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v652 : Nat := CFSG.KD.Fi24Tc.KV4 89
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l653 : List Nat := [CFSG.KD.Fi24Tc.Pc.v647, CFSG.KD.Fi24Tc.Pc.v648, CFSG.KD.Fi24Tc.Pc.v649, CFSG.KD.Fi24Tc.Pc.v650, CFSG.KD.Fi24Tc.Pc.v651, CFSG.KD.Fi24Tc.Pc.v652]
theorem CFSG.KD.Fi24Tc.Pc.p651 : Nat.beq (runC AR SD 647 (ckL CFSG.KD.Fi24Tc.Pc.l653) 2 651 CFSG.KD.Fi24Tc.Pc.l651) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f94 : Nat.beq (runC AR SD 647 (finC AR SD (nat_lit 94) 647 655) 2 653 CFSG.KD.Fi24Tc.Pc.l653) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk94 : chk (nat_lit 94) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 94) (lo := 647) (hi := 655) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 649) CFSG.KD.Fi24Tc.Pc.p647 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 651) CFSG.KD.Fi24Tc.Pc.p649 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 653) CFSG.KD.Fi24Tc.Pc.p651 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f94

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v655 : Nat := CFSG.KD.Fi24Tc.KV4 90
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v656 : Nat := CFSG.KD.Fi24Tc.KV4 91
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l657 : List Nat := [CFSG.KD.Fi24Tc.Pc.v655, CFSG.KD.Fi24Tc.Pc.v656]
theorem CFSG.KD.Fi24Tc.Pc.p655 : Nat.beq (runC AR SD 655 (ckL CFSG.KD.Fi24Tc.Pc.l657) 2 655 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v657 : Nat := CFSG.KD.Fi24Tc.KV4 92
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v658 : Nat := CFSG.KD.Fi24Tc.KV4 93
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l659 : List Nat := [CFSG.KD.Fi24Tc.Pc.v655, CFSG.KD.Fi24Tc.Pc.v656, CFSG.KD.Fi24Tc.Pc.v657, CFSG.KD.Fi24Tc.Pc.v658]
theorem CFSG.KD.Fi24Tc.Pc.p657 : Nat.beq (runC AR SD 655 (ckL CFSG.KD.Fi24Tc.Pc.l659) 2 657 CFSG.KD.Fi24Tc.Pc.l657) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v659 : Nat := CFSG.KD.Fi24Tc.KV4 94
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v660 : Nat := CFSG.KD.Fi24Tc.KV4 95
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l661 : List Nat := [CFSG.KD.Fi24Tc.Pc.v655, CFSG.KD.Fi24Tc.Pc.v656, CFSG.KD.Fi24Tc.Pc.v657, CFSG.KD.Fi24Tc.Pc.v658, CFSG.KD.Fi24Tc.Pc.v659, CFSG.KD.Fi24Tc.Pc.v660]
theorem CFSG.KD.Fi24Tc.Pc.p659 : Nat.beq (runC AR SD 655 (ckL CFSG.KD.Fi24Tc.Pc.l661) 2 659 CFSG.KD.Fi24Tc.Pc.l659) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f95 : Nat.beq (runC AR SD 655 (finC AR SD (nat_lit 95) 655 663) 2 661 CFSG.KD.Fi24Tc.Pc.l661) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk95 : chk (nat_lit 95) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 95) (lo := 655) (hi := 663) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 657) CFSG.KD.Fi24Tc.Pc.p655 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 659) CFSG.KD.Fi24Tc.Pc.p657 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 661) CFSG.KD.Fi24Tc.Pc.p659 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f95

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v663 : Nat := CFSG.KD.Fi24Tc.KV4 96
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l664 : List Nat := [CFSG.KD.Fi24Tc.Pc.v663]
theorem CFSG.KD.Fi24Tc.Pc.p663 : Nat.beq (runC AR SD 663 (ckL CFSG.KD.Fi24Tc.Pc.l664) 1 663 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v664 : Nat := CFSG.KD.Fi24Tc.KV4 97
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l665 : List Nat := [CFSG.KD.Fi24Tc.Pc.v663, CFSG.KD.Fi24Tc.Pc.v664]
theorem CFSG.KD.Fi24Tc.Pc.p664 : Nat.beq (runC AR SD 663 (ckL CFSG.KD.Fi24Tc.Pc.l665) 1 664 CFSG.KD.Fi24Tc.Pc.l664) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v665 : Nat := CFSG.KD.Fi24Tc.KV4 98
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v666 : Nat := CFSG.KD.Fi24Tc.KV4 99
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l667 : List Nat := [CFSG.KD.Fi24Tc.Pc.v663, CFSG.KD.Fi24Tc.Pc.v664, CFSG.KD.Fi24Tc.Pc.v665, CFSG.KD.Fi24Tc.Pc.v666]
theorem CFSG.KD.Fi24Tc.Pc.p665 : Nat.beq (runC AR SD 663 (ckL CFSG.KD.Fi24Tc.Pc.l667) 2 665 CFSG.KD.Fi24Tc.Pc.l665) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v667 : Nat := CFSG.KD.Fi24Tc.KV4 100
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v668 : Nat := CFSG.KD.Fi24Tc.KV4 101
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l669 : List Nat := [CFSG.KD.Fi24Tc.Pc.v663, CFSG.KD.Fi24Tc.Pc.v664, CFSG.KD.Fi24Tc.Pc.v665, CFSG.KD.Fi24Tc.Pc.v666, CFSG.KD.Fi24Tc.Pc.v667, CFSG.KD.Fi24Tc.Pc.v668]
theorem CFSG.KD.Fi24Tc.Pc.p667 : Nat.beq (runC AR SD 663 (ckL CFSG.KD.Fi24Tc.Pc.l669) 2 667 CFSG.KD.Fi24Tc.Pc.l667) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f96 : Nat.beq (runC AR SD 663 (finC AR SD (nat_lit 96) 663 670) 1 669 CFSG.KD.Fi24Tc.Pc.l669) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk96 : chk (nat_lit 96) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 96) (lo := 663) (hi := 670) (m := 7) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 7) (m2 := 6) (j2 := 664) CFSG.KD.Fi24Tc.Pc.p663 rfl rfl).trans ((runC_seq (m := 6) (m2 := 5) (j2 := 665) CFSG.KD.Fi24Tc.Pc.p664 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 667) CFSG.KD.Fi24Tc.Pc.p665 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 669) CFSG.KD.Fi24Tc.Pc.p667 rfl rfl)))))).trans CFSG.KD.Fi24Tc.Pc.f96

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v670 : Nat := CFSG.KD.Fi24Tc.KV4 102
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v671 : Nat := CFSG.KD.Fi24Tc.KV4 103
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l672 : List Nat := [CFSG.KD.Fi24Tc.Pc.v670, CFSG.KD.Fi24Tc.Pc.v671]
theorem CFSG.KD.Fi24Tc.Pc.p670 : Nat.beq (runC AR SD 670 (ckL CFSG.KD.Fi24Tc.Pc.l672) 2 670 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v672 : Nat := CFSG.KD.Fi24Tc.KV4 104
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v673 : Nat := CFSG.KD.Fi24Tc.KV4 105
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l674 : List Nat := [CFSG.KD.Fi24Tc.Pc.v670, CFSG.KD.Fi24Tc.Pc.v671, CFSG.KD.Fi24Tc.Pc.v672, CFSG.KD.Fi24Tc.Pc.v673]
theorem CFSG.KD.Fi24Tc.Pc.p672 : Nat.beq (runC AR SD 670 (ckL CFSG.KD.Fi24Tc.Pc.l674) 2 672 CFSG.KD.Fi24Tc.Pc.l672) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v674 : Nat := CFSG.KD.Fi24Tc.KV4 106
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v675 : Nat := CFSG.KD.Fi24Tc.KV4 107
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l676 : List Nat := [CFSG.KD.Fi24Tc.Pc.v670, CFSG.KD.Fi24Tc.Pc.v671, CFSG.KD.Fi24Tc.Pc.v672, CFSG.KD.Fi24Tc.Pc.v673, CFSG.KD.Fi24Tc.Pc.v674, CFSG.KD.Fi24Tc.Pc.v675]
theorem CFSG.KD.Fi24Tc.Pc.p674 : Nat.beq (runC AR SD 670 (ckL CFSG.KD.Fi24Tc.Pc.l676) 2 674 CFSG.KD.Fi24Tc.Pc.l674) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f97 : Nat.beq (runC AR SD 670 (finC AR SD (nat_lit 97) 670 678) 2 676 CFSG.KD.Fi24Tc.Pc.l676) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk97 : chk (nat_lit 97) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 97) (lo := 670) (hi := 678) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 672) CFSG.KD.Fi24Tc.Pc.p670 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 674) CFSG.KD.Fi24Tc.Pc.p672 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 676) CFSG.KD.Fi24Tc.Pc.p674 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f97

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v678 : Nat := CFSG.KD.Fi24Tc.KV4 108
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v679 : Nat := CFSG.KD.Fi24Tc.KV4 109
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l680 : List Nat := [CFSG.KD.Fi24Tc.Pc.v678, CFSG.KD.Fi24Tc.Pc.v679]
theorem CFSG.KD.Fi24Tc.Pc.p678 : Nat.beq (runC AR SD 678 (ckL CFSG.KD.Fi24Tc.Pc.l680) 2 678 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v680 : Nat := CFSG.KD.Fi24Tc.KV4 110
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v681 : Nat := CFSG.KD.Fi24Tc.KV4 111
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l682 : List Nat := [CFSG.KD.Fi24Tc.Pc.v678, CFSG.KD.Fi24Tc.Pc.v679, CFSG.KD.Fi24Tc.Pc.v680, CFSG.KD.Fi24Tc.Pc.v681]
theorem CFSG.KD.Fi24Tc.Pc.p680 : Nat.beq (runC AR SD 678 (ckL CFSG.KD.Fi24Tc.Pc.l682) 2 680 CFSG.KD.Fi24Tc.Pc.l680) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v682 : Nat := CFSG.KD.Fi24Tc.KV4 112
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v683 : Nat := CFSG.KD.Fi24Tc.KV4 113
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l684 : List Nat := [CFSG.KD.Fi24Tc.Pc.v678, CFSG.KD.Fi24Tc.Pc.v679, CFSG.KD.Fi24Tc.Pc.v680, CFSG.KD.Fi24Tc.Pc.v681, CFSG.KD.Fi24Tc.Pc.v682, CFSG.KD.Fi24Tc.Pc.v683]
theorem CFSG.KD.Fi24Tc.Pc.p682 : Nat.beq (runC AR SD 678 (ckL CFSG.KD.Fi24Tc.Pc.l684) 2 682 CFSG.KD.Fi24Tc.Pc.l682) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f98 : Nat.beq (runC AR SD 678 (finC AR SD (nat_lit 98) 678 686) 2 684 CFSG.KD.Fi24Tc.Pc.l684) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk98 : chk (nat_lit 98) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 98) (lo := 678) (hi := 686) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 680) CFSG.KD.Fi24Tc.Pc.p678 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 682) CFSG.KD.Fi24Tc.Pc.p680 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 684) CFSG.KD.Fi24Tc.Pc.p682 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f98

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v686 : Nat := CFSG.KD.Fi24Tc.KV4 114
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v687 : Nat := CFSG.KD.Fi24Tc.KV4 115
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l688 : List Nat := [CFSG.KD.Fi24Tc.Pc.v686, CFSG.KD.Fi24Tc.Pc.v687]
theorem CFSG.KD.Fi24Tc.Pc.p686 : Nat.beq (runC AR SD 686 (ckL CFSG.KD.Fi24Tc.Pc.l688) 2 686 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v688 : Nat := CFSG.KD.Fi24Tc.KV4 116
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v689 : Nat := CFSG.KD.Fi24Tc.KV4 117
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l690 : List Nat := [CFSG.KD.Fi24Tc.Pc.v686, CFSG.KD.Fi24Tc.Pc.v687, CFSG.KD.Fi24Tc.Pc.v688, CFSG.KD.Fi24Tc.Pc.v689]
theorem CFSG.KD.Fi24Tc.Pc.p688 : Nat.beq (runC AR SD 686 (ckL CFSG.KD.Fi24Tc.Pc.l690) 2 688 CFSG.KD.Fi24Tc.Pc.l688) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v690 : Nat := CFSG.KD.Fi24Tc.KV4 118
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v691 : Nat := CFSG.KD.Fi24Tc.KV4 119
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l692 : List Nat := [CFSG.KD.Fi24Tc.Pc.v686, CFSG.KD.Fi24Tc.Pc.v687, CFSG.KD.Fi24Tc.Pc.v688, CFSG.KD.Fi24Tc.Pc.v689, CFSG.KD.Fi24Tc.Pc.v690, CFSG.KD.Fi24Tc.Pc.v691]
theorem CFSG.KD.Fi24Tc.Pc.p690 : Nat.beq (runC AR SD 686 (ckL CFSG.KD.Fi24Tc.Pc.l692) 2 690 CFSG.KD.Fi24Tc.Pc.l690) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f99 : Nat.beq (runC AR SD 686 (finC AR SD (nat_lit 99) 686 694) 2 692 CFSG.KD.Fi24Tc.Pc.l692) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk99 : chk (nat_lit 99) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 99) (lo := 686) (hi := 694) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 688) CFSG.KD.Fi24Tc.Pc.p686 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 690) CFSG.KD.Fi24Tc.Pc.p688 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 692) CFSG.KD.Fi24Tc.Pc.p690 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f99

end
