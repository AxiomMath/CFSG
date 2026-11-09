module

public import Certificates.Kernel.Sporadic.Fi24Alpha.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Alpha KV4 "Certificates/Kernel/Sporadic/Fi24Alpha/data/v4.bin" 152491 4 23941087 12250268313417436518

public section

open CFSG.KD.Fi24Alpha CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v527 : Nat := CFSG.KD.Fi24Alpha.KV4 0
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v528 : Nat := CFSG.KD.Fi24Alpha.KV4 1
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l529 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v527, CFSG.KD.Fi24Alpha.Pc.v528]
theorem CFSG.KD.Fi24Alpha.Pc.p527 : Nat.beq (runC AR SD 527 (ckL CFSG.KD.Fi24Alpha.Pc.l529) 2 527 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v529 : Nat := CFSG.KD.Fi24Alpha.KV4 2
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v530 : Nat := CFSG.KD.Fi24Alpha.KV4 3
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l531 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v527, CFSG.KD.Fi24Alpha.Pc.v528, CFSG.KD.Fi24Alpha.Pc.v529, CFSG.KD.Fi24Alpha.Pc.v530]
theorem CFSG.KD.Fi24Alpha.Pc.p529 : Nat.beq (runC AR SD 527 (ckL CFSG.KD.Fi24Alpha.Pc.l531) 2 529 CFSG.KD.Fi24Alpha.Pc.l529) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v531 : Nat := CFSG.KD.Fi24Alpha.KV4 4
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v532 : Nat := CFSG.KD.Fi24Alpha.KV4 5
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l533 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v527, CFSG.KD.Fi24Alpha.Pc.v528, CFSG.KD.Fi24Alpha.Pc.v529, CFSG.KD.Fi24Alpha.Pc.v530, CFSG.KD.Fi24Alpha.Pc.v531, CFSG.KD.Fi24Alpha.Pc.v532]
theorem CFSG.KD.Fi24Alpha.Pc.p531 : Nat.beq (runC AR SD 527 (ckL CFSG.KD.Fi24Alpha.Pc.l533) 2 531 CFSG.KD.Fi24Alpha.Pc.l531) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v533 : Nat := CFSG.KD.Fi24Alpha.KV4 6
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v534 : Nat := CFSG.KD.Fi24Alpha.KV4 7
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l535 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v527, CFSG.KD.Fi24Alpha.Pc.v528, CFSG.KD.Fi24Alpha.Pc.v529, CFSG.KD.Fi24Alpha.Pc.v530, CFSG.KD.Fi24Alpha.Pc.v531, CFSG.KD.Fi24Alpha.Pc.v532, CFSG.KD.Fi24Alpha.Pc.v533, CFSG.KD.Fi24Alpha.Pc.v534]
theorem CFSG.KD.Fi24Alpha.Pc.p533 : Nat.beq (runC AR SD 527 (ckL CFSG.KD.Fi24Alpha.Pc.l535) 2 533 CFSG.KD.Fi24Alpha.Pc.l533) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v535 : Nat := CFSG.KD.Fi24Alpha.KV4 8
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v536 : Nat := CFSG.KD.Fi24Alpha.KV4 9
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l537 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v527, CFSG.KD.Fi24Alpha.Pc.v528, CFSG.KD.Fi24Alpha.Pc.v529, CFSG.KD.Fi24Alpha.Pc.v530, CFSG.KD.Fi24Alpha.Pc.v531, CFSG.KD.Fi24Alpha.Pc.v532, CFSG.KD.Fi24Alpha.Pc.v533, CFSG.KD.Fi24Alpha.Pc.v534, CFSG.KD.Fi24Alpha.Pc.v535, CFSG.KD.Fi24Alpha.Pc.v536]
theorem CFSG.KD.Fi24Alpha.Pc.p535 : Nat.beq (runC AR SD 527 (ckL CFSG.KD.Fi24Alpha.Pc.l537) 2 535 CFSG.KD.Fi24Alpha.Pc.l535) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v537 : Nat := CFSG.KD.Fi24Alpha.KV4 10
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v538 : Nat := CFSG.KD.Fi24Alpha.KV4 11
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l539 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v527, CFSG.KD.Fi24Alpha.Pc.v528, CFSG.KD.Fi24Alpha.Pc.v529, CFSG.KD.Fi24Alpha.Pc.v530, CFSG.KD.Fi24Alpha.Pc.v531, CFSG.KD.Fi24Alpha.Pc.v532, CFSG.KD.Fi24Alpha.Pc.v533, CFSG.KD.Fi24Alpha.Pc.v534, CFSG.KD.Fi24Alpha.Pc.v535, CFSG.KD.Fi24Alpha.Pc.v536, CFSG.KD.Fi24Alpha.Pc.v537, CFSG.KD.Fi24Alpha.Pc.v538]
theorem CFSG.KD.Fi24Alpha.Pc.p537 : Nat.beq (runC AR SD 527 (ckL CFSG.KD.Fi24Alpha.Pc.l539) 2 537 CFSG.KD.Fi24Alpha.Pc.l537) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v539 : Nat := CFSG.KD.Fi24Alpha.KV4 12
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v540 : Nat := CFSG.KD.Fi24Alpha.KV4 13
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l541 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v527, CFSG.KD.Fi24Alpha.Pc.v528, CFSG.KD.Fi24Alpha.Pc.v529, CFSG.KD.Fi24Alpha.Pc.v530, CFSG.KD.Fi24Alpha.Pc.v531, CFSG.KD.Fi24Alpha.Pc.v532, CFSG.KD.Fi24Alpha.Pc.v533, CFSG.KD.Fi24Alpha.Pc.v534, CFSG.KD.Fi24Alpha.Pc.v535, CFSG.KD.Fi24Alpha.Pc.v536, CFSG.KD.Fi24Alpha.Pc.v537, CFSG.KD.Fi24Alpha.Pc.v538, CFSG.KD.Fi24Alpha.Pc.v539, CFSG.KD.Fi24Alpha.Pc.v540]
theorem CFSG.KD.Fi24Alpha.Pc.p539 : Nat.beq (runC AR SD 527 (ckL CFSG.KD.Fi24Alpha.Pc.l541) 2 539 CFSG.KD.Fi24Alpha.Pc.l539) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v541 : Nat := CFSG.KD.Fi24Alpha.KV4 14
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v542 : Nat := CFSG.KD.Fi24Alpha.KV4 15
theorem CFSG.KD.Fi24Alpha.Pc.f40 : Nat.beq (runC AR SD 527 (finC AR SD (nat_lit 40) 527 543) 2 541 CFSG.KD.Fi24Alpha.Pc.l541) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk40 : chk (nat_lit 40) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 40) (lo := 527) (hi := 543) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 529) CFSG.KD.Fi24Alpha.Pc.p527 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 531) CFSG.KD.Fi24Alpha.Pc.p529 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 533) CFSG.KD.Fi24Alpha.Pc.p531 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 535) CFSG.KD.Fi24Alpha.Pc.p533 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 537) CFSG.KD.Fi24Alpha.Pc.p535 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 539) CFSG.KD.Fi24Alpha.Pc.p537 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 541) CFSG.KD.Fi24Alpha.Pc.p539 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f40

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v543 : Nat := CFSG.KD.Fi24Alpha.KV4 16
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v544 : Nat := CFSG.KD.Fi24Alpha.KV4 17
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l545 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v543, CFSG.KD.Fi24Alpha.Pc.v544]
theorem CFSG.KD.Fi24Alpha.Pc.p543 : Nat.beq (runC AR SD 543 (ckL CFSG.KD.Fi24Alpha.Pc.l545) 2 543 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v545 : Nat := CFSG.KD.Fi24Alpha.KV4 18
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v546 : Nat := CFSG.KD.Fi24Alpha.KV4 19
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l547 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v543, CFSG.KD.Fi24Alpha.Pc.v544, CFSG.KD.Fi24Alpha.Pc.v545, CFSG.KD.Fi24Alpha.Pc.v546]
theorem CFSG.KD.Fi24Alpha.Pc.p545 : Nat.beq (runC AR SD 543 (ckL CFSG.KD.Fi24Alpha.Pc.l547) 2 545 CFSG.KD.Fi24Alpha.Pc.l545) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v547 : Nat := CFSG.KD.Fi24Alpha.KV4 20
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v548 : Nat := CFSG.KD.Fi24Alpha.KV4 21
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l549 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v543, CFSG.KD.Fi24Alpha.Pc.v544, CFSG.KD.Fi24Alpha.Pc.v545, CFSG.KD.Fi24Alpha.Pc.v546, CFSG.KD.Fi24Alpha.Pc.v547, CFSG.KD.Fi24Alpha.Pc.v548]
theorem CFSG.KD.Fi24Alpha.Pc.p547 : Nat.beq (runC AR SD 543 (ckL CFSG.KD.Fi24Alpha.Pc.l549) 2 547 CFSG.KD.Fi24Alpha.Pc.l547) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v549 : Nat := CFSG.KD.Fi24Alpha.KV4 22
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v550 : Nat := CFSG.KD.Fi24Alpha.KV4 23
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l551 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v543, CFSG.KD.Fi24Alpha.Pc.v544, CFSG.KD.Fi24Alpha.Pc.v545, CFSG.KD.Fi24Alpha.Pc.v546, CFSG.KD.Fi24Alpha.Pc.v547, CFSG.KD.Fi24Alpha.Pc.v548, CFSG.KD.Fi24Alpha.Pc.v549, CFSG.KD.Fi24Alpha.Pc.v550]
theorem CFSG.KD.Fi24Alpha.Pc.p549 : Nat.beq (runC AR SD 543 (ckL CFSG.KD.Fi24Alpha.Pc.l551) 2 549 CFSG.KD.Fi24Alpha.Pc.l549) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v551 : Nat := CFSG.KD.Fi24Alpha.KV4 24
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l552 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v543, CFSG.KD.Fi24Alpha.Pc.v544, CFSG.KD.Fi24Alpha.Pc.v545, CFSG.KD.Fi24Alpha.Pc.v546, CFSG.KD.Fi24Alpha.Pc.v547, CFSG.KD.Fi24Alpha.Pc.v548, CFSG.KD.Fi24Alpha.Pc.v549, CFSG.KD.Fi24Alpha.Pc.v550, CFSG.KD.Fi24Alpha.Pc.v551]
theorem CFSG.KD.Fi24Alpha.Pc.p551 : Nat.beq (runC AR SD 543 (ckL CFSG.KD.Fi24Alpha.Pc.l552) 1 551 CFSG.KD.Fi24Alpha.Pc.l551) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v552 : Nat := CFSG.KD.Fi24Alpha.KV4 25
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v553 : Nat := CFSG.KD.Fi24Alpha.KV4 26
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l554 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v543, CFSG.KD.Fi24Alpha.Pc.v544, CFSG.KD.Fi24Alpha.Pc.v545, CFSG.KD.Fi24Alpha.Pc.v546, CFSG.KD.Fi24Alpha.Pc.v547, CFSG.KD.Fi24Alpha.Pc.v548, CFSG.KD.Fi24Alpha.Pc.v549, CFSG.KD.Fi24Alpha.Pc.v550, CFSG.KD.Fi24Alpha.Pc.v551, CFSG.KD.Fi24Alpha.Pc.v552, CFSG.KD.Fi24Alpha.Pc.v553]
theorem CFSG.KD.Fi24Alpha.Pc.p552 : Nat.beq (runC AR SD 543 (ckL CFSG.KD.Fi24Alpha.Pc.l554) 2 552 CFSG.KD.Fi24Alpha.Pc.l552) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v554 : Nat := CFSG.KD.Fi24Alpha.KV4 27
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v555 : Nat := CFSG.KD.Fi24Alpha.KV4 28
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l556 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v543, CFSG.KD.Fi24Alpha.Pc.v544, CFSG.KD.Fi24Alpha.Pc.v545, CFSG.KD.Fi24Alpha.Pc.v546, CFSG.KD.Fi24Alpha.Pc.v547, CFSG.KD.Fi24Alpha.Pc.v548, CFSG.KD.Fi24Alpha.Pc.v549, CFSG.KD.Fi24Alpha.Pc.v550, CFSG.KD.Fi24Alpha.Pc.v551, CFSG.KD.Fi24Alpha.Pc.v552, CFSG.KD.Fi24Alpha.Pc.v553, CFSG.KD.Fi24Alpha.Pc.v554, CFSG.KD.Fi24Alpha.Pc.v555]
theorem CFSG.KD.Fi24Alpha.Pc.p554 : Nat.beq (runC AR SD 543 (ckL CFSG.KD.Fi24Alpha.Pc.l556) 2 554 CFSG.KD.Fi24Alpha.Pc.l554) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v556 : Nat := CFSG.KD.Fi24Alpha.KV4 29
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v557 : Nat := CFSG.KD.Fi24Alpha.KV4 30
theorem CFSG.KD.Fi24Alpha.Pc.f41 : Nat.beq (runC AR SD 543 (finC AR SD (nat_lit 41) 543 558) 2 556 CFSG.KD.Fi24Alpha.Pc.l556) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk41 : chk (nat_lit 41) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 41) (lo := 543) (hi := 558) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 545) CFSG.KD.Fi24Alpha.Pc.p543 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 547) CFSG.KD.Fi24Alpha.Pc.p545 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 549) CFSG.KD.Fi24Alpha.Pc.p547 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 551) CFSG.KD.Fi24Alpha.Pc.p549 rfl rfl).trans ((runC_seq (m := 7) (m2 := 6) (j2 := 552) CFSG.KD.Fi24Alpha.Pc.p551 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 554) CFSG.KD.Fi24Alpha.Pc.p552 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 556) CFSG.KD.Fi24Alpha.Pc.p554 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f41

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v558 : Nat := CFSG.KD.Fi24Alpha.KV4 31
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v559 : Nat := CFSG.KD.Fi24Alpha.KV4 32
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l560 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v558, CFSG.KD.Fi24Alpha.Pc.v559]
theorem CFSG.KD.Fi24Alpha.Pc.p558 : Nat.beq (runC AR SD 558 (ckL CFSG.KD.Fi24Alpha.Pc.l560) 2 558 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v560 : Nat := CFSG.KD.Fi24Alpha.KV4 33
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v561 : Nat := CFSG.KD.Fi24Alpha.KV4 34
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l562 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v558, CFSG.KD.Fi24Alpha.Pc.v559, CFSG.KD.Fi24Alpha.Pc.v560, CFSG.KD.Fi24Alpha.Pc.v561]
theorem CFSG.KD.Fi24Alpha.Pc.p560 : Nat.beq (runC AR SD 558 (ckL CFSG.KD.Fi24Alpha.Pc.l562) 2 560 CFSG.KD.Fi24Alpha.Pc.l560) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v562 : Nat := CFSG.KD.Fi24Alpha.KV4 35
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v563 : Nat := CFSG.KD.Fi24Alpha.KV4 36
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l564 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v558, CFSG.KD.Fi24Alpha.Pc.v559, CFSG.KD.Fi24Alpha.Pc.v560, CFSG.KD.Fi24Alpha.Pc.v561, CFSG.KD.Fi24Alpha.Pc.v562, CFSG.KD.Fi24Alpha.Pc.v563]
theorem CFSG.KD.Fi24Alpha.Pc.p562 : Nat.beq (runC AR SD 558 (ckL CFSG.KD.Fi24Alpha.Pc.l564) 2 562 CFSG.KD.Fi24Alpha.Pc.l562) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v564 : Nat := CFSG.KD.Fi24Alpha.KV4 37
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v565 : Nat := CFSG.KD.Fi24Alpha.KV4 38
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l566 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v558, CFSG.KD.Fi24Alpha.Pc.v559, CFSG.KD.Fi24Alpha.Pc.v560, CFSG.KD.Fi24Alpha.Pc.v561, CFSG.KD.Fi24Alpha.Pc.v562, CFSG.KD.Fi24Alpha.Pc.v563, CFSG.KD.Fi24Alpha.Pc.v564, CFSG.KD.Fi24Alpha.Pc.v565]
theorem CFSG.KD.Fi24Alpha.Pc.p564 : Nat.beq (runC AR SD 558 (ckL CFSG.KD.Fi24Alpha.Pc.l566) 2 564 CFSG.KD.Fi24Alpha.Pc.l564) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v566 : Nat := CFSG.KD.Fi24Alpha.KV4 39
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v567 : Nat := CFSG.KD.Fi24Alpha.KV4 40
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l568 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v558, CFSG.KD.Fi24Alpha.Pc.v559, CFSG.KD.Fi24Alpha.Pc.v560, CFSG.KD.Fi24Alpha.Pc.v561, CFSG.KD.Fi24Alpha.Pc.v562, CFSG.KD.Fi24Alpha.Pc.v563, CFSG.KD.Fi24Alpha.Pc.v564, CFSG.KD.Fi24Alpha.Pc.v565, CFSG.KD.Fi24Alpha.Pc.v566, CFSG.KD.Fi24Alpha.Pc.v567]
theorem CFSG.KD.Fi24Alpha.Pc.p566 : Nat.beq (runC AR SD 558 (ckL CFSG.KD.Fi24Alpha.Pc.l568) 2 566 CFSG.KD.Fi24Alpha.Pc.l566) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v568 : Nat := CFSG.KD.Fi24Alpha.KV4 41
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v569 : Nat := CFSG.KD.Fi24Alpha.KV4 42
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l570 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v558, CFSG.KD.Fi24Alpha.Pc.v559, CFSG.KD.Fi24Alpha.Pc.v560, CFSG.KD.Fi24Alpha.Pc.v561, CFSG.KD.Fi24Alpha.Pc.v562, CFSG.KD.Fi24Alpha.Pc.v563, CFSG.KD.Fi24Alpha.Pc.v564, CFSG.KD.Fi24Alpha.Pc.v565, CFSG.KD.Fi24Alpha.Pc.v566, CFSG.KD.Fi24Alpha.Pc.v567, CFSG.KD.Fi24Alpha.Pc.v568, CFSG.KD.Fi24Alpha.Pc.v569]
theorem CFSG.KD.Fi24Alpha.Pc.p568 : Nat.beq (runC AR SD 558 (ckL CFSG.KD.Fi24Alpha.Pc.l570) 2 568 CFSG.KD.Fi24Alpha.Pc.l568) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v570 : Nat := CFSG.KD.Fi24Alpha.KV4 43
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v571 : Nat := CFSG.KD.Fi24Alpha.KV4 44
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l572 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v558, CFSG.KD.Fi24Alpha.Pc.v559, CFSG.KD.Fi24Alpha.Pc.v560, CFSG.KD.Fi24Alpha.Pc.v561, CFSG.KD.Fi24Alpha.Pc.v562, CFSG.KD.Fi24Alpha.Pc.v563, CFSG.KD.Fi24Alpha.Pc.v564, CFSG.KD.Fi24Alpha.Pc.v565, CFSG.KD.Fi24Alpha.Pc.v566, CFSG.KD.Fi24Alpha.Pc.v567, CFSG.KD.Fi24Alpha.Pc.v568, CFSG.KD.Fi24Alpha.Pc.v569, CFSG.KD.Fi24Alpha.Pc.v570, CFSG.KD.Fi24Alpha.Pc.v571]
theorem CFSG.KD.Fi24Alpha.Pc.p570 : Nat.beq (runC AR SD 558 (ckL CFSG.KD.Fi24Alpha.Pc.l572) 2 570 CFSG.KD.Fi24Alpha.Pc.l570) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v572 : Nat := CFSG.KD.Fi24Alpha.KV4 45
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v573 : Nat := CFSG.KD.Fi24Alpha.KV4 46
theorem CFSG.KD.Fi24Alpha.Pc.f42 : Nat.beq (runC AR SD 558 (finC AR SD (nat_lit 42) 558 574) 2 572 CFSG.KD.Fi24Alpha.Pc.l572) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk42 : chk (nat_lit 42) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 42) (lo := 558) (hi := 574) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 560) CFSG.KD.Fi24Alpha.Pc.p558 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 562) CFSG.KD.Fi24Alpha.Pc.p560 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 564) CFSG.KD.Fi24Alpha.Pc.p562 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 566) CFSG.KD.Fi24Alpha.Pc.p564 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 568) CFSG.KD.Fi24Alpha.Pc.p566 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 570) CFSG.KD.Fi24Alpha.Pc.p568 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 572) CFSG.KD.Fi24Alpha.Pc.p570 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f42

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v574 : Nat := CFSG.KD.Fi24Alpha.KV4 47
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v575 : Nat := CFSG.KD.Fi24Alpha.KV4 48
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l576 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v574, CFSG.KD.Fi24Alpha.Pc.v575]
theorem CFSG.KD.Fi24Alpha.Pc.p574 : Nat.beq (runC AR SD 574 (ckL CFSG.KD.Fi24Alpha.Pc.l576) 2 574 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v576 : Nat := CFSG.KD.Fi24Alpha.KV4 49
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v577 : Nat := CFSG.KD.Fi24Alpha.KV4 50
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l578 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v574, CFSG.KD.Fi24Alpha.Pc.v575, CFSG.KD.Fi24Alpha.Pc.v576, CFSG.KD.Fi24Alpha.Pc.v577]
theorem CFSG.KD.Fi24Alpha.Pc.p576 : Nat.beq (runC AR SD 574 (ckL CFSG.KD.Fi24Alpha.Pc.l578) 2 576 CFSG.KD.Fi24Alpha.Pc.l576) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v578 : Nat := CFSG.KD.Fi24Alpha.KV4 51
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v579 : Nat := CFSG.KD.Fi24Alpha.KV4 52
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l580 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v574, CFSG.KD.Fi24Alpha.Pc.v575, CFSG.KD.Fi24Alpha.Pc.v576, CFSG.KD.Fi24Alpha.Pc.v577, CFSG.KD.Fi24Alpha.Pc.v578, CFSG.KD.Fi24Alpha.Pc.v579]
theorem CFSG.KD.Fi24Alpha.Pc.p578 : Nat.beq (runC AR SD 574 (ckL CFSG.KD.Fi24Alpha.Pc.l580) 2 578 CFSG.KD.Fi24Alpha.Pc.l578) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v580 : Nat := CFSG.KD.Fi24Alpha.KV4 53
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v581 : Nat := CFSG.KD.Fi24Alpha.KV4 54
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l582 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v574, CFSG.KD.Fi24Alpha.Pc.v575, CFSG.KD.Fi24Alpha.Pc.v576, CFSG.KD.Fi24Alpha.Pc.v577, CFSG.KD.Fi24Alpha.Pc.v578, CFSG.KD.Fi24Alpha.Pc.v579, CFSG.KD.Fi24Alpha.Pc.v580, CFSG.KD.Fi24Alpha.Pc.v581]
theorem CFSG.KD.Fi24Alpha.Pc.p580 : Nat.beq (runC AR SD 574 (ckL CFSG.KD.Fi24Alpha.Pc.l582) 2 580 CFSG.KD.Fi24Alpha.Pc.l580) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v582 : Nat := CFSG.KD.Fi24Alpha.KV4 55
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v583 : Nat := CFSG.KD.Fi24Alpha.KV4 56
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l584 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v574, CFSG.KD.Fi24Alpha.Pc.v575, CFSG.KD.Fi24Alpha.Pc.v576, CFSG.KD.Fi24Alpha.Pc.v577, CFSG.KD.Fi24Alpha.Pc.v578, CFSG.KD.Fi24Alpha.Pc.v579, CFSG.KD.Fi24Alpha.Pc.v580, CFSG.KD.Fi24Alpha.Pc.v581, CFSG.KD.Fi24Alpha.Pc.v582, CFSG.KD.Fi24Alpha.Pc.v583]
theorem CFSG.KD.Fi24Alpha.Pc.p582 : Nat.beq (runC AR SD 574 (ckL CFSG.KD.Fi24Alpha.Pc.l584) 2 582 CFSG.KD.Fi24Alpha.Pc.l582) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v584 : Nat := CFSG.KD.Fi24Alpha.KV4 57
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v585 : Nat := CFSG.KD.Fi24Alpha.KV4 58
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l586 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v574, CFSG.KD.Fi24Alpha.Pc.v575, CFSG.KD.Fi24Alpha.Pc.v576, CFSG.KD.Fi24Alpha.Pc.v577, CFSG.KD.Fi24Alpha.Pc.v578, CFSG.KD.Fi24Alpha.Pc.v579, CFSG.KD.Fi24Alpha.Pc.v580, CFSG.KD.Fi24Alpha.Pc.v581, CFSG.KD.Fi24Alpha.Pc.v582, CFSG.KD.Fi24Alpha.Pc.v583, CFSG.KD.Fi24Alpha.Pc.v584, CFSG.KD.Fi24Alpha.Pc.v585]
theorem CFSG.KD.Fi24Alpha.Pc.p584 : Nat.beq (runC AR SD 574 (ckL CFSG.KD.Fi24Alpha.Pc.l586) 2 584 CFSG.KD.Fi24Alpha.Pc.l584) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v586 : Nat := CFSG.KD.Fi24Alpha.KV4 59
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v587 : Nat := CFSG.KD.Fi24Alpha.KV4 60
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l588 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v574, CFSG.KD.Fi24Alpha.Pc.v575, CFSG.KD.Fi24Alpha.Pc.v576, CFSG.KD.Fi24Alpha.Pc.v577, CFSG.KD.Fi24Alpha.Pc.v578, CFSG.KD.Fi24Alpha.Pc.v579, CFSG.KD.Fi24Alpha.Pc.v580, CFSG.KD.Fi24Alpha.Pc.v581, CFSG.KD.Fi24Alpha.Pc.v582, CFSG.KD.Fi24Alpha.Pc.v583, CFSG.KD.Fi24Alpha.Pc.v584, CFSG.KD.Fi24Alpha.Pc.v585, CFSG.KD.Fi24Alpha.Pc.v586, CFSG.KD.Fi24Alpha.Pc.v587]
theorem CFSG.KD.Fi24Alpha.Pc.p586 : Nat.beq (runC AR SD 574 (ckL CFSG.KD.Fi24Alpha.Pc.l588) 2 586 CFSG.KD.Fi24Alpha.Pc.l586) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v588 : Nat := CFSG.KD.Fi24Alpha.KV4 61
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v589 : Nat := CFSG.KD.Fi24Alpha.KV4 62
theorem CFSG.KD.Fi24Alpha.Pc.f43 : Nat.beq (runC AR SD 574 (finC AR SD (nat_lit 43) 574 590) 2 588 CFSG.KD.Fi24Alpha.Pc.l588) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk43 : chk (nat_lit 43) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 43) (lo := 574) (hi := 590) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 576) CFSG.KD.Fi24Alpha.Pc.p574 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 578) CFSG.KD.Fi24Alpha.Pc.p576 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 580) CFSG.KD.Fi24Alpha.Pc.p578 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 582) CFSG.KD.Fi24Alpha.Pc.p580 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 584) CFSG.KD.Fi24Alpha.Pc.p582 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 586) CFSG.KD.Fi24Alpha.Pc.p584 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 588) CFSG.KD.Fi24Alpha.Pc.p586 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f43

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v590 : Nat := CFSG.KD.Fi24Alpha.KV4 63
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v591 : Nat := CFSG.KD.Fi24Alpha.KV4 64
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l592 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v590, CFSG.KD.Fi24Alpha.Pc.v591]
theorem CFSG.KD.Fi24Alpha.Pc.p590 : Nat.beq (runC AR SD 590 (ckL CFSG.KD.Fi24Alpha.Pc.l592) 2 590 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v592 : Nat := CFSG.KD.Fi24Alpha.KV4 65
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v593 : Nat := CFSG.KD.Fi24Alpha.KV4 66
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l594 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v590, CFSG.KD.Fi24Alpha.Pc.v591, CFSG.KD.Fi24Alpha.Pc.v592, CFSG.KD.Fi24Alpha.Pc.v593]
theorem CFSG.KD.Fi24Alpha.Pc.p592 : Nat.beq (runC AR SD 590 (ckL CFSG.KD.Fi24Alpha.Pc.l594) 2 592 CFSG.KD.Fi24Alpha.Pc.l592) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v594 : Nat := CFSG.KD.Fi24Alpha.KV4 67
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v595 : Nat := CFSG.KD.Fi24Alpha.KV4 68
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l596 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v590, CFSG.KD.Fi24Alpha.Pc.v591, CFSG.KD.Fi24Alpha.Pc.v592, CFSG.KD.Fi24Alpha.Pc.v593, CFSG.KD.Fi24Alpha.Pc.v594, CFSG.KD.Fi24Alpha.Pc.v595]
theorem CFSG.KD.Fi24Alpha.Pc.p594 : Nat.beq (runC AR SD 590 (ckL CFSG.KD.Fi24Alpha.Pc.l596) 2 594 CFSG.KD.Fi24Alpha.Pc.l594) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v596 : Nat := CFSG.KD.Fi24Alpha.KV4 69
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v597 : Nat := CFSG.KD.Fi24Alpha.KV4 70
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l598 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v590, CFSG.KD.Fi24Alpha.Pc.v591, CFSG.KD.Fi24Alpha.Pc.v592, CFSG.KD.Fi24Alpha.Pc.v593, CFSG.KD.Fi24Alpha.Pc.v594, CFSG.KD.Fi24Alpha.Pc.v595, CFSG.KD.Fi24Alpha.Pc.v596, CFSG.KD.Fi24Alpha.Pc.v597]
theorem CFSG.KD.Fi24Alpha.Pc.p596 : Nat.beq (runC AR SD 590 (ckL CFSG.KD.Fi24Alpha.Pc.l598) 2 596 CFSG.KD.Fi24Alpha.Pc.l596) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v598 : Nat := CFSG.KD.Fi24Alpha.KV4 71
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v599 : Nat := CFSG.KD.Fi24Alpha.KV4 72
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l600 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v590, CFSG.KD.Fi24Alpha.Pc.v591, CFSG.KD.Fi24Alpha.Pc.v592, CFSG.KD.Fi24Alpha.Pc.v593, CFSG.KD.Fi24Alpha.Pc.v594, CFSG.KD.Fi24Alpha.Pc.v595, CFSG.KD.Fi24Alpha.Pc.v596, CFSG.KD.Fi24Alpha.Pc.v597, CFSG.KD.Fi24Alpha.Pc.v598, CFSG.KD.Fi24Alpha.Pc.v599]
theorem CFSG.KD.Fi24Alpha.Pc.p598 : Nat.beq (runC AR SD 590 (ckL CFSG.KD.Fi24Alpha.Pc.l600) 2 598 CFSG.KD.Fi24Alpha.Pc.l598) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v600 : Nat := CFSG.KD.Fi24Alpha.KV4 73
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v601 : Nat := CFSG.KD.Fi24Alpha.KV4 74
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l602 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v590, CFSG.KD.Fi24Alpha.Pc.v591, CFSG.KD.Fi24Alpha.Pc.v592, CFSG.KD.Fi24Alpha.Pc.v593, CFSG.KD.Fi24Alpha.Pc.v594, CFSG.KD.Fi24Alpha.Pc.v595, CFSG.KD.Fi24Alpha.Pc.v596, CFSG.KD.Fi24Alpha.Pc.v597, CFSG.KD.Fi24Alpha.Pc.v598, CFSG.KD.Fi24Alpha.Pc.v599, CFSG.KD.Fi24Alpha.Pc.v600, CFSG.KD.Fi24Alpha.Pc.v601]
theorem CFSG.KD.Fi24Alpha.Pc.p600 : Nat.beq (runC AR SD 590 (ckL CFSG.KD.Fi24Alpha.Pc.l602) 2 600 CFSG.KD.Fi24Alpha.Pc.l600) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v602 : Nat := CFSG.KD.Fi24Alpha.KV4 75
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v603 : Nat := CFSG.KD.Fi24Alpha.KV4 76
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l604 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v590, CFSG.KD.Fi24Alpha.Pc.v591, CFSG.KD.Fi24Alpha.Pc.v592, CFSG.KD.Fi24Alpha.Pc.v593, CFSG.KD.Fi24Alpha.Pc.v594, CFSG.KD.Fi24Alpha.Pc.v595, CFSG.KD.Fi24Alpha.Pc.v596, CFSG.KD.Fi24Alpha.Pc.v597, CFSG.KD.Fi24Alpha.Pc.v598, CFSG.KD.Fi24Alpha.Pc.v599, CFSG.KD.Fi24Alpha.Pc.v600, CFSG.KD.Fi24Alpha.Pc.v601, CFSG.KD.Fi24Alpha.Pc.v602, CFSG.KD.Fi24Alpha.Pc.v603]
theorem CFSG.KD.Fi24Alpha.Pc.p602 : Nat.beq (runC AR SD 590 (ckL CFSG.KD.Fi24Alpha.Pc.l604) 2 602 CFSG.KD.Fi24Alpha.Pc.l602) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v604 : Nat := CFSG.KD.Fi24Alpha.KV4 77
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v605 : Nat := CFSG.KD.Fi24Alpha.KV4 78
theorem CFSG.KD.Fi24Alpha.Pc.f44 : Nat.beq (runC AR SD 590 (finC AR SD (nat_lit 44) 590 606) 2 604 CFSG.KD.Fi24Alpha.Pc.l604) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk44 : chk (nat_lit 44) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 44) (lo := 590) (hi := 606) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 592) CFSG.KD.Fi24Alpha.Pc.p590 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 594) CFSG.KD.Fi24Alpha.Pc.p592 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 596) CFSG.KD.Fi24Alpha.Pc.p594 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 598) CFSG.KD.Fi24Alpha.Pc.p596 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 600) CFSG.KD.Fi24Alpha.Pc.p598 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 602) CFSG.KD.Fi24Alpha.Pc.p600 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 604) CFSG.KD.Fi24Alpha.Pc.p602 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f44

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v606 : Nat := CFSG.KD.Fi24Alpha.KV4 79
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v607 : Nat := CFSG.KD.Fi24Alpha.KV4 80
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l608 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v606, CFSG.KD.Fi24Alpha.Pc.v607]
theorem CFSG.KD.Fi24Alpha.Pc.p606 : Nat.beq (runC AR SD 606 (ckL CFSG.KD.Fi24Alpha.Pc.l608) 2 606 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v608 : Nat := CFSG.KD.Fi24Alpha.KV4 81
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v609 : Nat := CFSG.KD.Fi24Alpha.KV4 82
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l610 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v606, CFSG.KD.Fi24Alpha.Pc.v607, CFSG.KD.Fi24Alpha.Pc.v608, CFSG.KD.Fi24Alpha.Pc.v609]
theorem CFSG.KD.Fi24Alpha.Pc.p608 : Nat.beq (runC AR SD 606 (ckL CFSG.KD.Fi24Alpha.Pc.l610) 2 608 CFSG.KD.Fi24Alpha.Pc.l608) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v610 : Nat := CFSG.KD.Fi24Alpha.KV4 83
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v611 : Nat := CFSG.KD.Fi24Alpha.KV4 84
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l612 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v606, CFSG.KD.Fi24Alpha.Pc.v607, CFSG.KD.Fi24Alpha.Pc.v608, CFSG.KD.Fi24Alpha.Pc.v609, CFSG.KD.Fi24Alpha.Pc.v610, CFSG.KD.Fi24Alpha.Pc.v611]
theorem CFSG.KD.Fi24Alpha.Pc.p610 : Nat.beq (runC AR SD 606 (ckL CFSG.KD.Fi24Alpha.Pc.l612) 2 610 CFSG.KD.Fi24Alpha.Pc.l610) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v612 : Nat := CFSG.KD.Fi24Alpha.KV4 85
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v613 : Nat := CFSG.KD.Fi24Alpha.KV4 86
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l614 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v606, CFSG.KD.Fi24Alpha.Pc.v607, CFSG.KD.Fi24Alpha.Pc.v608, CFSG.KD.Fi24Alpha.Pc.v609, CFSG.KD.Fi24Alpha.Pc.v610, CFSG.KD.Fi24Alpha.Pc.v611, CFSG.KD.Fi24Alpha.Pc.v612, CFSG.KD.Fi24Alpha.Pc.v613]
theorem CFSG.KD.Fi24Alpha.Pc.p612 : Nat.beq (runC AR SD 606 (ckL CFSG.KD.Fi24Alpha.Pc.l614) 2 612 CFSG.KD.Fi24Alpha.Pc.l612) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v614 : Nat := CFSG.KD.Fi24Alpha.KV4 87
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v615 : Nat := CFSG.KD.Fi24Alpha.KV4 88
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l616 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v606, CFSG.KD.Fi24Alpha.Pc.v607, CFSG.KD.Fi24Alpha.Pc.v608, CFSG.KD.Fi24Alpha.Pc.v609, CFSG.KD.Fi24Alpha.Pc.v610, CFSG.KD.Fi24Alpha.Pc.v611, CFSG.KD.Fi24Alpha.Pc.v612, CFSG.KD.Fi24Alpha.Pc.v613, CFSG.KD.Fi24Alpha.Pc.v614, CFSG.KD.Fi24Alpha.Pc.v615]
theorem CFSG.KD.Fi24Alpha.Pc.p614 : Nat.beq (runC AR SD 606 (ckL CFSG.KD.Fi24Alpha.Pc.l616) 2 614 CFSG.KD.Fi24Alpha.Pc.l614) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v616 : Nat := CFSG.KD.Fi24Alpha.KV4 89
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v617 : Nat := CFSG.KD.Fi24Alpha.KV4 90
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l618 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v606, CFSG.KD.Fi24Alpha.Pc.v607, CFSG.KD.Fi24Alpha.Pc.v608, CFSG.KD.Fi24Alpha.Pc.v609, CFSG.KD.Fi24Alpha.Pc.v610, CFSG.KD.Fi24Alpha.Pc.v611, CFSG.KD.Fi24Alpha.Pc.v612, CFSG.KD.Fi24Alpha.Pc.v613, CFSG.KD.Fi24Alpha.Pc.v614, CFSG.KD.Fi24Alpha.Pc.v615, CFSG.KD.Fi24Alpha.Pc.v616, CFSG.KD.Fi24Alpha.Pc.v617]
theorem CFSG.KD.Fi24Alpha.Pc.p616 : Nat.beq (runC AR SD 606 (ckL CFSG.KD.Fi24Alpha.Pc.l618) 2 616 CFSG.KD.Fi24Alpha.Pc.l616) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v618 : Nat := CFSG.KD.Fi24Alpha.KV4 91
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v619 : Nat := CFSG.KD.Fi24Alpha.KV4 92
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l620 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v606, CFSG.KD.Fi24Alpha.Pc.v607, CFSG.KD.Fi24Alpha.Pc.v608, CFSG.KD.Fi24Alpha.Pc.v609, CFSG.KD.Fi24Alpha.Pc.v610, CFSG.KD.Fi24Alpha.Pc.v611, CFSG.KD.Fi24Alpha.Pc.v612, CFSG.KD.Fi24Alpha.Pc.v613, CFSG.KD.Fi24Alpha.Pc.v614, CFSG.KD.Fi24Alpha.Pc.v615, CFSG.KD.Fi24Alpha.Pc.v616, CFSG.KD.Fi24Alpha.Pc.v617, CFSG.KD.Fi24Alpha.Pc.v618, CFSG.KD.Fi24Alpha.Pc.v619]
theorem CFSG.KD.Fi24Alpha.Pc.p618 : Nat.beq (runC AR SD 606 (ckL CFSG.KD.Fi24Alpha.Pc.l620) 2 618 CFSG.KD.Fi24Alpha.Pc.l618) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v620 : Nat := CFSG.KD.Fi24Alpha.KV4 93
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v621 : Nat := CFSG.KD.Fi24Alpha.KV4 94
theorem CFSG.KD.Fi24Alpha.Pc.f45 : Nat.beq (runC AR SD 606 (finC AR SD (nat_lit 45) 606 622) 2 620 CFSG.KD.Fi24Alpha.Pc.l620) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk45 : chk (nat_lit 45) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 45) (lo := 606) (hi := 622) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 608) CFSG.KD.Fi24Alpha.Pc.p606 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 610) CFSG.KD.Fi24Alpha.Pc.p608 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 612) CFSG.KD.Fi24Alpha.Pc.p610 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 614) CFSG.KD.Fi24Alpha.Pc.p612 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 616) CFSG.KD.Fi24Alpha.Pc.p614 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 618) CFSG.KD.Fi24Alpha.Pc.p616 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 620) CFSG.KD.Fi24Alpha.Pc.p618 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f45

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v622 : Nat := CFSG.KD.Fi24Alpha.KV4 95
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v623 : Nat := CFSG.KD.Fi24Alpha.KV4 96
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l624 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v622, CFSG.KD.Fi24Alpha.Pc.v623]
theorem CFSG.KD.Fi24Alpha.Pc.p622 : Nat.beq (runC AR SD 622 (ckL CFSG.KD.Fi24Alpha.Pc.l624) 2 622 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v624 : Nat := CFSG.KD.Fi24Alpha.KV4 97
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v625 : Nat := CFSG.KD.Fi24Alpha.KV4 98
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l626 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v622, CFSG.KD.Fi24Alpha.Pc.v623, CFSG.KD.Fi24Alpha.Pc.v624, CFSG.KD.Fi24Alpha.Pc.v625]
theorem CFSG.KD.Fi24Alpha.Pc.p624 : Nat.beq (runC AR SD 622 (ckL CFSG.KD.Fi24Alpha.Pc.l626) 2 624 CFSG.KD.Fi24Alpha.Pc.l624) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v626 : Nat := CFSG.KD.Fi24Alpha.KV4 99
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v627 : Nat := CFSG.KD.Fi24Alpha.KV4 100
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l628 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v622, CFSG.KD.Fi24Alpha.Pc.v623, CFSG.KD.Fi24Alpha.Pc.v624, CFSG.KD.Fi24Alpha.Pc.v625, CFSG.KD.Fi24Alpha.Pc.v626, CFSG.KD.Fi24Alpha.Pc.v627]
theorem CFSG.KD.Fi24Alpha.Pc.p626 : Nat.beq (runC AR SD 622 (ckL CFSG.KD.Fi24Alpha.Pc.l628) 2 626 CFSG.KD.Fi24Alpha.Pc.l626) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v628 : Nat := CFSG.KD.Fi24Alpha.KV4 101
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v629 : Nat := CFSG.KD.Fi24Alpha.KV4 102
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l630 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v622, CFSG.KD.Fi24Alpha.Pc.v623, CFSG.KD.Fi24Alpha.Pc.v624, CFSG.KD.Fi24Alpha.Pc.v625, CFSG.KD.Fi24Alpha.Pc.v626, CFSG.KD.Fi24Alpha.Pc.v627, CFSG.KD.Fi24Alpha.Pc.v628, CFSG.KD.Fi24Alpha.Pc.v629]
theorem CFSG.KD.Fi24Alpha.Pc.p628 : Nat.beq (runC AR SD 622 (ckL CFSG.KD.Fi24Alpha.Pc.l630) 2 628 CFSG.KD.Fi24Alpha.Pc.l628) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v630 : Nat := CFSG.KD.Fi24Alpha.KV4 103
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v631 : Nat := CFSG.KD.Fi24Alpha.KV4 104
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l632 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v622, CFSG.KD.Fi24Alpha.Pc.v623, CFSG.KD.Fi24Alpha.Pc.v624, CFSG.KD.Fi24Alpha.Pc.v625, CFSG.KD.Fi24Alpha.Pc.v626, CFSG.KD.Fi24Alpha.Pc.v627, CFSG.KD.Fi24Alpha.Pc.v628, CFSG.KD.Fi24Alpha.Pc.v629, CFSG.KD.Fi24Alpha.Pc.v630, CFSG.KD.Fi24Alpha.Pc.v631]
theorem CFSG.KD.Fi24Alpha.Pc.p630 : Nat.beq (runC AR SD 622 (ckL CFSG.KD.Fi24Alpha.Pc.l632) 2 630 CFSG.KD.Fi24Alpha.Pc.l630) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v632 : Nat := CFSG.KD.Fi24Alpha.KV4 105
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v633 : Nat := CFSG.KD.Fi24Alpha.KV4 106
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l634 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v622, CFSG.KD.Fi24Alpha.Pc.v623, CFSG.KD.Fi24Alpha.Pc.v624, CFSG.KD.Fi24Alpha.Pc.v625, CFSG.KD.Fi24Alpha.Pc.v626, CFSG.KD.Fi24Alpha.Pc.v627, CFSG.KD.Fi24Alpha.Pc.v628, CFSG.KD.Fi24Alpha.Pc.v629, CFSG.KD.Fi24Alpha.Pc.v630, CFSG.KD.Fi24Alpha.Pc.v631, CFSG.KD.Fi24Alpha.Pc.v632, CFSG.KD.Fi24Alpha.Pc.v633]
theorem CFSG.KD.Fi24Alpha.Pc.p632 : Nat.beq (runC AR SD 622 (ckL CFSG.KD.Fi24Alpha.Pc.l634) 2 632 CFSG.KD.Fi24Alpha.Pc.l632) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v634 : Nat := CFSG.KD.Fi24Alpha.KV4 107
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v635 : Nat := CFSG.KD.Fi24Alpha.KV4 108
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l636 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v622, CFSG.KD.Fi24Alpha.Pc.v623, CFSG.KD.Fi24Alpha.Pc.v624, CFSG.KD.Fi24Alpha.Pc.v625, CFSG.KD.Fi24Alpha.Pc.v626, CFSG.KD.Fi24Alpha.Pc.v627, CFSG.KD.Fi24Alpha.Pc.v628, CFSG.KD.Fi24Alpha.Pc.v629, CFSG.KD.Fi24Alpha.Pc.v630, CFSG.KD.Fi24Alpha.Pc.v631, CFSG.KD.Fi24Alpha.Pc.v632, CFSG.KD.Fi24Alpha.Pc.v633, CFSG.KD.Fi24Alpha.Pc.v634, CFSG.KD.Fi24Alpha.Pc.v635]
theorem CFSG.KD.Fi24Alpha.Pc.p634 : Nat.beq (runC AR SD 622 (ckL CFSG.KD.Fi24Alpha.Pc.l636) 2 634 CFSG.KD.Fi24Alpha.Pc.l634) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v636 : Nat := CFSG.KD.Fi24Alpha.KV4 109
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v637 : Nat := CFSG.KD.Fi24Alpha.KV4 110
theorem CFSG.KD.Fi24Alpha.Pc.f46 : Nat.beq (runC AR SD 622 (finC AR SD (nat_lit 46) 622 638) 2 636 CFSG.KD.Fi24Alpha.Pc.l636) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk46 : chk (nat_lit 46) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 46) (lo := 622) (hi := 638) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 624) CFSG.KD.Fi24Alpha.Pc.p622 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 626) CFSG.KD.Fi24Alpha.Pc.p624 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 628) CFSG.KD.Fi24Alpha.Pc.p626 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 630) CFSG.KD.Fi24Alpha.Pc.p628 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 632) CFSG.KD.Fi24Alpha.Pc.p630 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 634) CFSG.KD.Fi24Alpha.Pc.p632 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 636) CFSG.KD.Fi24Alpha.Pc.p634 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f46

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v638 : Nat := CFSG.KD.Fi24Alpha.KV4 111
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v639 : Nat := CFSG.KD.Fi24Alpha.KV4 112
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l640 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v638, CFSG.KD.Fi24Alpha.Pc.v639]
theorem CFSG.KD.Fi24Alpha.Pc.p638 : Nat.beq (runC AR SD 638 (ckL CFSG.KD.Fi24Alpha.Pc.l640) 2 638 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v640 : Nat := CFSG.KD.Fi24Alpha.KV4 113
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v641 : Nat := CFSG.KD.Fi24Alpha.KV4 114
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l642 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v638, CFSG.KD.Fi24Alpha.Pc.v639, CFSG.KD.Fi24Alpha.Pc.v640, CFSG.KD.Fi24Alpha.Pc.v641]
theorem CFSG.KD.Fi24Alpha.Pc.p640 : Nat.beq (runC AR SD 638 (ckL CFSG.KD.Fi24Alpha.Pc.l642) 2 640 CFSG.KD.Fi24Alpha.Pc.l640) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v642 : Nat := CFSG.KD.Fi24Alpha.KV4 115
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l643 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v638, CFSG.KD.Fi24Alpha.Pc.v639, CFSG.KD.Fi24Alpha.Pc.v640, CFSG.KD.Fi24Alpha.Pc.v641, CFSG.KD.Fi24Alpha.Pc.v642]
theorem CFSG.KD.Fi24Alpha.Pc.p642 : Nat.beq (runC AR SD 638 (ckL CFSG.KD.Fi24Alpha.Pc.l643) 1 642 CFSG.KD.Fi24Alpha.Pc.l642) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v643 : Nat := CFSG.KD.Fi24Alpha.KV4 116
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v644 : Nat := CFSG.KD.Fi24Alpha.KV4 117
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l645 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v638, CFSG.KD.Fi24Alpha.Pc.v639, CFSG.KD.Fi24Alpha.Pc.v640, CFSG.KD.Fi24Alpha.Pc.v641, CFSG.KD.Fi24Alpha.Pc.v642, CFSG.KD.Fi24Alpha.Pc.v643, CFSG.KD.Fi24Alpha.Pc.v644]
theorem CFSG.KD.Fi24Alpha.Pc.p643 : Nat.beq (runC AR SD 638 (ckL CFSG.KD.Fi24Alpha.Pc.l645) 2 643 CFSG.KD.Fi24Alpha.Pc.l643) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v645 : Nat := CFSG.KD.Fi24Alpha.KV4 118
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v646 : Nat := CFSG.KD.Fi24Alpha.KV4 119
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l647 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v638, CFSG.KD.Fi24Alpha.Pc.v639, CFSG.KD.Fi24Alpha.Pc.v640, CFSG.KD.Fi24Alpha.Pc.v641, CFSG.KD.Fi24Alpha.Pc.v642, CFSG.KD.Fi24Alpha.Pc.v643, CFSG.KD.Fi24Alpha.Pc.v644, CFSG.KD.Fi24Alpha.Pc.v645, CFSG.KD.Fi24Alpha.Pc.v646]
theorem CFSG.KD.Fi24Alpha.Pc.p645 : Nat.beq (runC AR SD 638 (ckL CFSG.KD.Fi24Alpha.Pc.l647) 2 645 CFSG.KD.Fi24Alpha.Pc.l645) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v647 : Nat := CFSG.KD.Fi24Alpha.KV4 120
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v648 : Nat := CFSG.KD.Fi24Alpha.KV4 121
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l649 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v638, CFSG.KD.Fi24Alpha.Pc.v639, CFSG.KD.Fi24Alpha.Pc.v640, CFSG.KD.Fi24Alpha.Pc.v641, CFSG.KD.Fi24Alpha.Pc.v642, CFSG.KD.Fi24Alpha.Pc.v643, CFSG.KD.Fi24Alpha.Pc.v644, CFSG.KD.Fi24Alpha.Pc.v645, CFSG.KD.Fi24Alpha.Pc.v646, CFSG.KD.Fi24Alpha.Pc.v647, CFSG.KD.Fi24Alpha.Pc.v648]
theorem CFSG.KD.Fi24Alpha.Pc.p647 : Nat.beq (runC AR SD 638 (ckL CFSG.KD.Fi24Alpha.Pc.l649) 2 647 CFSG.KD.Fi24Alpha.Pc.l647) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v649 : Nat := CFSG.KD.Fi24Alpha.KV4 122
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v650 : Nat := CFSG.KD.Fi24Alpha.KV4 123
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l651 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v638, CFSG.KD.Fi24Alpha.Pc.v639, CFSG.KD.Fi24Alpha.Pc.v640, CFSG.KD.Fi24Alpha.Pc.v641, CFSG.KD.Fi24Alpha.Pc.v642, CFSG.KD.Fi24Alpha.Pc.v643, CFSG.KD.Fi24Alpha.Pc.v644, CFSG.KD.Fi24Alpha.Pc.v645, CFSG.KD.Fi24Alpha.Pc.v646, CFSG.KD.Fi24Alpha.Pc.v647, CFSG.KD.Fi24Alpha.Pc.v648, CFSG.KD.Fi24Alpha.Pc.v649, CFSG.KD.Fi24Alpha.Pc.v650]
theorem CFSG.KD.Fi24Alpha.Pc.p649 : Nat.beq (runC AR SD 638 (ckL CFSG.KD.Fi24Alpha.Pc.l651) 2 649 CFSG.KD.Fi24Alpha.Pc.l649) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v651 : Nat := CFSG.KD.Fi24Alpha.KV4 124
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v652 : Nat := CFSG.KD.Fi24Alpha.KV4 125
theorem CFSG.KD.Fi24Alpha.Pc.f47 : Nat.beq (runC AR SD 638 (finC AR SD (nat_lit 47) 638 653) 2 651 CFSG.KD.Fi24Alpha.Pc.l651) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk47 : chk (nat_lit 47) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 47) (lo := 638) (hi := 653) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 640) CFSG.KD.Fi24Alpha.Pc.p638 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 642) CFSG.KD.Fi24Alpha.Pc.p640 rfl rfl).trans ((runC_seq (m := 11) (m2 := 10) (j2 := 643) CFSG.KD.Fi24Alpha.Pc.p642 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 645) CFSG.KD.Fi24Alpha.Pc.p643 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 647) CFSG.KD.Fi24Alpha.Pc.p645 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 649) CFSG.KD.Fi24Alpha.Pc.p647 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 651) CFSG.KD.Fi24Alpha.Pc.p649 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f47

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v653 : Nat := CFSG.KD.Fi24Alpha.KV4 126
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v654 : Nat := CFSG.KD.Fi24Alpha.KV4 127
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l655 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v653, CFSG.KD.Fi24Alpha.Pc.v654]
theorem CFSG.KD.Fi24Alpha.Pc.p653 : Nat.beq (runC AR SD 653 (ckL CFSG.KD.Fi24Alpha.Pc.l655) 2 653 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v655 : Nat := CFSG.KD.Fi24Alpha.KV4 128
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v656 : Nat := CFSG.KD.Fi24Alpha.KV4 129
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l657 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v653, CFSG.KD.Fi24Alpha.Pc.v654, CFSG.KD.Fi24Alpha.Pc.v655, CFSG.KD.Fi24Alpha.Pc.v656]
theorem CFSG.KD.Fi24Alpha.Pc.p655 : Nat.beq (runC AR SD 653 (ckL CFSG.KD.Fi24Alpha.Pc.l657) 2 655 CFSG.KD.Fi24Alpha.Pc.l655) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v657 : Nat := CFSG.KD.Fi24Alpha.KV4 130
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v658 : Nat := CFSG.KD.Fi24Alpha.KV4 131
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l659 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v653, CFSG.KD.Fi24Alpha.Pc.v654, CFSG.KD.Fi24Alpha.Pc.v655, CFSG.KD.Fi24Alpha.Pc.v656, CFSG.KD.Fi24Alpha.Pc.v657, CFSG.KD.Fi24Alpha.Pc.v658]
theorem CFSG.KD.Fi24Alpha.Pc.p657 : Nat.beq (runC AR SD 653 (ckL CFSG.KD.Fi24Alpha.Pc.l659) 2 657 CFSG.KD.Fi24Alpha.Pc.l657) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v659 : Nat := CFSG.KD.Fi24Alpha.KV4 132
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v660 : Nat := CFSG.KD.Fi24Alpha.KV4 133
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l661 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v653, CFSG.KD.Fi24Alpha.Pc.v654, CFSG.KD.Fi24Alpha.Pc.v655, CFSG.KD.Fi24Alpha.Pc.v656, CFSG.KD.Fi24Alpha.Pc.v657, CFSG.KD.Fi24Alpha.Pc.v658, CFSG.KD.Fi24Alpha.Pc.v659, CFSG.KD.Fi24Alpha.Pc.v660]
theorem CFSG.KD.Fi24Alpha.Pc.p659 : Nat.beq (runC AR SD 653 (ckL CFSG.KD.Fi24Alpha.Pc.l661) 2 659 CFSG.KD.Fi24Alpha.Pc.l659) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v661 : Nat := CFSG.KD.Fi24Alpha.KV4 134
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v662 : Nat := CFSG.KD.Fi24Alpha.KV4 135
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l663 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v653, CFSG.KD.Fi24Alpha.Pc.v654, CFSG.KD.Fi24Alpha.Pc.v655, CFSG.KD.Fi24Alpha.Pc.v656, CFSG.KD.Fi24Alpha.Pc.v657, CFSG.KD.Fi24Alpha.Pc.v658, CFSG.KD.Fi24Alpha.Pc.v659, CFSG.KD.Fi24Alpha.Pc.v660, CFSG.KD.Fi24Alpha.Pc.v661, CFSG.KD.Fi24Alpha.Pc.v662]
theorem CFSG.KD.Fi24Alpha.Pc.p661 : Nat.beq (runC AR SD 653 (ckL CFSG.KD.Fi24Alpha.Pc.l663) 2 661 CFSG.KD.Fi24Alpha.Pc.l661) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v663 : Nat := CFSG.KD.Fi24Alpha.KV4 136
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l664 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v653, CFSG.KD.Fi24Alpha.Pc.v654, CFSG.KD.Fi24Alpha.Pc.v655, CFSG.KD.Fi24Alpha.Pc.v656, CFSG.KD.Fi24Alpha.Pc.v657, CFSG.KD.Fi24Alpha.Pc.v658, CFSG.KD.Fi24Alpha.Pc.v659, CFSG.KD.Fi24Alpha.Pc.v660, CFSG.KD.Fi24Alpha.Pc.v661, CFSG.KD.Fi24Alpha.Pc.v662, CFSG.KD.Fi24Alpha.Pc.v663]
theorem CFSG.KD.Fi24Alpha.Pc.p663 : Nat.beq (runC AR SD 653 (ckL CFSG.KD.Fi24Alpha.Pc.l664) 1 663 CFSG.KD.Fi24Alpha.Pc.l663) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v664 : Nat := CFSG.KD.Fi24Alpha.KV4 137
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v665 : Nat := CFSG.KD.Fi24Alpha.KV4 138
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l666 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v653, CFSG.KD.Fi24Alpha.Pc.v654, CFSG.KD.Fi24Alpha.Pc.v655, CFSG.KD.Fi24Alpha.Pc.v656, CFSG.KD.Fi24Alpha.Pc.v657, CFSG.KD.Fi24Alpha.Pc.v658, CFSG.KD.Fi24Alpha.Pc.v659, CFSG.KD.Fi24Alpha.Pc.v660, CFSG.KD.Fi24Alpha.Pc.v661, CFSG.KD.Fi24Alpha.Pc.v662, CFSG.KD.Fi24Alpha.Pc.v663, CFSG.KD.Fi24Alpha.Pc.v664, CFSG.KD.Fi24Alpha.Pc.v665]
theorem CFSG.KD.Fi24Alpha.Pc.p664 : Nat.beq (runC AR SD 653 (ckL CFSG.KD.Fi24Alpha.Pc.l666) 2 664 CFSG.KD.Fi24Alpha.Pc.l664) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v666 : Nat := CFSG.KD.Fi24Alpha.KV4 139
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v667 : Nat := CFSG.KD.Fi24Alpha.KV4 140
theorem CFSG.KD.Fi24Alpha.Pc.f48 : Nat.beq (runC AR SD 653 (finC AR SD (nat_lit 48) 653 668) 2 666 CFSG.KD.Fi24Alpha.Pc.l666) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk48 : chk (nat_lit 48) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 48) (lo := 653) (hi := 668) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 655) CFSG.KD.Fi24Alpha.Pc.p653 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 657) CFSG.KD.Fi24Alpha.Pc.p655 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 659) CFSG.KD.Fi24Alpha.Pc.p657 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 661) CFSG.KD.Fi24Alpha.Pc.p659 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 663) CFSG.KD.Fi24Alpha.Pc.p661 rfl rfl).trans ((runC_seq (m := 5) (m2 := 4) (j2 := 664) CFSG.KD.Fi24Alpha.Pc.p663 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 666) CFSG.KD.Fi24Alpha.Pc.p664 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f48

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v668 : Nat := CFSG.KD.Fi24Alpha.KV4 141
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v669 : Nat := CFSG.KD.Fi24Alpha.KV4 142
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l670 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v668, CFSG.KD.Fi24Alpha.Pc.v669]
theorem CFSG.KD.Fi24Alpha.Pc.p668 : Nat.beq (runC AR SD 668 (ckL CFSG.KD.Fi24Alpha.Pc.l670) 2 668 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v670 : Nat := CFSG.KD.Fi24Alpha.KV4 143
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v671 : Nat := CFSG.KD.Fi24Alpha.KV4 144
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l672 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v668, CFSG.KD.Fi24Alpha.Pc.v669, CFSG.KD.Fi24Alpha.Pc.v670, CFSG.KD.Fi24Alpha.Pc.v671]
theorem CFSG.KD.Fi24Alpha.Pc.p670 : Nat.beq (runC AR SD 668 (ckL CFSG.KD.Fi24Alpha.Pc.l672) 2 670 CFSG.KD.Fi24Alpha.Pc.l670) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v672 : Nat := CFSG.KD.Fi24Alpha.KV4 145
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v673 : Nat := CFSG.KD.Fi24Alpha.KV4 146
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l674 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v668, CFSG.KD.Fi24Alpha.Pc.v669, CFSG.KD.Fi24Alpha.Pc.v670, CFSG.KD.Fi24Alpha.Pc.v671, CFSG.KD.Fi24Alpha.Pc.v672, CFSG.KD.Fi24Alpha.Pc.v673]
theorem CFSG.KD.Fi24Alpha.Pc.p672 : Nat.beq (runC AR SD 668 (ckL CFSG.KD.Fi24Alpha.Pc.l674) 2 672 CFSG.KD.Fi24Alpha.Pc.l672) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v674 : Nat := CFSG.KD.Fi24Alpha.KV4 147
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v675 : Nat := CFSG.KD.Fi24Alpha.KV4 148
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l676 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v668, CFSG.KD.Fi24Alpha.Pc.v669, CFSG.KD.Fi24Alpha.Pc.v670, CFSG.KD.Fi24Alpha.Pc.v671, CFSG.KD.Fi24Alpha.Pc.v672, CFSG.KD.Fi24Alpha.Pc.v673, CFSG.KD.Fi24Alpha.Pc.v674, CFSG.KD.Fi24Alpha.Pc.v675]
theorem CFSG.KD.Fi24Alpha.Pc.p674 : Nat.beq (runC AR SD 668 (ckL CFSG.KD.Fi24Alpha.Pc.l676) 2 674 CFSG.KD.Fi24Alpha.Pc.l674) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v676 : Nat := CFSG.KD.Fi24Alpha.KV4 149
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v677 : Nat := CFSG.KD.Fi24Alpha.KV4 150
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l678 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v668, CFSG.KD.Fi24Alpha.Pc.v669, CFSG.KD.Fi24Alpha.Pc.v670, CFSG.KD.Fi24Alpha.Pc.v671, CFSG.KD.Fi24Alpha.Pc.v672, CFSG.KD.Fi24Alpha.Pc.v673, CFSG.KD.Fi24Alpha.Pc.v674, CFSG.KD.Fi24Alpha.Pc.v675, CFSG.KD.Fi24Alpha.Pc.v676, CFSG.KD.Fi24Alpha.Pc.v677]
theorem CFSG.KD.Fi24Alpha.Pc.p676 : Nat.beq (runC AR SD 668 (ckL CFSG.KD.Fi24Alpha.Pc.l678) 2 676 CFSG.KD.Fi24Alpha.Pc.l676) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v678 : Nat := CFSG.KD.Fi24Alpha.KV4 151
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v679 : Nat := CFSG.KD.Fi24Alpha.KV4 152
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l680 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v668, CFSG.KD.Fi24Alpha.Pc.v669, CFSG.KD.Fi24Alpha.Pc.v670, CFSG.KD.Fi24Alpha.Pc.v671, CFSG.KD.Fi24Alpha.Pc.v672, CFSG.KD.Fi24Alpha.Pc.v673, CFSG.KD.Fi24Alpha.Pc.v674, CFSG.KD.Fi24Alpha.Pc.v675, CFSG.KD.Fi24Alpha.Pc.v676, CFSG.KD.Fi24Alpha.Pc.v677, CFSG.KD.Fi24Alpha.Pc.v678, CFSG.KD.Fi24Alpha.Pc.v679]
theorem CFSG.KD.Fi24Alpha.Pc.p678 : Nat.beq (runC AR SD 668 (ckL CFSG.KD.Fi24Alpha.Pc.l680) 2 678 CFSG.KD.Fi24Alpha.Pc.l678) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v680 : Nat := CFSG.KD.Fi24Alpha.KV4 153
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v681 : Nat := CFSG.KD.Fi24Alpha.KV4 154
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l682 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v668, CFSG.KD.Fi24Alpha.Pc.v669, CFSG.KD.Fi24Alpha.Pc.v670, CFSG.KD.Fi24Alpha.Pc.v671, CFSG.KD.Fi24Alpha.Pc.v672, CFSG.KD.Fi24Alpha.Pc.v673, CFSG.KD.Fi24Alpha.Pc.v674, CFSG.KD.Fi24Alpha.Pc.v675, CFSG.KD.Fi24Alpha.Pc.v676, CFSG.KD.Fi24Alpha.Pc.v677, CFSG.KD.Fi24Alpha.Pc.v678, CFSG.KD.Fi24Alpha.Pc.v679, CFSG.KD.Fi24Alpha.Pc.v680, CFSG.KD.Fi24Alpha.Pc.v681]
theorem CFSG.KD.Fi24Alpha.Pc.p680 : Nat.beq (runC AR SD 668 (ckL CFSG.KD.Fi24Alpha.Pc.l682) 2 680 CFSG.KD.Fi24Alpha.Pc.l680) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v682 : Nat := CFSG.KD.Fi24Alpha.KV4 155
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v683 : Nat := CFSG.KD.Fi24Alpha.KV4 156
theorem CFSG.KD.Fi24Alpha.Pc.f49 : Nat.beq (runC AR SD 668 (finC AR SD (nat_lit 49) 668 684) 2 682 CFSG.KD.Fi24Alpha.Pc.l682) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk49 : chk (nat_lit 49) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 49) (lo := 668) (hi := 684) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 670) CFSG.KD.Fi24Alpha.Pc.p668 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 672) CFSG.KD.Fi24Alpha.Pc.p670 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 674) CFSG.KD.Fi24Alpha.Pc.p672 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 676) CFSG.KD.Fi24Alpha.Pc.p674 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 678) CFSG.KD.Fi24Alpha.Pc.p676 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 680) CFSG.KD.Fi24Alpha.Pc.p678 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 682) CFSG.KD.Fi24Alpha.Pc.p680 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f49

end
