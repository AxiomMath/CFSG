module

public import Certificates.Kernel.Sporadic.Fi24Cp.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Cp KV5 "Certificates/Kernel/Sporadic/Fi24Cp/data/v5.bin" 152491 4 23636105 15588309511234973019

public section

open CFSG.KD.Fi24Cp CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v645 : Nat := CFSG.KD.Fi24Cp.KV5 0
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v646 : Nat := CFSG.KD.Fi24Cp.KV5 1
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l647 : List Nat := [CFSG.KD.Fi24Cp.Pc.v645, CFSG.KD.Fi24Cp.Pc.v646]
theorem CFSG.KD.Fi24Cp.Pc.p645 : Nat.beq (runC AR SD 645 (ckL CFSG.KD.Fi24Cp.Pc.l647) 2 645 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v647 : Nat := CFSG.KD.Fi24Cp.KV5 2
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v648 : Nat := CFSG.KD.Fi24Cp.KV5 3
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l649 : List Nat := [CFSG.KD.Fi24Cp.Pc.v645, CFSG.KD.Fi24Cp.Pc.v646, CFSG.KD.Fi24Cp.Pc.v647, CFSG.KD.Fi24Cp.Pc.v648]
theorem CFSG.KD.Fi24Cp.Pc.p647 : Nat.beq (runC AR SD 645 (ckL CFSG.KD.Fi24Cp.Pc.l649) 2 647 CFSG.KD.Fi24Cp.Pc.l647) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v649 : Nat := CFSG.KD.Fi24Cp.KV5 4
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v650 : Nat := CFSG.KD.Fi24Cp.KV5 5
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l651 : List Nat := [CFSG.KD.Fi24Cp.Pc.v645, CFSG.KD.Fi24Cp.Pc.v646, CFSG.KD.Fi24Cp.Pc.v647, CFSG.KD.Fi24Cp.Pc.v648, CFSG.KD.Fi24Cp.Pc.v649, CFSG.KD.Fi24Cp.Pc.v650]
theorem CFSG.KD.Fi24Cp.Pc.p649 : Nat.beq (runC AR SD 645 (ckL CFSG.KD.Fi24Cp.Pc.l651) 2 649 CFSG.KD.Fi24Cp.Pc.l649) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a651_2 : Nat := CFSG.KD.Fi24Cp.KV5 6
theorem CFSG.KD.Fi24Cp.Pc.q651_2 : Nat.beq (powTop AR.mul (getV AR SD 645 CFSG.KD.Fi24Cp.Pc.l651 (SD.na.getD 651 0)) (SD.nk.getD 651 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a651_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a651_1 : Nat := CFSG.KD.Fi24Cp.KV5 7
theorem CFSG.KD.Fi24Cp.Pc.q651_1 : Nat.beq (powTop AR.mul (getV AR SD 645 CFSG.KD.Fi24Cp.Pc.l651 (SD.na.getD 651 0)) (SD.nk.getD 651 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a651_1) 1 CFSG.KD.Fi24Cp.Pc.a651_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v651 : Nat := CFSG.KD.Fi24Cp.KV5 8
theorem CFSG.KD.Fi24Cp.Pc.r651 : Nat.beq (powR AR.mul AR.one (getV AR SD 645 CFSG.KD.Fi24Cp.Pc.l651 (SD.na.getD 651 0)) (SD.nk.getD 651 1) 1 CFSG.KD.Fi24Cp.Pc.a651_1 true) CFSG.KD.Fi24Cp.Pc.v651 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v652 : Nat := CFSG.KD.Fi24Cp.KV5 9
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v653 : Nat := CFSG.KD.Fi24Cp.KV5 10
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l652 : List Nat := [CFSG.KD.Fi24Cp.Pc.v645, CFSG.KD.Fi24Cp.Pc.v646, CFSG.KD.Fi24Cp.Pc.v647, CFSG.KD.Fi24Cp.Pc.v648, CFSG.KD.Fi24Cp.Pc.v649, CFSG.KD.Fi24Cp.Pc.v650, CFSG.KD.Fi24Cp.Pc.v651]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l654 : List Nat := [CFSG.KD.Fi24Cp.Pc.v645, CFSG.KD.Fi24Cp.Pc.v646, CFSG.KD.Fi24Cp.Pc.v647, CFSG.KD.Fi24Cp.Pc.v648, CFSG.KD.Fi24Cp.Pc.v649, CFSG.KD.Fi24Cp.Pc.v650, CFSG.KD.Fi24Cp.Pc.v651, CFSG.KD.Fi24Cp.Pc.v652, CFSG.KD.Fi24Cp.Pc.v653]
theorem CFSG.KD.Fi24Cp.Pc.p652 : Nat.beq (runC AR SD 645 (ckL CFSG.KD.Fi24Cp.Pc.l654) 2 652 CFSG.KD.Fi24Cp.Pc.l652) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v654 : Nat := CFSG.KD.Fi24Cp.KV5 11
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v655 : Nat := CFSG.KD.Fi24Cp.KV5 12
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l656 : List Nat := [CFSG.KD.Fi24Cp.Pc.v645, CFSG.KD.Fi24Cp.Pc.v646, CFSG.KD.Fi24Cp.Pc.v647, CFSG.KD.Fi24Cp.Pc.v648, CFSG.KD.Fi24Cp.Pc.v649, CFSG.KD.Fi24Cp.Pc.v650, CFSG.KD.Fi24Cp.Pc.v651, CFSG.KD.Fi24Cp.Pc.v652, CFSG.KD.Fi24Cp.Pc.v653, CFSG.KD.Fi24Cp.Pc.v654, CFSG.KD.Fi24Cp.Pc.v655]
theorem CFSG.KD.Fi24Cp.Pc.p654 : Nat.beq (runC AR SD 645 (ckL CFSG.KD.Fi24Cp.Pc.l656) 2 654 CFSG.KD.Fi24Cp.Pc.l654) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v656 : Nat := CFSG.KD.Fi24Cp.KV5 13
theorem CFSG.KD.Fi24Cp.Pc.f50 : Nat.beq (runC AR SD 645 (finC AR SD (nat_lit 50) 645 657) 1 656 CFSG.KD.Fi24Cp.Pc.l656) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk50 : chk (nat_lit 50) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 50) (lo := 645) (hi := 657) (m := 12) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 12) (m2 := 10) (j2 := 647) CFSG.KD.Fi24Cp.Pc.p645 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 649) CFSG.KD.Fi24Cp.Pc.p647 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 651) CFSG.KD.Fi24Cp.Pc.p649 rfl rfl).trans ((runC_node (m := 6) (m2 := 5) (j2 := 652) (Lr := CFSG.KD.Fi24Cp.Pc.l652) ((nodeV_pow (R := AR) (D := SD) (lo := 645) (L := CFSG.KD.Fi24Cp.Pc.l651) (j := 651) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 645 CFSG.KD.Fi24Cp.Pc.l651 (SD.na.getD 651 0)) (SD.nk.getD 651 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q651_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q651_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r651))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 654) CFSG.KD.Fi24Cp.Pc.p652 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 656) CFSG.KD.Fi24Cp.Pc.p654 rfl rfl)))))))).trans CFSG.KD.Fi24Cp.Pc.f50

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v657 : Nat := CFSG.KD.Fi24Cp.KV5 14
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v658 : Nat := CFSG.KD.Fi24Cp.KV5 15
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l659 : List Nat := [CFSG.KD.Fi24Cp.Pc.v657, CFSG.KD.Fi24Cp.Pc.v658]
theorem CFSG.KD.Fi24Cp.Pc.p657 : Nat.beq (runC AR SD 657 (ckL CFSG.KD.Fi24Cp.Pc.l659) 2 657 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v659 : Nat := CFSG.KD.Fi24Cp.KV5 16
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v660 : Nat := CFSG.KD.Fi24Cp.KV5 17
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l661 : List Nat := [CFSG.KD.Fi24Cp.Pc.v657, CFSG.KD.Fi24Cp.Pc.v658, CFSG.KD.Fi24Cp.Pc.v659, CFSG.KD.Fi24Cp.Pc.v660]
theorem CFSG.KD.Fi24Cp.Pc.p659 : Nat.beq (runC AR SD 657 (ckL CFSG.KD.Fi24Cp.Pc.l661) 2 659 CFSG.KD.Fi24Cp.Pc.l659) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v661 : Nat := CFSG.KD.Fi24Cp.KV5 18
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v662 : Nat := CFSG.KD.Fi24Cp.KV5 19
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l663 : List Nat := [CFSG.KD.Fi24Cp.Pc.v657, CFSG.KD.Fi24Cp.Pc.v658, CFSG.KD.Fi24Cp.Pc.v659, CFSG.KD.Fi24Cp.Pc.v660, CFSG.KD.Fi24Cp.Pc.v661, CFSG.KD.Fi24Cp.Pc.v662]
theorem CFSG.KD.Fi24Cp.Pc.p661 : Nat.beq (runC AR SD 657 (ckL CFSG.KD.Fi24Cp.Pc.l663) 2 661 CFSG.KD.Fi24Cp.Pc.l661) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v663 : Nat := CFSG.KD.Fi24Cp.KV5 20
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v664 : Nat := CFSG.KD.Fi24Cp.KV5 21
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l665 : List Nat := [CFSG.KD.Fi24Cp.Pc.v657, CFSG.KD.Fi24Cp.Pc.v658, CFSG.KD.Fi24Cp.Pc.v659, CFSG.KD.Fi24Cp.Pc.v660, CFSG.KD.Fi24Cp.Pc.v661, CFSG.KD.Fi24Cp.Pc.v662, CFSG.KD.Fi24Cp.Pc.v663, CFSG.KD.Fi24Cp.Pc.v664]
theorem CFSG.KD.Fi24Cp.Pc.p663 : Nat.beq (runC AR SD 657 (ckL CFSG.KD.Fi24Cp.Pc.l665) 2 663 CFSG.KD.Fi24Cp.Pc.l663) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v665 : Nat := CFSG.KD.Fi24Cp.KV5 22
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v666 : Nat := CFSG.KD.Fi24Cp.KV5 23
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l667 : List Nat := [CFSG.KD.Fi24Cp.Pc.v657, CFSG.KD.Fi24Cp.Pc.v658, CFSG.KD.Fi24Cp.Pc.v659, CFSG.KD.Fi24Cp.Pc.v660, CFSG.KD.Fi24Cp.Pc.v661, CFSG.KD.Fi24Cp.Pc.v662, CFSG.KD.Fi24Cp.Pc.v663, CFSG.KD.Fi24Cp.Pc.v664, CFSG.KD.Fi24Cp.Pc.v665, CFSG.KD.Fi24Cp.Pc.v666]
theorem CFSG.KD.Fi24Cp.Pc.p665 : Nat.beq (runC AR SD 657 (ckL CFSG.KD.Fi24Cp.Pc.l667) 2 665 CFSG.KD.Fi24Cp.Pc.l665) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v667 : Nat := CFSG.KD.Fi24Cp.KV5 24
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v668 : Nat := CFSG.KD.Fi24Cp.KV5 25
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l669 : List Nat := [CFSG.KD.Fi24Cp.Pc.v657, CFSG.KD.Fi24Cp.Pc.v658, CFSG.KD.Fi24Cp.Pc.v659, CFSG.KD.Fi24Cp.Pc.v660, CFSG.KD.Fi24Cp.Pc.v661, CFSG.KD.Fi24Cp.Pc.v662, CFSG.KD.Fi24Cp.Pc.v663, CFSG.KD.Fi24Cp.Pc.v664, CFSG.KD.Fi24Cp.Pc.v665, CFSG.KD.Fi24Cp.Pc.v666, CFSG.KD.Fi24Cp.Pc.v667, CFSG.KD.Fi24Cp.Pc.v668]
theorem CFSG.KD.Fi24Cp.Pc.p667 : Nat.beq (runC AR SD 657 (ckL CFSG.KD.Fi24Cp.Pc.l669) 2 667 CFSG.KD.Fi24Cp.Pc.l667) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v669 : Nat := CFSG.KD.Fi24Cp.KV5 26
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v670 : Nat := CFSG.KD.Fi24Cp.KV5 27
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l671 : List Nat := [CFSG.KD.Fi24Cp.Pc.v657, CFSG.KD.Fi24Cp.Pc.v658, CFSG.KD.Fi24Cp.Pc.v659, CFSG.KD.Fi24Cp.Pc.v660, CFSG.KD.Fi24Cp.Pc.v661, CFSG.KD.Fi24Cp.Pc.v662, CFSG.KD.Fi24Cp.Pc.v663, CFSG.KD.Fi24Cp.Pc.v664, CFSG.KD.Fi24Cp.Pc.v665, CFSG.KD.Fi24Cp.Pc.v666, CFSG.KD.Fi24Cp.Pc.v667, CFSG.KD.Fi24Cp.Pc.v668, CFSG.KD.Fi24Cp.Pc.v669, CFSG.KD.Fi24Cp.Pc.v670]
theorem CFSG.KD.Fi24Cp.Pc.p669 : Nat.beq (runC AR SD 657 (ckL CFSG.KD.Fi24Cp.Pc.l671) 2 669 CFSG.KD.Fi24Cp.Pc.l669) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v671 : Nat := CFSG.KD.Fi24Cp.KV5 28
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v672 : Nat := CFSG.KD.Fi24Cp.KV5 29
theorem CFSG.KD.Fi24Cp.Pc.f51 : Nat.beq (runC AR SD 657 (finC AR SD (nat_lit 51) 657 673) 2 671 CFSG.KD.Fi24Cp.Pc.l671) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk51 : chk (nat_lit 51) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 51) (lo := 657) (hi := 673) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 659) CFSG.KD.Fi24Cp.Pc.p657 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 661) CFSG.KD.Fi24Cp.Pc.p659 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 663) CFSG.KD.Fi24Cp.Pc.p661 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 665) CFSG.KD.Fi24Cp.Pc.p663 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 667) CFSG.KD.Fi24Cp.Pc.p665 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 669) CFSG.KD.Fi24Cp.Pc.p667 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 671) CFSG.KD.Fi24Cp.Pc.p669 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f51

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v673 : Nat := CFSG.KD.Fi24Cp.KV5 30
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v674 : Nat := CFSG.KD.Fi24Cp.KV5 31
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l675 : List Nat := [CFSG.KD.Fi24Cp.Pc.v673, CFSG.KD.Fi24Cp.Pc.v674]
theorem CFSG.KD.Fi24Cp.Pc.p673 : Nat.beq (runC AR SD 673 (ckL CFSG.KD.Fi24Cp.Pc.l675) 2 673 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v675 : Nat := CFSG.KD.Fi24Cp.KV5 32
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v676 : Nat := CFSG.KD.Fi24Cp.KV5 33
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l677 : List Nat := [CFSG.KD.Fi24Cp.Pc.v673, CFSG.KD.Fi24Cp.Pc.v674, CFSG.KD.Fi24Cp.Pc.v675, CFSG.KD.Fi24Cp.Pc.v676]
theorem CFSG.KD.Fi24Cp.Pc.p675 : Nat.beq (runC AR SD 673 (ckL CFSG.KD.Fi24Cp.Pc.l677) 2 675 CFSG.KD.Fi24Cp.Pc.l675) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v677 : Nat := CFSG.KD.Fi24Cp.KV5 34
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v678 : Nat := CFSG.KD.Fi24Cp.KV5 35
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l679 : List Nat := [CFSG.KD.Fi24Cp.Pc.v673, CFSG.KD.Fi24Cp.Pc.v674, CFSG.KD.Fi24Cp.Pc.v675, CFSG.KD.Fi24Cp.Pc.v676, CFSG.KD.Fi24Cp.Pc.v677, CFSG.KD.Fi24Cp.Pc.v678]
theorem CFSG.KD.Fi24Cp.Pc.p677 : Nat.beq (runC AR SD 673 (ckL CFSG.KD.Fi24Cp.Pc.l679) 2 677 CFSG.KD.Fi24Cp.Pc.l677) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v679 : Nat := CFSG.KD.Fi24Cp.KV5 36
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v680 : Nat := CFSG.KD.Fi24Cp.KV5 37
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l681 : List Nat := [CFSG.KD.Fi24Cp.Pc.v673, CFSG.KD.Fi24Cp.Pc.v674, CFSG.KD.Fi24Cp.Pc.v675, CFSG.KD.Fi24Cp.Pc.v676, CFSG.KD.Fi24Cp.Pc.v677, CFSG.KD.Fi24Cp.Pc.v678, CFSG.KD.Fi24Cp.Pc.v679, CFSG.KD.Fi24Cp.Pc.v680]
theorem CFSG.KD.Fi24Cp.Pc.p679 : Nat.beq (runC AR SD 673 (ckL CFSG.KD.Fi24Cp.Pc.l681) 2 679 CFSG.KD.Fi24Cp.Pc.l679) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v681 : Nat := CFSG.KD.Fi24Cp.KV5 38
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v682 : Nat := CFSG.KD.Fi24Cp.KV5 39
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l683 : List Nat := [CFSG.KD.Fi24Cp.Pc.v673, CFSG.KD.Fi24Cp.Pc.v674, CFSG.KD.Fi24Cp.Pc.v675, CFSG.KD.Fi24Cp.Pc.v676, CFSG.KD.Fi24Cp.Pc.v677, CFSG.KD.Fi24Cp.Pc.v678, CFSG.KD.Fi24Cp.Pc.v679, CFSG.KD.Fi24Cp.Pc.v680, CFSG.KD.Fi24Cp.Pc.v681, CFSG.KD.Fi24Cp.Pc.v682]
theorem CFSG.KD.Fi24Cp.Pc.p681 : Nat.beq (runC AR SD 673 (ckL CFSG.KD.Fi24Cp.Pc.l683) 2 681 CFSG.KD.Fi24Cp.Pc.l681) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v683 : Nat := CFSG.KD.Fi24Cp.KV5 40
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v684 : Nat := CFSG.KD.Fi24Cp.KV5 41
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l685 : List Nat := [CFSG.KD.Fi24Cp.Pc.v673, CFSG.KD.Fi24Cp.Pc.v674, CFSG.KD.Fi24Cp.Pc.v675, CFSG.KD.Fi24Cp.Pc.v676, CFSG.KD.Fi24Cp.Pc.v677, CFSG.KD.Fi24Cp.Pc.v678, CFSG.KD.Fi24Cp.Pc.v679, CFSG.KD.Fi24Cp.Pc.v680, CFSG.KD.Fi24Cp.Pc.v681, CFSG.KD.Fi24Cp.Pc.v682, CFSG.KD.Fi24Cp.Pc.v683, CFSG.KD.Fi24Cp.Pc.v684]
theorem CFSG.KD.Fi24Cp.Pc.p683 : Nat.beq (runC AR SD 673 (ckL CFSG.KD.Fi24Cp.Pc.l685) 2 683 CFSG.KD.Fi24Cp.Pc.l683) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v685 : Nat := CFSG.KD.Fi24Cp.KV5 42
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v686 : Nat := CFSG.KD.Fi24Cp.KV5 43
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l687 : List Nat := [CFSG.KD.Fi24Cp.Pc.v673, CFSG.KD.Fi24Cp.Pc.v674, CFSG.KD.Fi24Cp.Pc.v675, CFSG.KD.Fi24Cp.Pc.v676, CFSG.KD.Fi24Cp.Pc.v677, CFSG.KD.Fi24Cp.Pc.v678, CFSG.KD.Fi24Cp.Pc.v679, CFSG.KD.Fi24Cp.Pc.v680, CFSG.KD.Fi24Cp.Pc.v681, CFSG.KD.Fi24Cp.Pc.v682, CFSG.KD.Fi24Cp.Pc.v683, CFSG.KD.Fi24Cp.Pc.v684, CFSG.KD.Fi24Cp.Pc.v685, CFSG.KD.Fi24Cp.Pc.v686]
theorem CFSG.KD.Fi24Cp.Pc.p685 : Nat.beq (runC AR SD 673 (ckL CFSG.KD.Fi24Cp.Pc.l687) 2 685 CFSG.KD.Fi24Cp.Pc.l685) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v687 : Nat := CFSG.KD.Fi24Cp.KV5 44
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v688 : Nat := CFSG.KD.Fi24Cp.KV5 45
theorem CFSG.KD.Fi24Cp.Pc.f52 : Nat.beq (runC AR SD 673 (finC AR SD (nat_lit 52) 673 689) 2 687 CFSG.KD.Fi24Cp.Pc.l687) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk52 : chk (nat_lit 52) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 52) (lo := 673) (hi := 689) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 675) CFSG.KD.Fi24Cp.Pc.p673 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 677) CFSG.KD.Fi24Cp.Pc.p675 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 679) CFSG.KD.Fi24Cp.Pc.p677 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 681) CFSG.KD.Fi24Cp.Pc.p679 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 683) CFSG.KD.Fi24Cp.Pc.p681 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 685) CFSG.KD.Fi24Cp.Pc.p683 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 687) CFSG.KD.Fi24Cp.Pc.p685 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f52

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v689 : Nat := CFSG.KD.Fi24Cp.KV5 46
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l690 : List Nat := [CFSG.KD.Fi24Cp.Pc.v689]
theorem CFSG.KD.Fi24Cp.Pc.p689 : Nat.beq (runC AR SD 689 (ckL CFSG.KD.Fi24Cp.Pc.l690) 1 689 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a690_2 : Nat := CFSG.KD.Fi24Cp.KV5 47
theorem CFSG.KD.Fi24Cp.Pc.q690_2 : Nat.beq (powTop AR.mul (getV AR SD 689 CFSG.KD.Fi24Cp.Pc.l690 (SD.na.getD 690 0)) (SD.nk.getD 690 1) 2 (ckP CFSG.KD.Fi24Cp.Pc.a690_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a690_1 : Nat := CFSG.KD.Fi24Cp.KV5 48
theorem CFSG.KD.Fi24Cp.Pc.q690_1 : Nat.beq (powTop AR.mul (getV AR SD 689 CFSG.KD.Fi24Cp.Pc.l690 (SD.na.getD 690 0)) (SD.nk.getD 690 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a690_1) 1 CFSG.KD.Fi24Cp.Pc.a690_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v690 : Nat := CFSG.KD.Fi24Cp.KV5 49
theorem CFSG.KD.Fi24Cp.Pc.r690 : Nat.beq (powR AR.mul AR.one (getV AR SD 689 CFSG.KD.Fi24Cp.Pc.l690 (SD.na.getD 690 0)) (SD.nk.getD 690 1) 1 CFSG.KD.Fi24Cp.Pc.a690_1 true) CFSG.KD.Fi24Cp.Pc.v690 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v691 : Nat := CFSG.KD.Fi24Cp.KV5 50
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v692 : Nat := CFSG.KD.Fi24Cp.KV5 51
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l691 : List Nat := [CFSG.KD.Fi24Cp.Pc.v689, CFSG.KD.Fi24Cp.Pc.v690]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l693 : List Nat := [CFSG.KD.Fi24Cp.Pc.v689, CFSG.KD.Fi24Cp.Pc.v690, CFSG.KD.Fi24Cp.Pc.v691, CFSG.KD.Fi24Cp.Pc.v692]
theorem CFSG.KD.Fi24Cp.Pc.p691 : Nat.beq (runC AR SD 689 (ckL CFSG.KD.Fi24Cp.Pc.l693) 2 691 CFSG.KD.Fi24Cp.Pc.l691) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v693 : Nat := CFSG.KD.Fi24Cp.KV5 52
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v694 : Nat := CFSG.KD.Fi24Cp.KV5 53
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l695 : List Nat := [CFSG.KD.Fi24Cp.Pc.v689, CFSG.KD.Fi24Cp.Pc.v690, CFSG.KD.Fi24Cp.Pc.v691, CFSG.KD.Fi24Cp.Pc.v692, CFSG.KD.Fi24Cp.Pc.v693, CFSG.KD.Fi24Cp.Pc.v694]
theorem CFSG.KD.Fi24Cp.Pc.p693 : Nat.beq (runC AR SD 689 (ckL CFSG.KD.Fi24Cp.Pc.l695) 2 693 CFSG.KD.Fi24Cp.Pc.l693) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v695 : Nat := CFSG.KD.Fi24Cp.KV5 54
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v696 : Nat := CFSG.KD.Fi24Cp.KV5 55
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l697 : List Nat := [CFSG.KD.Fi24Cp.Pc.v689, CFSG.KD.Fi24Cp.Pc.v690, CFSG.KD.Fi24Cp.Pc.v691, CFSG.KD.Fi24Cp.Pc.v692, CFSG.KD.Fi24Cp.Pc.v693, CFSG.KD.Fi24Cp.Pc.v694, CFSG.KD.Fi24Cp.Pc.v695, CFSG.KD.Fi24Cp.Pc.v696]
theorem CFSG.KD.Fi24Cp.Pc.p695 : Nat.beq (runC AR SD 689 (ckL CFSG.KD.Fi24Cp.Pc.l697) 2 695 CFSG.KD.Fi24Cp.Pc.l695) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v697 : Nat := CFSG.KD.Fi24Cp.KV5 56
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v698 : Nat := CFSG.KD.Fi24Cp.KV5 57
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l699 : List Nat := [CFSG.KD.Fi24Cp.Pc.v689, CFSG.KD.Fi24Cp.Pc.v690, CFSG.KD.Fi24Cp.Pc.v691, CFSG.KD.Fi24Cp.Pc.v692, CFSG.KD.Fi24Cp.Pc.v693, CFSG.KD.Fi24Cp.Pc.v694, CFSG.KD.Fi24Cp.Pc.v695, CFSG.KD.Fi24Cp.Pc.v696, CFSG.KD.Fi24Cp.Pc.v697, CFSG.KD.Fi24Cp.Pc.v698]
theorem CFSG.KD.Fi24Cp.Pc.p697 : Nat.beq (runC AR SD 689 (ckL CFSG.KD.Fi24Cp.Pc.l699) 2 697 CFSG.KD.Fi24Cp.Pc.l697) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v699 : Nat := CFSG.KD.Fi24Cp.KV5 58
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v700 : Nat := CFSG.KD.Fi24Cp.KV5 59
theorem CFSG.KD.Fi24Cp.Pc.f53 : Nat.beq (runC AR SD 689 (finC AR SD (nat_lit 53) 689 701) 2 699 CFSG.KD.Fi24Cp.Pc.l699) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk53 : chk (nat_lit 53) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 53) (lo := 689) (hi := 701) (m := 12) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 12) (m2 := 11) (j2 := 690) CFSG.KD.Fi24Cp.Pc.p689 rfl rfl).trans ((runC_node (m := 11) (m2 := 10) (j2 := 691) (Lr := CFSG.KD.Fi24Cp.Pc.l691) ((nodeV_pow (R := AR) (D := SD) (lo := 689) (L := CFSG.KD.Fi24Cp.Pc.l690) (j := 690) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 689 CFSG.KD.Fi24Cp.Pc.l690 (SD.na.getD 690 0)) (SD.nk.getD 690 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q690_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Cp.Pc.q690_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r690))))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 693) CFSG.KD.Fi24Cp.Pc.p691 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 695) CFSG.KD.Fi24Cp.Pc.p693 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 697) CFSG.KD.Fi24Cp.Pc.p695 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 699) CFSG.KD.Fi24Cp.Pc.p697 rfl rfl)))))))).trans CFSG.KD.Fi24Cp.Pc.f53

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v701 : Nat := CFSG.KD.Fi24Cp.KV5 60
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v702 : Nat := CFSG.KD.Fi24Cp.KV5 61
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l703 : List Nat := [CFSG.KD.Fi24Cp.Pc.v701, CFSG.KD.Fi24Cp.Pc.v702]
theorem CFSG.KD.Fi24Cp.Pc.p701 : Nat.beq (runC AR SD 701 (ckL CFSG.KD.Fi24Cp.Pc.l703) 2 701 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v703 : Nat := CFSG.KD.Fi24Cp.KV5 62
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v704 : Nat := CFSG.KD.Fi24Cp.KV5 63
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l705 : List Nat := [CFSG.KD.Fi24Cp.Pc.v701, CFSG.KD.Fi24Cp.Pc.v702, CFSG.KD.Fi24Cp.Pc.v703, CFSG.KD.Fi24Cp.Pc.v704]
theorem CFSG.KD.Fi24Cp.Pc.p703 : Nat.beq (runC AR SD 701 (ckL CFSG.KD.Fi24Cp.Pc.l705) 2 703 CFSG.KD.Fi24Cp.Pc.l703) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v705 : Nat := CFSG.KD.Fi24Cp.KV5 64
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v706 : Nat := CFSG.KD.Fi24Cp.KV5 65
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l707 : List Nat := [CFSG.KD.Fi24Cp.Pc.v701, CFSG.KD.Fi24Cp.Pc.v702, CFSG.KD.Fi24Cp.Pc.v703, CFSG.KD.Fi24Cp.Pc.v704, CFSG.KD.Fi24Cp.Pc.v705, CFSG.KD.Fi24Cp.Pc.v706]
theorem CFSG.KD.Fi24Cp.Pc.p705 : Nat.beq (runC AR SD 701 (ckL CFSG.KD.Fi24Cp.Pc.l707) 2 705 CFSG.KD.Fi24Cp.Pc.l705) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v707 : Nat := CFSG.KD.Fi24Cp.KV5 66
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v708 : Nat := CFSG.KD.Fi24Cp.KV5 67
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l709 : List Nat := [CFSG.KD.Fi24Cp.Pc.v701, CFSG.KD.Fi24Cp.Pc.v702, CFSG.KD.Fi24Cp.Pc.v703, CFSG.KD.Fi24Cp.Pc.v704, CFSG.KD.Fi24Cp.Pc.v705, CFSG.KD.Fi24Cp.Pc.v706, CFSG.KD.Fi24Cp.Pc.v707, CFSG.KD.Fi24Cp.Pc.v708]
theorem CFSG.KD.Fi24Cp.Pc.p707 : Nat.beq (runC AR SD 701 (ckL CFSG.KD.Fi24Cp.Pc.l709) 2 707 CFSG.KD.Fi24Cp.Pc.l707) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v709 : Nat := CFSG.KD.Fi24Cp.KV5 68
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v710 : Nat := CFSG.KD.Fi24Cp.KV5 69
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l711 : List Nat := [CFSG.KD.Fi24Cp.Pc.v701, CFSG.KD.Fi24Cp.Pc.v702, CFSG.KD.Fi24Cp.Pc.v703, CFSG.KD.Fi24Cp.Pc.v704, CFSG.KD.Fi24Cp.Pc.v705, CFSG.KD.Fi24Cp.Pc.v706, CFSG.KD.Fi24Cp.Pc.v707, CFSG.KD.Fi24Cp.Pc.v708, CFSG.KD.Fi24Cp.Pc.v709, CFSG.KD.Fi24Cp.Pc.v710]
theorem CFSG.KD.Fi24Cp.Pc.p709 : Nat.beq (runC AR SD 701 (ckL CFSG.KD.Fi24Cp.Pc.l711) 2 709 CFSG.KD.Fi24Cp.Pc.l709) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v711 : Nat := CFSG.KD.Fi24Cp.KV5 70
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v712 : Nat := CFSG.KD.Fi24Cp.KV5 71
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l713 : List Nat := [CFSG.KD.Fi24Cp.Pc.v701, CFSG.KD.Fi24Cp.Pc.v702, CFSG.KD.Fi24Cp.Pc.v703, CFSG.KD.Fi24Cp.Pc.v704, CFSG.KD.Fi24Cp.Pc.v705, CFSG.KD.Fi24Cp.Pc.v706, CFSG.KD.Fi24Cp.Pc.v707, CFSG.KD.Fi24Cp.Pc.v708, CFSG.KD.Fi24Cp.Pc.v709, CFSG.KD.Fi24Cp.Pc.v710, CFSG.KD.Fi24Cp.Pc.v711, CFSG.KD.Fi24Cp.Pc.v712]
theorem CFSG.KD.Fi24Cp.Pc.p711 : Nat.beq (runC AR SD 701 (ckL CFSG.KD.Fi24Cp.Pc.l713) 2 711 CFSG.KD.Fi24Cp.Pc.l711) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v713 : Nat := CFSG.KD.Fi24Cp.KV5 72
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v714 : Nat := CFSG.KD.Fi24Cp.KV5 73
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l715 : List Nat := [CFSG.KD.Fi24Cp.Pc.v701, CFSG.KD.Fi24Cp.Pc.v702, CFSG.KD.Fi24Cp.Pc.v703, CFSG.KD.Fi24Cp.Pc.v704, CFSG.KD.Fi24Cp.Pc.v705, CFSG.KD.Fi24Cp.Pc.v706, CFSG.KD.Fi24Cp.Pc.v707, CFSG.KD.Fi24Cp.Pc.v708, CFSG.KD.Fi24Cp.Pc.v709, CFSG.KD.Fi24Cp.Pc.v710, CFSG.KD.Fi24Cp.Pc.v711, CFSG.KD.Fi24Cp.Pc.v712, CFSG.KD.Fi24Cp.Pc.v713, CFSG.KD.Fi24Cp.Pc.v714]
theorem CFSG.KD.Fi24Cp.Pc.p713 : Nat.beq (runC AR SD 701 (ckL CFSG.KD.Fi24Cp.Pc.l715) 2 713 CFSG.KD.Fi24Cp.Pc.l713) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v715 : Nat := CFSG.KD.Fi24Cp.KV5 74
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v716 : Nat := CFSG.KD.Fi24Cp.KV5 75
theorem CFSG.KD.Fi24Cp.Pc.f54 : Nat.beq (runC AR SD 701 (finC AR SD (nat_lit 54) 701 717) 2 715 CFSG.KD.Fi24Cp.Pc.l715) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk54 : chk (nat_lit 54) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 54) (lo := 701) (hi := 717) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 703) CFSG.KD.Fi24Cp.Pc.p701 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 705) CFSG.KD.Fi24Cp.Pc.p703 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 707) CFSG.KD.Fi24Cp.Pc.p705 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 709) CFSG.KD.Fi24Cp.Pc.p707 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 711) CFSG.KD.Fi24Cp.Pc.p709 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 713) CFSG.KD.Fi24Cp.Pc.p711 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 715) CFSG.KD.Fi24Cp.Pc.p713 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f54

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v717 : Nat := CFSG.KD.Fi24Cp.KV5 76
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v718 : Nat := CFSG.KD.Fi24Cp.KV5 77
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l719 : List Nat := [CFSG.KD.Fi24Cp.Pc.v717, CFSG.KD.Fi24Cp.Pc.v718]
theorem CFSG.KD.Fi24Cp.Pc.p717 : Nat.beq (runC AR SD 717 (ckL CFSG.KD.Fi24Cp.Pc.l719) 2 717 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v719 : Nat := CFSG.KD.Fi24Cp.KV5 78
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v720 : Nat := CFSG.KD.Fi24Cp.KV5 79
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l721 : List Nat := [CFSG.KD.Fi24Cp.Pc.v717, CFSG.KD.Fi24Cp.Pc.v718, CFSG.KD.Fi24Cp.Pc.v719, CFSG.KD.Fi24Cp.Pc.v720]
theorem CFSG.KD.Fi24Cp.Pc.p719 : Nat.beq (runC AR SD 717 (ckL CFSG.KD.Fi24Cp.Pc.l721) 2 719 CFSG.KD.Fi24Cp.Pc.l719) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v721 : Nat := CFSG.KD.Fi24Cp.KV5 80
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v722 : Nat := CFSG.KD.Fi24Cp.KV5 81
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l723 : List Nat := [CFSG.KD.Fi24Cp.Pc.v717, CFSG.KD.Fi24Cp.Pc.v718, CFSG.KD.Fi24Cp.Pc.v719, CFSG.KD.Fi24Cp.Pc.v720, CFSG.KD.Fi24Cp.Pc.v721, CFSG.KD.Fi24Cp.Pc.v722]
theorem CFSG.KD.Fi24Cp.Pc.p721 : Nat.beq (runC AR SD 717 (ckL CFSG.KD.Fi24Cp.Pc.l723) 2 721 CFSG.KD.Fi24Cp.Pc.l721) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v723 : Nat := CFSG.KD.Fi24Cp.KV5 82
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v724 : Nat := CFSG.KD.Fi24Cp.KV5 83
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l725 : List Nat := [CFSG.KD.Fi24Cp.Pc.v717, CFSG.KD.Fi24Cp.Pc.v718, CFSG.KD.Fi24Cp.Pc.v719, CFSG.KD.Fi24Cp.Pc.v720, CFSG.KD.Fi24Cp.Pc.v721, CFSG.KD.Fi24Cp.Pc.v722, CFSG.KD.Fi24Cp.Pc.v723, CFSG.KD.Fi24Cp.Pc.v724]
theorem CFSG.KD.Fi24Cp.Pc.p723 : Nat.beq (runC AR SD 717 (ckL CFSG.KD.Fi24Cp.Pc.l725) 2 723 CFSG.KD.Fi24Cp.Pc.l723) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v725 : Nat := CFSG.KD.Fi24Cp.KV5 84
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v726 : Nat := CFSG.KD.Fi24Cp.KV5 85
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l727 : List Nat := [CFSG.KD.Fi24Cp.Pc.v717, CFSG.KD.Fi24Cp.Pc.v718, CFSG.KD.Fi24Cp.Pc.v719, CFSG.KD.Fi24Cp.Pc.v720, CFSG.KD.Fi24Cp.Pc.v721, CFSG.KD.Fi24Cp.Pc.v722, CFSG.KD.Fi24Cp.Pc.v723, CFSG.KD.Fi24Cp.Pc.v724, CFSG.KD.Fi24Cp.Pc.v725, CFSG.KD.Fi24Cp.Pc.v726]
theorem CFSG.KD.Fi24Cp.Pc.p725 : Nat.beq (runC AR SD 717 (ckL CFSG.KD.Fi24Cp.Pc.l727) 2 725 CFSG.KD.Fi24Cp.Pc.l725) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v727 : Nat := CFSG.KD.Fi24Cp.KV5 86
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v728 : Nat := CFSG.KD.Fi24Cp.KV5 87
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l729 : List Nat := [CFSG.KD.Fi24Cp.Pc.v717, CFSG.KD.Fi24Cp.Pc.v718, CFSG.KD.Fi24Cp.Pc.v719, CFSG.KD.Fi24Cp.Pc.v720, CFSG.KD.Fi24Cp.Pc.v721, CFSG.KD.Fi24Cp.Pc.v722, CFSG.KD.Fi24Cp.Pc.v723, CFSG.KD.Fi24Cp.Pc.v724, CFSG.KD.Fi24Cp.Pc.v725, CFSG.KD.Fi24Cp.Pc.v726, CFSG.KD.Fi24Cp.Pc.v727, CFSG.KD.Fi24Cp.Pc.v728]
theorem CFSG.KD.Fi24Cp.Pc.p727 : Nat.beq (runC AR SD 717 (ckL CFSG.KD.Fi24Cp.Pc.l729) 2 727 CFSG.KD.Fi24Cp.Pc.l727) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v729 : Nat := CFSG.KD.Fi24Cp.KV5 88
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v730 : Nat := CFSG.KD.Fi24Cp.KV5 89
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l731 : List Nat := [CFSG.KD.Fi24Cp.Pc.v717, CFSG.KD.Fi24Cp.Pc.v718, CFSG.KD.Fi24Cp.Pc.v719, CFSG.KD.Fi24Cp.Pc.v720, CFSG.KD.Fi24Cp.Pc.v721, CFSG.KD.Fi24Cp.Pc.v722, CFSG.KD.Fi24Cp.Pc.v723, CFSG.KD.Fi24Cp.Pc.v724, CFSG.KD.Fi24Cp.Pc.v725, CFSG.KD.Fi24Cp.Pc.v726, CFSG.KD.Fi24Cp.Pc.v727, CFSG.KD.Fi24Cp.Pc.v728, CFSG.KD.Fi24Cp.Pc.v729, CFSG.KD.Fi24Cp.Pc.v730]
theorem CFSG.KD.Fi24Cp.Pc.p729 : Nat.beq (runC AR SD 717 (ckL CFSG.KD.Fi24Cp.Pc.l731) 2 729 CFSG.KD.Fi24Cp.Pc.l729) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v731 : Nat := CFSG.KD.Fi24Cp.KV5 90
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v732 : Nat := CFSG.KD.Fi24Cp.KV5 91
theorem CFSG.KD.Fi24Cp.Pc.f55 : Nat.beq (runC AR SD 717 (finC AR SD (nat_lit 55) 717 733) 2 731 CFSG.KD.Fi24Cp.Pc.l731) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk55 : chk (nat_lit 55) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 55) (lo := 717) (hi := 733) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 719) CFSG.KD.Fi24Cp.Pc.p717 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 721) CFSG.KD.Fi24Cp.Pc.p719 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 723) CFSG.KD.Fi24Cp.Pc.p721 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 725) CFSG.KD.Fi24Cp.Pc.p723 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 727) CFSG.KD.Fi24Cp.Pc.p725 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 729) CFSG.KD.Fi24Cp.Pc.p727 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 731) CFSG.KD.Fi24Cp.Pc.p729 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f55

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v733 : Nat := CFSG.KD.Fi24Cp.KV5 92
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l734 : List Nat := [CFSG.KD.Fi24Cp.Pc.v733]
theorem CFSG.KD.Fi24Cp.Pc.p733 : Nat.beq (runC AR SD 733 (ckL CFSG.KD.Fi24Cp.Pc.l734) 1 733 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.a734_1 : Nat := CFSG.KD.Fi24Cp.KV5 93
theorem CFSG.KD.Fi24Cp.Pc.q734_1 : Nat.beq (powTop AR.mul (getV AR SD 733 CFSG.KD.Fi24Cp.Pc.l734 (SD.na.getD 734 0)) (SD.nk.getD 734 1) 1 (ckP CFSG.KD.Fi24Cp.Pc.a734_1) 15 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v734 : Nat := CFSG.KD.Fi24Cp.KV5 94
theorem CFSG.KD.Fi24Cp.Pc.r734 : Nat.beq (powR AR.mul AR.one (getV AR SD 733 CFSG.KD.Fi24Cp.Pc.l734 (SD.na.getD 734 0)) (SD.nk.getD 734 1) 1 CFSG.KD.Fi24Cp.Pc.a734_1 true) CFSG.KD.Fi24Cp.Pc.v734 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v735 : Nat := CFSG.KD.Fi24Cp.KV5 95
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v736 : Nat := CFSG.KD.Fi24Cp.KV5 96
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l735 : List Nat := [CFSG.KD.Fi24Cp.Pc.v733, CFSG.KD.Fi24Cp.Pc.v734]
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l737 : List Nat := [CFSG.KD.Fi24Cp.Pc.v733, CFSG.KD.Fi24Cp.Pc.v734, CFSG.KD.Fi24Cp.Pc.v735, CFSG.KD.Fi24Cp.Pc.v736]
theorem CFSG.KD.Fi24Cp.Pc.p735 : Nat.beq (runC AR SD 733 (ckL CFSG.KD.Fi24Cp.Pc.l737) 2 735 CFSG.KD.Fi24Cp.Pc.l735) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v737 : Nat := CFSG.KD.Fi24Cp.KV5 97
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v738 : Nat := CFSG.KD.Fi24Cp.KV5 98
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l739 : List Nat := [CFSG.KD.Fi24Cp.Pc.v733, CFSG.KD.Fi24Cp.Pc.v734, CFSG.KD.Fi24Cp.Pc.v735, CFSG.KD.Fi24Cp.Pc.v736, CFSG.KD.Fi24Cp.Pc.v737, CFSG.KD.Fi24Cp.Pc.v738]
theorem CFSG.KD.Fi24Cp.Pc.p737 : Nat.beq (runC AR SD 733 (ckL CFSG.KD.Fi24Cp.Pc.l739) 2 737 CFSG.KD.Fi24Cp.Pc.l737) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v739 : Nat := CFSG.KD.Fi24Cp.KV5 99
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v740 : Nat := CFSG.KD.Fi24Cp.KV5 100
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l741 : List Nat := [CFSG.KD.Fi24Cp.Pc.v733, CFSG.KD.Fi24Cp.Pc.v734, CFSG.KD.Fi24Cp.Pc.v735, CFSG.KD.Fi24Cp.Pc.v736, CFSG.KD.Fi24Cp.Pc.v737, CFSG.KD.Fi24Cp.Pc.v738, CFSG.KD.Fi24Cp.Pc.v739, CFSG.KD.Fi24Cp.Pc.v740]
theorem CFSG.KD.Fi24Cp.Pc.p739 : Nat.beq (runC AR SD 733 (ckL CFSG.KD.Fi24Cp.Pc.l741) 2 739 CFSG.KD.Fi24Cp.Pc.l739) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v741 : Nat := CFSG.KD.Fi24Cp.KV5 101
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v742 : Nat := CFSG.KD.Fi24Cp.KV5 102
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l743 : List Nat := [CFSG.KD.Fi24Cp.Pc.v733, CFSG.KD.Fi24Cp.Pc.v734, CFSG.KD.Fi24Cp.Pc.v735, CFSG.KD.Fi24Cp.Pc.v736, CFSG.KD.Fi24Cp.Pc.v737, CFSG.KD.Fi24Cp.Pc.v738, CFSG.KD.Fi24Cp.Pc.v739, CFSG.KD.Fi24Cp.Pc.v740, CFSG.KD.Fi24Cp.Pc.v741, CFSG.KD.Fi24Cp.Pc.v742]
theorem CFSG.KD.Fi24Cp.Pc.p741 : Nat.beq (runC AR SD 733 (ckL CFSG.KD.Fi24Cp.Pc.l743) 2 741 CFSG.KD.Fi24Cp.Pc.l741) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v743 : Nat := CFSG.KD.Fi24Cp.KV5 103
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v744 : Nat := CFSG.KD.Fi24Cp.KV5 104
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l745 : List Nat := [CFSG.KD.Fi24Cp.Pc.v733, CFSG.KD.Fi24Cp.Pc.v734, CFSG.KD.Fi24Cp.Pc.v735, CFSG.KD.Fi24Cp.Pc.v736, CFSG.KD.Fi24Cp.Pc.v737, CFSG.KD.Fi24Cp.Pc.v738, CFSG.KD.Fi24Cp.Pc.v739, CFSG.KD.Fi24Cp.Pc.v740, CFSG.KD.Fi24Cp.Pc.v741, CFSG.KD.Fi24Cp.Pc.v742, CFSG.KD.Fi24Cp.Pc.v743, CFSG.KD.Fi24Cp.Pc.v744]
theorem CFSG.KD.Fi24Cp.Pc.p743 : Nat.beq (runC AR SD 733 (ckL CFSG.KD.Fi24Cp.Pc.l745) 2 743 CFSG.KD.Fi24Cp.Pc.l743) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v745 : Nat := CFSG.KD.Fi24Cp.KV5 105
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v746 : Nat := CFSG.KD.Fi24Cp.KV5 106
theorem CFSG.KD.Fi24Cp.Pc.f56 : Nat.beq (runC AR SD 733 (finC AR SD (nat_lit 56) 733 747) 2 745 CFSG.KD.Fi24Cp.Pc.l745) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk56 : chk (nat_lit 56) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 56) (lo := 733) (hi := 747) (m := 14) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 14) (m2 := 13) (j2 := 734) CFSG.KD.Fi24Cp.Pc.p733 rfl rfl).trans ((runC_node (m := 13) (m2 := 12) (j2 := 735) (Lr := CFSG.KD.Fi24Cp.Pc.l735) ((nodeV_pow (R := AR) (D := SD) (lo := 733) (L := CFSG.KD.Fi24Cp.Pc.l734) (j := 734) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 733 CFSG.KD.Fi24Cp.Pc.l734 (SD.na.getD 734 0)) (SD.nk.getD 734 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Cp.Pc.q734_1 rfl).trans (powR_last CFSG.KD.Fi24Cp.Pc.r734)))) (by quickRfl) rfl rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 737) CFSG.KD.Fi24Cp.Pc.p735 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 739) CFSG.KD.Fi24Cp.Pc.p737 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 741) CFSG.KD.Fi24Cp.Pc.p739 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 743) CFSG.KD.Fi24Cp.Pc.p741 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 745) CFSG.KD.Fi24Cp.Pc.p743 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f56

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v747 : Nat := CFSG.KD.Fi24Cp.KV5 107
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v748 : Nat := CFSG.KD.Fi24Cp.KV5 108
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l749 : List Nat := [CFSG.KD.Fi24Cp.Pc.v747, CFSG.KD.Fi24Cp.Pc.v748]
theorem CFSG.KD.Fi24Cp.Pc.p747 : Nat.beq (runC AR SD 747 (ckL CFSG.KD.Fi24Cp.Pc.l749) 2 747 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v749 : Nat := CFSG.KD.Fi24Cp.KV5 109
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v750 : Nat := CFSG.KD.Fi24Cp.KV5 110
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l751 : List Nat := [CFSG.KD.Fi24Cp.Pc.v747, CFSG.KD.Fi24Cp.Pc.v748, CFSG.KD.Fi24Cp.Pc.v749, CFSG.KD.Fi24Cp.Pc.v750]
theorem CFSG.KD.Fi24Cp.Pc.p749 : Nat.beq (runC AR SD 747 (ckL CFSG.KD.Fi24Cp.Pc.l751) 2 749 CFSG.KD.Fi24Cp.Pc.l749) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v751 : Nat := CFSG.KD.Fi24Cp.KV5 111
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v752 : Nat := CFSG.KD.Fi24Cp.KV5 112
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l753 : List Nat := [CFSG.KD.Fi24Cp.Pc.v747, CFSG.KD.Fi24Cp.Pc.v748, CFSG.KD.Fi24Cp.Pc.v749, CFSG.KD.Fi24Cp.Pc.v750, CFSG.KD.Fi24Cp.Pc.v751, CFSG.KD.Fi24Cp.Pc.v752]
theorem CFSG.KD.Fi24Cp.Pc.p751 : Nat.beq (runC AR SD 747 (ckL CFSG.KD.Fi24Cp.Pc.l753) 2 751 CFSG.KD.Fi24Cp.Pc.l751) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v753 : Nat := CFSG.KD.Fi24Cp.KV5 113
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v754 : Nat := CFSG.KD.Fi24Cp.KV5 114
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l755 : List Nat := [CFSG.KD.Fi24Cp.Pc.v747, CFSG.KD.Fi24Cp.Pc.v748, CFSG.KD.Fi24Cp.Pc.v749, CFSG.KD.Fi24Cp.Pc.v750, CFSG.KD.Fi24Cp.Pc.v751, CFSG.KD.Fi24Cp.Pc.v752, CFSG.KD.Fi24Cp.Pc.v753, CFSG.KD.Fi24Cp.Pc.v754]
theorem CFSG.KD.Fi24Cp.Pc.p753 : Nat.beq (runC AR SD 747 (ckL CFSG.KD.Fi24Cp.Pc.l755) 2 753 CFSG.KD.Fi24Cp.Pc.l753) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v755 : Nat := CFSG.KD.Fi24Cp.KV5 115
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v756 : Nat := CFSG.KD.Fi24Cp.KV5 116
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l757 : List Nat := [CFSG.KD.Fi24Cp.Pc.v747, CFSG.KD.Fi24Cp.Pc.v748, CFSG.KD.Fi24Cp.Pc.v749, CFSG.KD.Fi24Cp.Pc.v750, CFSG.KD.Fi24Cp.Pc.v751, CFSG.KD.Fi24Cp.Pc.v752, CFSG.KD.Fi24Cp.Pc.v753, CFSG.KD.Fi24Cp.Pc.v754, CFSG.KD.Fi24Cp.Pc.v755, CFSG.KD.Fi24Cp.Pc.v756]
theorem CFSG.KD.Fi24Cp.Pc.p755 : Nat.beq (runC AR SD 747 (ckL CFSG.KD.Fi24Cp.Pc.l757) 2 755 CFSG.KD.Fi24Cp.Pc.l755) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v757 : Nat := CFSG.KD.Fi24Cp.KV5 117
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v758 : Nat := CFSG.KD.Fi24Cp.KV5 118
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l759 : List Nat := [CFSG.KD.Fi24Cp.Pc.v747, CFSG.KD.Fi24Cp.Pc.v748, CFSG.KD.Fi24Cp.Pc.v749, CFSG.KD.Fi24Cp.Pc.v750, CFSG.KD.Fi24Cp.Pc.v751, CFSG.KD.Fi24Cp.Pc.v752, CFSG.KD.Fi24Cp.Pc.v753, CFSG.KD.Fi24Cp.Pc.v754, CFSG.KD.Fi24Cp.Pc.v755, CFSG.KD.Fi24Cp.Pc.v756, CFSG.KD.Fi24Cp.Pc.v757, CFSG.KD.Fi24Cp.Pc.v758]
theorem CFSG.KD.Fi24Cp.Pc.p757 : Nat.beq (runC AR SD 747 (ckL CFSG.KD.Fi24Cp.Pc.l759) 2 757 CFSG.KD.Fi24Cp.Pc.l757) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v759 : Nat := CFSG.KD.Fi24Cp.KV5 119
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v760 : Nat := CFSG.KD.Fi24Cp.KV5 120
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l761 : List Nat := [CFSG.KD.Fi24Cp.Pc.v747, CFSG.KD.Fi24Cp.Pc.v748, CFSG.KD.Fi24Cp.Pc.v749, CFSG.KD.Fi24Cp.Pc.v750, CFSG.KD.Fi24Cp.Pc.v751, CFSG.KD.Fi24Cp.Pc.v752, CFSG.KD.Fi24Cp.Pc.v753, CFSG.KD.Fi24Cp.Pc.v754, CFSG.KD.Fi24Cp.Pc.v755, CFSG.KD.Fi24Cp.Pc.v756, CFSG.KD.Fi24Cp.Pc.v757, CFSG.KD.Fi24Cp.Pc.v758, CFSG.KD.Fi24Cp.Pc.v759, CFSG.KD.Fi24Cp.Pc.v760]
theorem CFSG.KD.Fi24Cp.Pc.p759 : Nat.beq (runC AR SD 747 (ckL CFSG.KD.Fi24Cp.Pc.l761) 2 759 CFSG.KD.Fi24Cp.Pc.l759) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v761 : Nat := CFSG.KD.Fi24Cp.KV5 121
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v762 : Nat := CFSG.KD.Fi24Cp.KV5 122
theorem CFSG.KD.Fi24Cp.Pc.f57 : Nat.beq (runC AR SD 747 (finC AR SD (nat_lit 57) 747 763) 2 761 CFSG.KD.Fi24Cp.Pc.l761) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk57 : chk (nat_lit 57) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 57) (lo := 747) (hi := 763) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 749) CFSG.KD.Fi24Cp.Pc.p747 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 751) CFSG.KD.Fi24Cp.Pc.p749 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 753) CFSG.KD.Fi24Cp.Pc.p751 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 755) CFSG.KD.Fi24Cp.Pc.p753 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 757) CFSG.KD.Fi24Cp.Pc.p755 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 759) CFSG.KD.Fi24Cp.Pc.p757 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 761) CFSG.KD.Fi24Cp.Pc.p759 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f57

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v763 : Nat := CFSG.KD.Fi24Cp.KV5 123
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v764 : Nat := CFSG.KD.Fi24Cp.KV5 124
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l765 : List Nat := [CFSG.KD.Fi24Cp.Pc.v763, CFSG.KD.Fi24Cp.Pc.v764]
theorem CFSG.KD.Fi24Cp.Pc.p763 : Nat.beq (runC AR SD 763 (ckL CFSG.KD.Fi24Cp.Pc.l765) 2 763 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v765 : Nat := CFSG.KD.Fi24Cp.KV5 125
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v766 : Nat := CFSG.KD.Fi24Cp.KV5 126
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l767 : List Nat := [CFSG.KD.Fi24Cp.Pc.v763, CFSG.KD.Fi24Cp.Pc.v764, CFSG.KD.Fi24Cp.Pc.v765, CFSG.KD.Fi24Cp.Pc.v766]
theorem CFSG.KD.Fi24Cp.Pc.p765 : Nat.beq (runC AR SD 763 (ckL CFSG.KD.Fi24Cp.Pc.l767) 2 765 CFSG.KD.Fi24Cp.Pc.l765) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v767 : Nat := CFSG.KD.Fi24Cp.KV5 127
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v768 : Nat := CFSG.KD.Fi24Cp.KV5 128
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l769 : List Nat := [CFSG.KD.Fi24Cp.Pc.v763, CFSG.KD.Fi24Cp.Pc.v764, CFSG.KD.Fi24Cp.Pc.v765, CFSG.KD.Fi24Cp.Pc.v766, CFSG.KD.Fi24Cp.Pc.v767, CFSG.KD.Fi24Cp.Pc.v768]
theorem CFSG.KD.Fi24Cp.Pc.p767 : Nat.beq (runC AR SD 763 (ckL CFSG.KD.Fi24Cp.Pc.l769) 2 767 CFSG.KD.Fi24Cp.Pc.l767) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v769 : Nat := CFSG.KD.Fi24Cp.KV5 129
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v770 : Nat := CFSG.KD.Fi24Cp.KV5 130
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l771 : List Nat := [CFSG.KD.Fi24Cp.Pc.v763, CFSG.KD.Fi24Cp.Pc.v764, CFSG.KD.Fi24Cp.Pc.v765, CFSG.KD.Fi24Cp.Pc.v766, CFSG.KD.Fi24Cp.Pc.v767, CFSG.KD.Fi24Cp.Pc.v768, CFSG.KD.Fi24Cp.Pc.v769, CFSG.KD.Fi24Cp.Pc.v770]
theorem CFSG.KD.Fi24Cp.Pc.p769 : Nat.beq (runC AR SD 763 (ckL CFSG.KD.Fi24Cp.Pc.l771) 2 769 CFSG.KD.Fi24Cp.Pc.l769) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v771 : Nat := CFSG.KD.Fi24Cp.KV5 131
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v772 : Nat := CFSG.KD.Fi24Cp.KV5 132
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l773 : List Nat := [CFSG.KD.Fi24Cp.Pc.v763, CFSG.KD.Fi24Cp.Pc.v764, CFSG.KD.Fi24Cp.Pc.v765, CFSG.KD.Fi24Cp.Pc.v766, CFSG.KD.Fi24Cp.Pc.v767, CFSG.KD.Fi24Cp.Pc.v768, CFSG.KD.Fi24Cp.Pc.v769, CFSG.KD.Fi24Cp.Pc.v770, CFSG.KD.Fi24Cp.Pc.v771, CFSG.KD.Fi24Cp.Pc.v772]
theorem CFSG.KD.Fi24Cp.Pc.p771 : Nat.beq (runC AR SD 763 (ckL CFSG.KD.Fi24Cp.Pc.l773) 2 771 CFSG.KD.Fi24Cp.Pc.l771) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v773 : Nat := CFSG.KD.Fi24Cp.KV5 133
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v774 : Nat := CFSG.KD.Fi24Cp.KV5 134
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l775 : List Nat := [CFSG.KD.Fi24Cp.Pc.v763, CFSG.KD.Fi24Cp.Pc.v764, CFSG.KD.Fi24Cp.Pc.v765, CFSG.KD.Fi24Cp.Pc.v766, CFSG.KD.Fi24Cp.Pc.v767, CFSG.KD.Fi24Cp.Pc.v768, CFSG.KD.Fi24Cp.Pc.v769, CFSG.KD.Fi24Cp.Pc.v770, CFSG.KD.Fi24Cp.Pc.v771, CFSG.KD.Fi24Cp.Pc.v772, CFSG.KD.Fi24Cp.Pc.v773, CFSG.KD.Fi24Cp.Pc.v774]
theorem CFSG.KD.Fi24Cp.Pc.p773 : Nat.beq (runC AR SD 763 (ckL CFSG.KD.Fi24Cp.Pc.l775) 2 773 CFSG.KD.Fi24Cp.Pc.l773) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v775 : Nat := CFSG.KD.Fi24Cp.KV5 135
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v776 : Nat := CFSG.KD.Fi24Cp.KV5 136
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l777 : List Nat := [CFSG.KD.Fi24Cp.Pc.v763, CFSG.KD.Fi24Cp.Pc.v764, CFSG.KD.Fi24Cp.Pc.v765, CFSG.KD.Fi24Cp.Pc.v766, CFSG.KD.Fi24Cp.Pc.v767, CFSG.KD.Fi24Cp.Pc.v768, CFSG.KD.Fi24Cp.Pc.v769, CFSG.KD.Fi24Cp.Pc.v770, CFSG.KD.Fi24Cp.Pc.v771, CFSG.KD.Fi24Cp.Pc.v772, CFSG.KD.Fi24Cp.Pc.v773, CFSG.KD.Fi24Cp.Pc.v774, CFSG.KD.Fi24Cp.Pc.v775, CFSG.KD.Fi24Cp.Pc.v776]
theorem CFSG.KD.Fi24Cp.Pc.p775 : Nat.beq (runC AR SD 763 (ckL CFSG.KD.Fi24Cp.Pc.l777) 2 775 CFSG.KD.Fi24Cp.Pc.l775) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v777 : Nat := CFSG.KD.Fi24Cp.KV5 137
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v778 : Nat := CFSG.KD.Fi24Cp.KV5 138
theorem CFSG.KD.Fi24Cp.Pc.f58 : Nat.beq (runC AR SD 763 (finC AR SD (nat_lit 58) 763 779) 2 777 CFSG.KD.Fi24Cp.Pc.l777) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk58 : chk (nat_lit 58) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 58) (lo := 763) (hi := 779) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 765) CFSG.KD.Fi24Cp.Pc.p763 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 767) CFSG.KD.Fi24Cp.Pc.p765 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 769) CFSG.KD.Fi24Cp.Pc.p767 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 771) CFSG.KD.Fi24Cp.Pc.p769 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 773) CFSG.KD.Fi24Cp.Pc.p771 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 775) CFSG.KD.Fi24Cp.Pc.p773 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 777) CFSG.KD.Fi24Cp.Pc.p775 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f58

@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v779 : Nat := CFSG.KD.Fi24Cp.KV5 139
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v780 : Nat := CFSG.KD.Fi24Cp.KV5 140
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l781 : List Nat := [CFSG.KD.Fi24Cp.Pc.v779, CFSG.KD.Fi24Cp.Pc.v780]
theorem CFSG.KD.Fi24Cp.Pc.p779 : Nat.beq (runC AR SD 779 (ckL CFSG.KD.Fi24Cp.Pc.l781) 2 779 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v781 : Nat := CFSG.KD.Fi24Cp.KV5 141
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v782 : Nat := CFSG.KD.Fi24Cp.KV5 142
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l783 : List Nat := [CFSG.KD.Fi24Cp.Pc.v779, CFSG.KD.Fi24Cp.Pc.v780, CFSG.KD.Fi24Cp.Pc.v781, CFSG.KD.Fi24Cp.Pc.v782]
theorem CFSG.KD.Fi24Cp.Pc.p781 : Nat.beq (runC AR SD 779 (ckL CFSG.KD.Fi24Cp.Pc.l783) 2 781 CFSG.KD.Fi24Cp.Pc.l781) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v783 : Nat := CFSG.KD.Fi24Cp.KV5 143
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v784 : Nat := CFSG.KD.Fi24Cp.KV5 144
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l785 : List Nat := [CFSG.KD.Fi24Cp.Pc.v779, CFSG.KD.Fi24Cp.Pc.v780, CFSG.KD.Fi24Cp.Pc.v781, CFSG.KD.Fi24Cp.Pc.v782, CFSG.KD.Fi24Cp.Pc.v783, CFSG.KD.Fi24Cp.Pc.v784]
theorem CFSG.KD.Fi24Cp.Pc.p783 : Nat.beq (runC AR SD 779 (ckL CFSG.KD.Fi24Cp.Pc.l785) 2 783 CFSG.KD.Fi24Cp.Pc.l783) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v785 : Nat := CFSG.KD.Fi24Cp.KV5 145
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v786 : Nat := CFSG.KD.Fi24Cp.KV5 146
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l787 : List Nat := [CFSG.KD.Fi24Cp.Pc.v779, CFSG.KD.Fi24Cp.Pc.v780, CFSG.KD.Fi24Cp.Pc.v781, CFSG.KD.Fi24Cp.Pc.v782, CFSG.KD.Fi24Cp.Pc.v783, CFSG.KD.Fi24Cp.Pc.v784, CFSG.KD.Fi24Cp.Pc.v785, CFSG.KD.Fi24Cp.Pc.v786]
theorem CFSG.KD.Fi24Cp.Pc.p785 : Nat.beq (runC AR SD 779 (ckL CFSG.KD.Fi24Cp.Pc.l787) 2 785 CFSG.KD.Fi24Cp.Pc.l785) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v787 : Nat := CFSG.KD.Fi24Cp.KV5 147
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v788 : Nat := CFSG.KD.Fi24Cp.KV5 148
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l789 : List Nat := [CFSG.KD.Fi24Cp.Pc.v779, CFSG.KD.Fi24Cp.Pc.v780, CFSG.KD.Fi24Cp.Pc.v781, CFSG.KD.Fi24Cp.Pc.v782, CFSG.KD.Fi24Cp.Pc.v783, CFSG.KD.Fi24Cp.Pc.v784, CFSG.KD.Fi24Cp.Pc.v785, CFSG.KD.Fi24Cp.Pc.v786, CFSG.KD.Fi24Cp.Pc.v787, CFSG.KD.Fi24Cp.Pc.v788]
theorem CFSG.KD.Fi24Cp.Pc.p787 : Nat.beq (runC AR SD 779 (ckL CFSG.KD.Fi24Cp.Pc.l789) 2 787 CFSG.KD.Fi24Cp.Pc.l787) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v789 : Nat := CFSG.KD.Fi24Cp.KV5 149
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v790 : Nat := CFSG.KD.Fi24Cp.KV5 150
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l791 : List Nat := [CFSG.KD.Fi24Cp.Pc.v779, CFSG.KD.Fi24Cp.Pc.v780, CFSG.KD.Fi24Cp.Pc.v781, CFSG.KD.Fi24Cp.Pc.v782, CFSG.KD.Fi24Cp.Pc.v783, CFSG.KD.Fi24Cp.Pc.v784, CFSG.KD.Fi24Cp.Pc.v785, CFSG.KD.Fi24Cp.Pc.v786, CFSG.KD.Fi24Cp.Pc.v787, CFSG.KD.Fi24Cp.Pc.v788, CFSG.KD.Fi24Cp.Pc.v789, CFSG.KD.Fi24Cp.Pc.v790]
theorem CFSG.KD.Fi24Cp.Pc.p789 : Nat.beq (runC AR SD 779 (ckL CFSG.KD.Fi24Cp.Pc.l791) 2 789 CFSG.KD.Fi24Cp.Pc.l789) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v791 : Nat := CFSG.KD.Fi24Cp.KV5 151
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v792 : Nat := CFSG.KD.Fi24Cp.KV5 152
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.l793 : List Nat := [CFSG.KD.Fi24Cp.Pc.v779, CFSG.KD.Fi24Cp.Pc.v780, CFSG.KD.Fi24Cp.Pc.v781, CFSG.KD.Fi24Cp.Pc.v782, CFSG.KD.Fi24Cp.Pc.v783, CFSG.KD.Fi24Cp.Pc.v784, CFSG.KD.Fi24Cp.Pc.v785, CFSG.KD.Fi24Cp.Pc.v786, CFSG.KD.Fi24Cp.Pc.v787, CFSG.KD.Fi24Cp.Pc.v788, CFSG.KD.Fi24Cp.Pc.v789, CFSG.KD.Fi24Cp.Pc.v790, CFSG.KD.Fi24Cp.Pc.v791, CFSG.KD.Fi24Cp.Pc.v792]
theorem CFSG.KD.Fi24Cp.Pc.p791 : Nat.beq (runC AR SD 779 (ckL CFSG.KD.Fi24Cp.Pc.l793) 2 791 CFSG.KD.Fi24Cp.Pc.l791) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v793 : Nat := CFSG.KD.Fi24Cp.KV5 153
@[expose] noncomputable def CFSG.KD.Fi24Cp.Pc.v794 : Nat := CFSG.KD.Fi24Cp.KV5 154
theorem CFSG.KD.Fi24Cp.Pc.f59 : Nat.beq (runC AR SD 779 (finC AR SD (nat_lit 59) 779 795) 2 793 CFSG.KD.Fi24Cp.Pc.l793) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Cp.chk59 : chk (nat_lit 59) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 59) (lo := 779) (hi := 795) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 781) CFSG.KD.Fi24Cp.Pc.p779 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 783) CFSG.KD.Fi24Cp.Pc.p781 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 785) CFSG.KD.Fi24Cp.Pc.p783 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 787) CFSG.KD.Fi24Cp.Pc.p785 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 789) CFSG.KD.Fi24Cp.Pc.p787 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 791) CFSG.KD.Fi24Cp.Pc.p789 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 793) CFSG.KD.Fi24Cp.Pc.p791 rfl rfl))))))))).trans CFSG.KD.Fi24Cp.Pc.f59

end
