module

public import Certificates.Kernel.Sporadic.Fi24Alpha.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Alpha KV5 "Certificates/Kernel/Sporadic/Fi24Alpha/data/v5.bin" 152491 4 23178632 3077889766621782446

public section

open CFSG.KD.Fi24Alpha CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v684 : Nat := CFSG.KD.Fi24Alpha.KV5 0
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v685 : Nat := CFSG.KD.Fi24Alpha.KV5 1
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l686 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v684, CFSG.KD.Fi24Alpha.Pc.v685]
theorem CFSG.KD.Fi24Alpha.Pc.p684 : Nat.beq (runC AR SD 684 (ckL CFSG.KD.Fi24Alpha.Pc.l686) 2 684 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v686 : Nat := CFSG.KD.Fi24Alpha.KV5 2
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v687 : Nat := CFSG.KD.Fi24Alpha.KV5 3
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l688 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v684, CFSG.KD.Fi24Alpha.Pc.v685, CFSG.KD.Fi24Alpha.Pc.v686, CFSG.KD.Fi24Alpha.Pc.v687]
theorem CFSG.KD.Fi24Alpha.Pc.p686 : Nat.beq (runC AR SD 684 (ckL CFSG.KD.Fi24Alpha.Pc.l688) 2 686 CFSG.KD.Fi24Alpha.Pc.l686) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v688 : Nat := CFSG.KD.Fi24Alpha.KV5 4
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v689 : Nat := CFSG.KD.Fi24Alpha.KV5 5
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l690 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v684, CFSG.KD.Fi24Alpha.Pc.v685, CFSG.KD.Fi24Alpha.Pc.v686, CFSG.KD.Fi24Alpha.Pc.v687, CFSG.KD.Fi24Alpha.Pc.v688, CFSG.KD.Fi24Alpha.Pc.v689]
theorem CFSG.KD.Fi24Alpha.Pc.p688 : Nat.beq (runC AR SD 684 (ckL CFSG.KD.Fi24Alpha.Pc.l690) 2 688 CFSG.KD.Fi24Alpha.Pc.l688) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v690 : Nat := CFSG.KD.Fi24Alpha.KV5 6
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v691 : Nat := CFSG.KD.Fi24Alpha.KV5 7
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l692 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v684, CFSG.KD.Fi24Alpha.Pc.v685, CFSG.KD.Fi24Alpha.Pc.v686, CFSG.KD.Fi24Alpha.Pc.v687, CFSG.KD.Fi24Alpha.Pc.v688, CFSG.KD.Fi24Alpha.Pc.v689, CFSG.KD.Fi24Alpha.Pc.v690, CFSG.KD.Fi24Alpha.Pc.v691]
theorem CFSG.KD.Fi24Alpha.Pc.p690 : Nat.beq (runC AR SD 684 (ckL CFSG.KD.Fi24Alpha.Pc.l692) 2 690 CFSG.KD.Fi24Alpha.Pc.l690) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v692 : Nat := CFSG.KD.Fi24Alpha.KV5 8
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v693 : Nat := CFSG.KD.Fi24Alpha.KV5 9
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l694 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v684, CFSG.KD.Fi24Alpha.Pc.v685, CFSG.KD.Fi24Alpha.Pc.v686, CFSG.KD.Fi24Alpha.Pc.v687, CFSG.KD.Fi24Alpha.Pc.v688, CFSG.KD.Fi24Alpha.Pc.v689, CFSG.KD.Fi24Alpha.Pc.v690, CFSG.KD.Fi24Alpha.Pc.v691, CFSG.KD.Fi24Alpha.Pc.v692, CFSG.KD.Fi24Alpha.Pc.v693]
theorem CFSG.KD.Fi24Alpha.Pc.p692 : Nat.beq (runC AR SD 684 (ckL CFSG.KD.Fi24Alpha.Pc.l694) 2 692 CFSG.KD.Fi24Alpha.Pc.l692) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v694 : Nat := CFSG.KD.Fi24Alpha.KV5 10
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v695 : Nat := CFSG.KD.Fi24Alpha.KV5 11
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l696 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v684, CFSG.KD.Fi24Alpha.Pc.v685, CFSG.KD.Fi24Alpha.Pc.v686, CFSG.KD.Fi24Alpha.Pc.v687, CFSG.KD.Fi24Alpha.Pc.v688, CFSG.KD.Fi24Alpha.Pc.v689, CFSG.KD.Fi24Alpha.Pc.v690, CFSG.KD.Fi24Alpha.Pc.v691, CFSG.KD.Fi24Alpha.Pc.v692, CFSG.KD.Fi24Alpha.Pc.v693, CFSG.KD.Fi24Alpha.Pc.v694, CFSG.KD.Fi24Alpha.Pc.v695]
theorem CFSG.KD.Fi24Alpha.Pc.p694 : Nat.beq (runC AR SD 684 (ckL CFSG.KD.Fi24Alpha.Pc.l696) 2 694 CFSG.KD.Fi24Alpha.Pc.l694) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v696 : Nat := CFSG.KD.Fi24Alpha.KV5 12
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v697 : Nat := CFSG.KD.Fi24Alpha.KV5 13
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l698 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v684, CFSG.KD.Fi24Alpha.Pc.v685, CFSG.KD.Fi24Alpha.Pc.v686, CFSG.KD.Fi24Alpha.Pc.v687, CFSG.KD.Fi24Alpha.Pc.v688, CFSG.KD.Fi24Alpha.Pc.v689, CFSG.KD.Fi24Alpha.Pc.v690, CFSG.KD.Fi24Alpha.Pc.v691, CFSG.KD.Fi24Alpha.Pc.v692, CFSG.KD.Fi24Alpha.Pc.v693, CFSG.KD.Fi24Alpha.Pc.v694, CFSG.KD.Fi24Alpha.Pc.v695, CFSG.KD.Fi24Alpha.Pc.v696, CFSG.KD.Fi24Alpha.Pc.v697]
theorem CFSG.KD.Fi24Alpha.Pc.p696 : Nat.beq (runC AR SD 684 (ckL CFSG.KD.Fi24Alpha.Pc.l698) 2 696 CFSG.KD.Fi24Alpha.Pc.l696) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v698 : Nat := CFSG.KD.Fi24Alpha.KV5 14
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v699 : Nat := CFSG.KD.Fi24Alpha.KV5 15
theorem CFSG.KD.Fi24Alpha.Pc.f50 : Nat.beq (runC AR SD 684 (finC AR SD (nat_lit 50) 684 700) 2 698 CFSG.KD.Fi24Alpha.Pc.l698) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk50 : chk (nat_lit 50) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 50) (lo := 684) (hi := 700) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 686) CFSG.KD.Fi24Alpha.Pc.p684 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 688) CFSG.KD.Fi24Alpha.Pc.p686 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 690) CFSG.KD.Fi24Alpha.Pc.p688 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 692) CFSG.KD.Fi24Alpha.Pc.p690 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 694) CFSG.KD.Fi24Alpha.Pc.p692 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 696) CFSG.KD.Fi24Alpha.Pc.p694 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 698) CFSG.KD.Fi24Alpha.Pc.p696 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f50

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v700 : Nat := CFSG.KD.Fi24Alpha.KV5 16
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v701 : Nat := CFSG.KD.Fi24Alpha.KV5 17
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l702 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v700, CFSG.KD.Fi24Alpha.Pc.v701]
theorem CFSG.KD.Fi24Alpha.Pc.p700 : Nat.beq (runC AR SD 700 (ckL CFSG.KD.Fi24Alpha.Pc.l702) 2 700 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v702 : Nat := CFSG.KD.Fi24Alpha.KV5 18
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v703 : Nat := CFSG.KD.Fi24Alpha.KV5 19
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l704 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v700, CFSG.KD.Fi24Alpha.Pc.v701, CFSG.KD.Fi24Alpha.Pc.v702, CFSG.KD.Fi24Alpha.Pc.v703]
theorem CFSG.KD.Fi24Alpha.Pc.p702 : Nat.beq (runC AR SD 700 (ckL CFSG.KD.Fi24Alpha.Pc.l704) 2 702 CFSG.KD.Fi24Alpha.Pc.l702) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v704 : Nat := CFSG.KD.Fi24Alpha.KV5 20
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v705 : Nat := CFSG.KD.Fi24Alpha.KV5 21
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l706 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v700, CFSG.KD.Fi24Alpha.Pc.v701, CFSG.KD.Fi24Alpha.Pc.v702, CFSG.KD.Fi24Alpha.Pc.v703, CFSG.KD.Fi24Alpha.Pc.v704, CFSG.KD.Fi24Alpha.Pc.v705]
theorem CFSG.KD.Fi24Alpha.Pc.p704 : Nat.beq (runC AR SD 700 (ckL CFSG.KD.Fi24Alpha.Pc.l706) 2 704 CFSG.KD.Fi24Alpha.Pc.l704) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v706 : Nat := CFSG.KD.Fi24Alpha.KV5 22
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v707 : Nat := CFSG.KD.Fi24Alpha.KV5 23
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l708 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v700, CFSG.KD.Fi24Alpha.Pc.v701, CFSG.KD.Fi24Alpha.Pc.v702, CFSG.KD.Fi24Alpha.Pc.v703, CFSG.KD.Fi24Alpha.Pc.v704, CFSG.KD.Fi24Alpha.Pc.v705, CFSG.KD.Fi24Alpha.Pc.v706, CFSG.KD.Fi24Alpha.Pc.v707]
theorem CFSG.KD.Fi24Alpha.Pc.p706 : Nat.beq (runC AR SD 700 (ckL CFSG.KD.Fi24Alpha.Pc.l708) 2 706 CFSG.KD.Fi24Alpha.Pc.l706) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v708 : Nat := CFSG.KD.Fi24Alpha.KV5 24
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v709 : Nat := CFSG.KD.Fi24Alpha.KV5 25
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l710 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v700, CFSG.KD.Fi24Alpha.Pc.v701, CFSG.KD.Fi24Alpha.Pc.v702, CFSG.KD.Fi24Alpha.Pc.v703, CFSG.KD.Fi24Alpha.Pc.v704, CFSG.KD.Fi24Alpha.Pc.v705, CFSG.KD.Fi24Alpha.Pc.v706, CFSG.KD.Fi24Alpha.Pc.v707, CFSG.KD.Fi24Alpha.Pc.v708, CFSG.KD.Fi24Alpha.Pc.v709]
theorem CFSG.KD.Fi24Alpha.Pc.p708 : Nat.beq (runC AR SD 700 (ckL CFSG.KD.Fi24Alpha.Pc.l710) 2 708 CFSG.KD.Fi24Alpha.Pc.l708) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v710 : Nat := CFSG.KD.Fi24Alpha.KV5 26
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v711 : Nat := CFSG.KD.Fi24Alpha.KV5 27
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l712 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v700, CFSG.KD.Fi24Alpha.Pc.v701, CFSG.KD.Fi24Alpha.Pc.v702, CFSG.KD.Fi24Alpha.Pc.v703, CFSG.KD.Fi24Alpha.Pc.v704, CFSG.KD.Fi24Alpha.Pc.v705, CFSG.KD.Fi24Alpha.Pc.v706, CFSG.KD.Fi24Alpha.Pc.v707, CFSG.KD.Fi24Alpha.Pc.v708, CFSG.KD.Fi24Alpha.Pc.v709, CFSG.KD.Fi24Alpha.Pc.v710, CFSG.KD.Fi24Alpha.Pc.v711]
theorem CFSG.KD.Fi24Alpha.Pc.p710 : Nat.beq (runC AR SD 700 (ckL CFSG.KD.Fi24Alpha.Pc.l712) 2 710 CFSG.KD.Fi24Alpha.Pc.l710) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v712 : Nat := CFSG.KD.Fi24Alpha.KV5 28
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v713 : Nat := CFSG.KD.Fi24Alpha.KV5 29
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l714 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v700, CFSG.KD.Fi24Alpha.Pc.v701, CFSG.KD.Fi24Alpha.Pc.v702, CFSG.KD.Fi24Alpha.Pc.v703, CFSG.KD.Fi24Alpha.Pc.v704, CFSG.KD.Fi24Alpha.Pc.v705, CFSG.KD.Fi24Alpha.Pc.v706, CFSG.KD.Fi24Alpha.Pc.v707, CFSG.KD.Fi24Alpha.Pc.v708, CFSG.KD.Fi24Alpha.Pc.v709, CFSG.KD.Fi24Alpha.Pc.v710, CFSG.KD.Fi24Alpha.Pc.v711, CFSG.KD.Fi24Alpha.Pc.v712, CFSG.KD.Fi24Alpha.Pc.v713]
theorem CFSG.KD.Fi24Alpha.Pc.p712 : Nat.beq (runC AR SD 700 (ckL CFSG.KD.Fi24Alpha.Pc.l714) 2 712 CFSG.KD.Fi24Alpha.Pc.l712) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v714 : Nat := CFSG.KD.Fi24Alpha.KV5 30
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v715 : Nat := CFSG.KD.Fi24Alpha.KV5 31
theorem CFSG.KD.Fi24Alpha.Pc.f51 : Nat.beq (runC AR SD 700 (finC AR SD (nat_lit 51) 700 716) 2 714 CFSG.KD.Fi24Alpha.Pc.l714) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk51 : chk (nat_lit 51) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 51) (lo := 700) (hi := 716) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 702) CFSG.KD.Fi24Alpha.Pc.p700 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 704) CFSG.KD.Fi24Alpha.Pc.p702 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 706) CFSG.KD.Fi24Alpha.Pc.p704 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 708) CFSG.KD.Fi24Alpha.Pc.p706 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 710) CFSG.KD.Fi24Alpha.Pc.p708 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 712) CFSG.KD.Fi24Alpha.Pc.p710 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 714) CFSG.KD.Fi24Alpha.Pc.p712 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f51

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v716 : Nat := CFSG.KD.Fi24Alpha.KV5 32
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v717 : Nat := CFSG.KD.Fi24Alpha.KV5 33
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l718 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v716, CFSG.KD.Fi24Alpha.Pc.v717]
theorem CFSG.KD.Fi24Alpha.Pc.p716 : Nat.beq (runC AR SD 716 (ckL CFSG.KD.Fi24Alpha.Pc.l718) 2 716 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v718 : Nat := CFSG.KD.Fi24Alpha.KV5 34
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v719 : Nat := CFSG.KD.Fi24Alpha.KV5 35
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l720 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v716, CFSG.KD.Fi24Alpha.Pc.v717, CFSG.KD.Fi24Alpha.Pc.v718, CFSG.KD.Fi24Alpha.Pc.v719]
theorem CFSG.KD.Fi24Alpha.Pc.p718 : Nat.beq (runC AR SD 716 (ckL CFSG.KD.Fi24Alpha.Pc.l720) 2 718 CFSG.KD.Fi24Alpha.Pc.l718) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v720 : Nat := CFSG.KD.Fi24Alpha.KV5 36
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v721 : Nat := CFSG.KD.Fi24Alpha.KV5 37
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l722 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v716, CFSG.KD.Fi24Alpha.Pc.v717, CFSG.KD.Fi24Alpha.Pc.v718, CFSG.KD.Fi24Alpha.Pc.v719, CFSG.KD.Fi24Alpha.Pc.v720, CFSG.KD.Fi24Alpha.Pc.v721]
theorem CFSG.KD.Fi24Alpha.Pc.p720 : Nat.beq (runC AR SD 716 (ckL CFSG.KD.Fi24Alpha.Pc.l722) 2 720 CFSG.KD.Fi24Alpha.Pc.l720) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v722 : Nat := CFSG.KD.Fi24Alpha.KV5 38
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v723 : Nat := CFSG.KD.Fi24Alpha.KV5 39
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l724 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v716, CFSG.KD.Fi24Alpha.Pc.v717, CFSG.KD.Fi24Alpha.Pc.v718, CFSG.KD.Fi24Alpha.Pc.v719, CFSG.KD.Fi24Alpha.Pc.v720, CFSG.KD.Fi24Alpha.Pc.v721, CFSG.KD.Fi24Alpha.Pc.v722, CFSG.KD.Fi24Alpha.Pc.v723]
theorem CFSG.KD.Fi24Alpha.Pc.p722 : Nat.beq (runC AR SD 716 (ckL CFSG.KD.Fi24Alpha.Pc.l724) 2 722 CFSG.KD.Fi24Alpha.Pc.l722) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v724 : Nat := CFSG.KD.Fi24Alpha.KV5 40
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v725 : Nat := CFSG.KD.Fi24Alpha.KV5 41
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l726 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v716, CFSG.KD.Fi24Alpha.Pc.v717, CFSG.KD.Fi24Alpha.Pc.v718, CFSG.KD.Fi24Alpha.Pc.v719, CFSG.KD.Fi24Alpha.Pc.v720, CFSG.KD.Fi24Alpha.Pc.v721, CFSG.KD.Fi24Alpha.Pc.v722, CFSG.KD.Fi24Alpha.Pc.v723, CFSG.KD.Fi24Alpha.Pc.v724, CFSG.KD.Fi24Alpha.Pc.v725]
theorem CFSG.KD.Fi24Alpha.Pc.p724 : Nat.beq (runC AR SD 716 (ckL CFSG.KD.Fi24Alpha.Pc.l726) 2 724 CFSG.KD.Fi24Alpha.Pc.l724) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v726 : Nat := CFSG.KD.Fi24Alpha.KV5 42
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v727 : Nat := CFSG.KD.Fi24Alpha.KV5 43
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l728 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v716, CFSG.KD.Fi24Alpha.Pc.v717, CFSG.KD.Fi24Alpha.Pc.v718, CFSG.KD.Fi24Alpha.Pc.v719, CFSG.KD.Fi24Alpha.Pc.v720, CFSG.KD.Fi24Alpha.Pc.v721, CFSG.KD.Fi24Alpha.Pc.v722, CFSG.KD.Fi24Alpha.Pc.v723, CFSG.KD.Fi24Alpha.Pc.v724, CFSG.KD.Fi24Alpha.Pc.v725, CFSG.KD.Fi24Alpha.Pc.v726, CFSG.KD.Fi24Alpha.Pc.v727]
theorem CFSG.KD.Fi24Alpha.Pc.p726 : Nat.beq (runC AR SD 716 (ckL CFSG.KD.Fi24Alpha.Pc.l728) 2 726 CFSG.KD.Fi24Alpha.Pc.l726) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v728 : Nat := CFSG.KD.Fi24Alpha.KV5 44
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v729 : Nat := CFSG.KD.Fi24Alpha.KV5 45
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l730 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v716, CFSG.KD.Fi24Alpha.Pc.v717, CFSG.KD.Fi24Alpha.Pc.v718, CFSG.KD.Fi24Alpha.Pc.v719, CFSG.KD.Fi24Alpha.Pc.v720, CFSG.KD.Fi24Alpha.Pc.v721, CFSG.KD.Fi24Alpha.Pc.v722, CFSG.KD.Fi24Alpha.Pc.v723, CFSG.KD.Fi24Alpha.Pc.v724, CFSG.KD.Fi24Alpha.Pc.v725, CFSG.KD.Fi24Alpha.Pc.v726, CFSG.KD.Fi24Alpha.Pc.v727, CFSG.KD.Fi24Alpha.Pc.v728, CFSG.KD.Fi24Alpha.Pc.v729]
theorem CFSG.KD.Fi24Alpha.Pc.p728 : Nat.beq (runC AR SD 716 (ckL CFSG.KD.Fi24Alpha.Pc.l730) 2 728 CFSG.KD.Fi24Alpha.Pc.l728) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v730 : Nat := CFSG.KD.Fi24Alpha.KV5 46
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v731 : Nat := CFSG.KD.Fi24Alpha.KV5 47
theorem CFSG.KD.Fi24Alpha.Pc.f52 : Nat.beq (runC AR SD 716 (finC AR SD (nat_lit 52) 716 732) 2 730 CFSG.KD.Fi24Alpha.Pc.l730) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk52 : chk (nat_lit 52) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 52) (lo := 716) (hi := 732) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 718) CFSG.KD.Fi24Alpha.Pc.p716 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 720) CFSG.KD.Fi24Alpha.Pc.p718 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 722) CFSG.KD.Fi24Alpha.Pc.p720 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 724) CFSG.KD.Fi24Alpha.Pc.p722 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 726) CFSG.KD.Fi24Alpha.Pc.p724 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 728) CFSG.KD.Fi24Alpha.Pc.p726 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 730) CFSG.KD.Fi24Alpha.Pc.p728 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f52

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v732 : Nat := CFSG.KD.Fi24Alpha.KV5 48
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v733 : Nat := CFSG.KD.Fi24Alpha.KV5 49
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l734 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v732, CFSG.KD.Fi24Alpha.Pc.v733]
theorem CFSG.KD.Fi24Alpha.Pc.p732 : Nat.beq (runC AR SD 732 (ckL CFSG.KD.Fi24Alpha.Pc.l734) 2 732 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v734 : Nat := CFSG.KD.Fi24Alpha.KV5 50
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v735 : Nat := CFSG.KD.Fi24Alpha.KV5 51
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l736 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v732, CFSG.KD.Fi24Alpha.Pc.v733, CFSG.KD.Fi24Alpha.Pc.v734, CFSG.KD.Fi24Alpha.Pc.v735]
theorem CFSG.KD.Fi24Alpha.Pc.p734 : Nat.beq (runC AR SD 732 (ckL CFSG.KD.Fi24Alpha.Pc.l736) 2 734 CFSG.KD.Fi24Alpha.Pc.l734) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v736 : Nat := CFSG.KD.Fi24Alpha.KV5 52
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v737 : Nat := CFSG.KD.Fi24Alpha.KV5 53
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l738 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v732, CFSG.KD.Fi24Alpha.Pc.v733, CFSG.KD.Fi24Alpha.Pc.v734, CFSG.KD.Fi24Alpha.Pc.v735, CFSG.KD.Fi24Alpha.Pc.v736, CFSG.KD.Fi24Alpha.Pc.v737]
theorem CFSG.KD.Fi24Alpha.Pc.p736 : Nat.beq (runC AR SD 732 (ckL CFSG.KD.Fi24Alpha.Pc.l738) 2 736 CFSG.KD.Fi24Alpha.Pc.l736) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v738 : Nat := CFSG.KD.Fi24Alpha.KV5 54
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v739 : Nat := CFSG.KD.Fi24Alpha.KV5 55
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l740 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v732, CFSG.KD.Fi24Alpha.Pc.v733, CFSG.KD.Fi24Alpha.Pc.v734, CFSG.KD.Fi24Alpha.Pc.v735, CFSG.KD.Fi24Alpha.Pc.v736, CFSG.KD.Fi24Alpha.Pc.v737, CFSG.KD.Fi24Alpha.Pc.v738, CFSG.KD.Fi24Alpha.Pc.v739]
theorem CFSG.KD.Fi24Alpha.Pc.p738 : Nat.beq (runC AR SD 732 (ckL CFSG.KD.Fi24Alpha.Pc.l740) 2 738 CFSG.KD.Fi24Alpha.Pc.l738) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v740 : Nat := CFSG.KD.Fi24Alpha.KV5 56
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v741 : Nat := CFSG.KD.Fi24Alpha.KV5 57
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l742 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v732, CFSG.KD.Fi24Alpha.Pc.v733, CFSG.KD.Fi24Alpha.Pc.v734, CFSG.KD.Fi24Alpha.Pc.v735, CFSG.KD.Fi24Alpha.Pc.v736, CFSG.KD.Fi24Alpha.Pc.v737, CFSG.KD.Fi24Alpha.Pc.v738, CFSG.KD.Fi24Alpha.Pc.v739, CFSG.KD.Fi24Alpha.Pc.v740, CFSG.KD.Fi24Alpha.Pc.v741]
theorem CFSG.KD.Fi24Alpha.Pc.p740 : Nat.beq (runC AR SD 732 (ckL CFSG.KD.Fi24Alpha.Pc.l742) 2 740 CFSG.KD.Fi24Alpha.Pc.l740) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v742 : Nat := CFSG.KD.Fi24Alpha.KV5 58
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v743 : Nat := CFSG.KD.Fi24Alpha.KV5 59
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l744 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v732, CFSG.KD.Fi24Alpha.Pc.v733, CFSG.KD.Fi24Alpha.Pc.v734, CFSG.KD.Fi24Alpha.Pc.v735, CFSG.KD.Fi24Alpha.Pc.v736, CFSG.KD.Fi24Alpha.Pc.v737, CFSG.KD.Fi24Alpha.Pc.v738, CFSG.KD.Fi24Alpha.Pc.v739, CFSG.KD.Fi24Alpha.Pc.v740, CFSG.KD.Fi24Alpha.Pc.v741, CFSG.KD.Fi24Alpha.Pc.v742, CFSG.KD.Fi24Alpha.Pc.v743]
theorem CFSG.KD.Fi24Alpha.Pc.p742 : Nat.beq (runC AR SD 732 (ckL CFSG.KD.Fi24Alpha.Pc.l744) 2 742 CFSG.KD.Fi24Alpha.Pc.l742) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v744 : Nat := CFSG.KD.Fi24Alpha.KV5 60
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v745 : Nat := CFSG.KD.Fi24Alpha.KV5 61
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l746 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v732, CFSG.KD.Fi24Alpha.Pc.v733, CFSG.KD.Fi24Alpha.Pc.v734, CFSG.KD.Fi24Alpha.Pc.v735, CFSG.KD.Fi24Alpha.Pc.v736, CFSG.KD.Fi24Alpha.Pc.v737, CFSG.KD.Fi24Alpha.Pc.v738, CFSG.KD.Fi24Alpha.Pc.v739, CFSG.KD.Fi24Alpha.Pc.v740, CFSG.KD.Fi24Alpha.Pc.v741, CFSG.KD.Fi24Alpha.Pc.v742, CFSG.KD.Fi24Alpha.Pc.v743, CFSG.KD.Fi24Alpha.Pc.v744, CFSG.KD.Fi24Alpha.Pc.v745]
theorem CFSG.KD.Fi24Alpha.Pc.p744 : Nat.beq (runC AR SD 732 (ckL CFSG.KD.Fi24Alpha.Pc.l746) 2 744 CFSG.KD.Fi24Alpha.Pc.l744) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v746 : Nat := CFSG.KD.Fi24Alpha.KV5 62
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v747 : Nat := CFSG.KD.Fi24Alpha.KV5 63
theorem CFSG.KD.Fi24Alpha.Pc.f53 : Nat.beq (runC AR SD 732 (finC AR SD (nat_lit 53) 732 748) 2 746 CFSG.KD.Fi24Alpha.Pc.l746) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk53 : chk (nat_lit 53) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 53) (lo := 732) (hi := 748) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 734) CFSG.KD.Fi24Alpha.Pc.p732 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 736) CFSG.KD.Fi24Alpha.Pc.p734 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 738) CFSG.KD.Fi24Alpha.Pc.p736 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 740) CFSG.KD.Fi24Alpha.Pc.p738 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 742) CFSG.KD.Fi24Alpha.Pc.p740 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 744) CFSG.KD.Fi24Alpha.Pc.p742 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 746) CFSG.KD.Fi24Alpha.Pc.p744 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f53

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v748 : Nat := CFSG.KD.Fi24Alpha.KV5 64
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v749 : Nat := CFSG.KD.Fi24Alpha.KV5 65
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l750 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v748, CFSG.KD.Fi24Alpha.Pc.v749]
theorem CFSG.KD.Fi24Alpha.Pc.p748 : Nat.beq (runC AR SD 748 (ckL CFSG.KD.Fi24Alpha.Pc.l750) 2 748 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v750 : Nat := CFSG.KD.Fi24Alpha.KV5 66
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v751 : Nat := CFSG.KD.Fi24Alpha.KV5 67
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l752 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v748, CFSG.KD.Fi24Alpha.Pc.v749, CFSG.KD.Fi24Alpha.Pc.v750, CFSG.KD.Fi24Alpha.Pc.v751]
theorem CFSG.KD.Fi24Alpha.Pc.p750 : Nat.beq (runC AR SD 748 (ckL CFSG.KD.Fi24Alpha.Pc.l752) 2 750 CFSG.KD.Fi24Alpha.Pc.l750) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v752 : Nat := CFSG.KD.Fi24Alpha.KV5 68
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v753 : Nat := CFSG.KD.Fi24Alpha.KV5 69
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l754 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v748, CFSG.KD.Fi24Alpha.Pc.v749, CFSG.KD.Fi24Alpha.Pc.v750, CFSG.KD.Fi24Alpha.Pc.v751, CFSG.KD.Fi24Alpha.Pc.v752, CFSG.KD.Fi24Alpha.Pc.v753]
theorem CFSG.KD.Fi24Alpha.Pc.p752 : Nat.beq (runC AR SD 748 (ckL CFSG.KD.Fi24Alpha.Pc.l754) 2 752 CFSG.KD.Fi24Alpha.Pc.l752) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v754 : Nat := CFSG.KD.Fi24Alpha.KV5 70
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v755 : Nat := CFSG.KD.Fi24Alpha.KV5 71
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l756 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v748, CFSG.KD.Fi24Alpha.Pc.v749, CFSG.KD.Fi24Alpha.Pc.v750, CFSG.KD.Fi24Alpha.Pc.v751, CFSG.KD.Fi24Alpha.Pc.v752, CFSG.KD.Fi24Alpha.Pc.v753, CFSG.KD.Fi24Alpha.Pc.v754, CFSG.KD.Fi24Alpha.Pc.v755]
theorem CFSG.KD.Fi24Alpha.Pc.p754 : Nat.beq (runC AR SD 748 (ckL CFSG.KD.Fi24Alpha.Pc.l756) 2 754 CFSG.KD.Fi24Alpha.Pc.l754) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v756 : Nat := CFSG.KD.Fi24Alpha.KV5 72
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v757 : Nat := CFSG.KD.Fi24Alpha.KV5 73
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l758 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v748, CFSG.KD.Fi24Alpha.Pc.v749, CFSG.KD.Fi24Alpha.Pc.v750, CFSG.KD.Fi24Alpha.Pc.v751, CFSG.KD.Fi24Alpha.Pc.v752, CFSG.KD.Fi24Alpha.Pc.v753, CFSG.KD.Fi24Alpha.Pc.v754, CFSG.KD.Fi24Alpha.Pc.v755, CFSG.KD.Fi24Alpha.Pc.v756, CFSG.KD.Fi24Alpha.Pc.v757]
theorem CFSG.KD.Fi24Alpha.Pc.p756 : Nat.beq (runC AR SD 748 (ckL CFSG.KD.Fi24Alpha.Pc.l758) 2 756 CFSG.KD.Fi24Alpha.Pc.l756) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v758 : Nat := CFSG.KD.Fi24Alpha.KV5 74
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v759 : Nat := CFSG.KD.Fi24Alpha.KV5 75
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l760 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v748, CFSG.KD.Fi24Alpha.Pc.v749, CFSG.KD.Fi24Alpha.Pc.v750, CFSG.KD.Fi24Alpha.Pc.v751, CFSG.KD.Fi24Alpha.Pc.v752, CFSG.KD.Fi24Alpha.Pc.v753, CFSG.KD.Fi24Alpha.Pc.v754, CFSG.KD.Fi24Alpha.Pc.v755, CFSG.KD.Fi24Alpha.Pc.v756, CFSG.KD.Fi24Alpha.Pc.v757, CFSG.KD.Fi24Alpha.Pc.v758, CFSG.KD.Fi24Alpha.Pc.v759]
theorem CFSG.KD.Fi24Alpha.Pc.p758 : Nat.beq (runC AR SD 748 (ckL CFSG.KD.Fi24Alpha.Pc.l760) 2 758 CFSG.KD.Fi24Alpha.Pc.l758) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v760 : Nat := CFSG.KD.Fi24Alpha.KV5 76
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v761 : Nat := CFSG.KD.Fi24Alpha.KV5 77
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l762 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v748, CFSG.KD.Fi24Alpha.Pc.v749, CFSG.KD.Fi24Alpha.Pc.v750, CFSG.KD.Fi24Alpha.Pc.v751, CFSG.KD.Fi24Alpha.Pc.v752, CFSG.KD.Fi24Alpha.Pc.v753, CFSG.KD.Fi24Alpha.Pc.v754, CFSG.KD.Fi24Alpha.Pc.v755, CFSG.KD.Fi24Alpha.Pc.v756, CFSG.KD.Fi24Alpha.Pc.v757, CFSG.KD.Fi24Alpha.Pc.v758, CFSG.KD.Fi24Alpha.Pc.v759, CFSG.KD.Fi24Alpha.Pc.v760, CFSG.KD.Fi24Alpha.Pc.v761]
theorem CFSG.KD.Fi24Alpha.Pc.p760 : Nat.beq (runC AR SD 748 (ckL CFSG.KD.Fi24Alpha.Pc.l762) 2 760 CFSG.KD.Fi24Alpha.Pc.l760) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v762 : Nat := CFSG.KD.Fi24Alpha.KV5 78
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v763 : Nat := CFSG.KD.Fi24Alpha.KV5 79
theorem CFSG.KD.Fi24Alpha.Pc.f54 : Nat.beq (runC AR SD 748 (finC AR SD (nat_lit 54) 748 764) 2 762 CFSG.KD.Fi24Alpha.Pc.l762) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk54 : chk (nat_lit 54) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 54) (lo := 748) (hi := 764) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 750) CFSG.KD.Fi24Alpha.Pc.p748 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 752) CFSG.KD.Fi24Alpha.Pc.p750 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 754) CFSG.KD.Fi24Alpha.Pc.p752 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 756) CFSG.KD.Fi24Alpha.Pc.p754 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 758) CFSG.KD.Fi24Alpha.Pc.p756 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 760) CFSG.KD.Fi24Alpha.Pc.p758 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 762) CFSG.KD.Fi24Alpha.Pc.p760 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f54

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v764 : Nat := CFSG.KD.Fi24Alpha.KV5 80
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v765 : Nat := CFSG.KD.Fi24Alpha.KV5 81
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l766 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v764, CFSG.KD.Fi24Alpha.Pc.v765]
theorem CFSG.KD.Fi24Alpha.Pc.p764 : Nat.beq (runC AR SD 764 (ckL CFSG.KD.Fi24Alpha.Pc.l766) 2 764 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v766 : Nat := CFSG.KD.Fi24Alpha.KV5 82
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v767 : Nat := CFSG.KD.Fi24Alpha.KV5 83
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l768 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v764, CFSG.KD.Fi24Alpha.Pc.v765, CFSG.KD.Fi24Alpha.Pc.v766, CFSG.KD.Fi24Alpha.Pc.v767]
theorem CFSG.KD.Fi24Alpha.Pc.p766 : Nat.beq (runC AR SD 764 (ckL CFSG.KD.Fi24Alpha.Pc.l768) 2 766 CFSG.KD.Fi24Alpha.Pc.l766) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v768 : Nat := CFSG.KD.Fi24Alpha.KV5 84
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v769 : Nat := CFSG.KD.Fi24Alpha.KV5 85
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l770 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v764, CFSG.KD.Fi24Alpha.Pc.v765, CFSG.KD.Fi24Alpha.Pc.v766, CFSG.KD.Fi24Alpha.Pc.v767, CFSG.KD.Fi24Alpha.Pc.v768, CFSG.KD.Fi24Alpha.Pc.v769]
theorem CFSG.KD.Fi24Alpha.Pc.p768 : Nat.beq (runC AR SD 764 (ckL CFSG.KD.Fi24Alpha.Pc.l770) 2 768 CFSG.KD.Fi24Alpha.Pc.l768) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v770 : Nat := CFSG.KD.Fi24Alpha.KV5 86
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v771 : Nat := CFSG.KD.Fi24Alpha.KV5 87
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l772 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v764, CFSG.KD.Fi24Alpha.Pc.v765, CFSG.KD.Fi24Alpha.Pc.v766, CFSG.KD.Fi24Alpha.Pc.v767, CFSG.KD.Fi24Alpha.Pc.v768, CFSG.KD.Fi24Alpha.Pc.v769, CFSG.KD.Fi24Alpha.Pc.v770, CFSG.KD.Fi24Alpha.Pc.v771]
theorem CFSG.KD.Fi24Alpha.Pc.p770 : Nat.beq (runC AR SD 764 (ckL CFSG.KD.Fi24Alpha.Pc.l772) 2 770 CFSG.KD.Fi24Alpha.Pc.l770) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v772 : Nat := CFSG.KD.Fi24Alpha.KV5 88
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v773 : Nat := CFSG.KD.Fi24Alpha.KV5 89
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l774 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v764, CFSG.KD.Fi24Alpha.Pc.v765, CFSG.KD.Fi24Alpha.Pc.v766, CFSG.KD.Fi24Alpha.Pc.v767, CFSG.KD.Fi24Alpha.Pc.v768, CFSG.KD.Fi24Alpha.Pc.v769, CFSG.KD.Fi24Alpha.Pc.v770, CFSG.KD.Fi24Alpha.Pc.v771, CFSG.KD.Fi24Alpha.Pc.v772, CFSG.KD.Fi24Alpha.Pc.v773]
theorem CFSG.KD.Fi24Alpha.Pc.p772 : Nat.beq (runC AR SD 764 (ckL CFSG.KD.Fi24Alpha.Pc.l774) 2 772 CFSG.KD.Fi24Alpha.Pc.l772) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v774 : Nat := CFSG.KD.Fi24Alpha.KV5 90
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v775 : Nat := CFSG.KD.Fi24Alpha.KV5 91
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l776 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v764, CFSG.KD.Fi24Alpha.Pc.v765, CFSG.KD.Fi24Alpha.Pc.v766, CFSG.KD.Fi24Alpha.Pc.v767, CFSG.KD.Fi24Alpha.Pc.v768, CFSG.KD.Fi24Alpha.Pc.v769, CFSG.KD.Fi24Alpha.Pc.v770, CFSG.KD.Fi24Alpha.Pc.v771, CFSG.KD.Fi24Alpha.Pc.v772, CFSG.KD.Fi24Alpha.Pc.v773, CFSG.KD.Fi24Alpha.Pc.v774, CFSG.KD.Fi24Alpha.Pc.v775]
theorem CFSG.KD.Fi24Alpha.Pc.p774 : Nat.beq (runC AR SD 764 (ckL CFSG.KD.Fi24Alpha.Pc.l776) 2 774 CFSG.KD.Fi24Alpha.Pc.l774) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v776 : Nat := CFSG.KD.Fi24Alpha.KV5 92
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v777 : Nat := CFSG.KD.Fi24Alpha.KV5 93
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l778 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v764, CFSG.KD.Fi24Alpha.Pc.v765, CFSG.KD.Fi24Alpha.Pc.v766, CFSG.KD.Fi24Alpha.Pc.v767, CFSG.KD.Fi24Alpha.Pc.v768, CFSG.KD.Fi24Alpha.Pc.v769, CFSG.KD.Fi24Alpha.Pc.v770, CFSG.KD.Fi24Alpha.Pc.v771, CFSG.KD.Fi24Alpha.Pc.v772, CFSG.KD.Fi24Alpha.Pc.v773, CFSG.KD.Fi24Alpha.Pc.v774, CFSG.KD.Fi24Alpha.Pc.v775, CFSG.KD.Fi24Alpha.Pc.v776, CFSG.KD.Fi24Alpha.Pc.v777]
theorem CFSG.KD.Fi24Alpha.Pc.p776 : Nat.beq (runC AR SD 764 (ckL CFSG.KD.Fi24Alpha.Pc.l778) 2 776 CFSG.KD.Fi24Alpha.Pc.l776) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v778 : Nat := CFSG.KD.Fi24Alpha.KV5 94
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v779 : Nat := CFSG.KD.Fi24Alpha.KV5 95
theorem CFSG.KD.Fi24Alpha.Pc.f55 : Nat.beq (runC AR SD 764 (finC AR SD (nat_lit 55) 764 780) 2 778 CFSG.KD.Fi24Alpha.Pc.l778) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk55 : chk (nat_lit 55) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 55) (lo := 764) (hi := 780) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 766) CFSG.KD.Fi24Alpha.Pc.p764 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 768) CFSG.KD.Fi24Alpha.Pc.p766 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 770) CFSG.KD.Fi24Alpha.Pc.p768 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 772) CFSG.KD.Fi24Alpha.Pc.p770 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 774) CFSG.KD.Fi24Alpha.Pc.p772 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 776) CFSG.KD.Fi24Alpha.Pc.p774 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 778) CFSG.KD.Fi24Alpha.Pc.p776 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f55

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v780 : Nat := CFSG.KD.Fi24Alpha.KV5 96
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v781 : Nat := CFSG.KD.Fi24Alpha.KV5 97
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l782 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v780, CFSG.KD.Fi24Alpha.Pc.v781]
theorem CFSG.KD.Fi24Alpha.Pc.p780 : Nat.beq (runC AR SD 780 (ckL CFSG.KD.Fi24Alpha.Pc.l782) 2 780 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v782 : Nat := CFSG.KD.Fi24Alpha.KV5 98
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v783 : Nat := CFSG.KD.Fi24Alpha.KV5 99
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l784 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v780, CFSG.KD.Fi24Alpha.Pc.v781, CFSG.KD.Fi24Alpha.Pc.v782, CFSG.KD.Fi24Alpha.Pc.v783]
theorem CFSG.KD.Fi24Alpha.Pc.p782 : Nat.beq (runC AR SD 780 (ckL CFSG.KD.Fi24Alpha.Pc.l784) 2 782 CFSG.KD.Fi24Alpha.Pc.l782) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v784 : Nat := CFSG.KD.Fi24Alpha.KV5 100
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v785 : Nat := CFSG.KD.Fi24Alpha.KV5 101
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l786 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v780, CFSG.KD.Fi24Alpha.Pc.v781, CFSG.KD.Fi24Alpha.Pc.v782, CFSG.KD.Fi24Alpha.Pc.v783, CFSG.KD.Fi24Alpha.Pc.v784, CFSG.KD.Fi24Alpha.Pc.v785]
theorem CFSG.KD.Fi24Alpha.Pc.p784 : Nat.beq (runC AR SD 780 (ckL CFSG.KD.Fi24Alpha.Pc.l786) 2 784 CFSG.KD.Fi24Alpha.Pc.l784) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v786 : Nat := CFSG.KD.Fi24Alpha.KV5 102
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v787 : Nat := CFSG.KD.Fi24Alpha.KV5 103
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l788 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v780, CFSG.KD.Fi24Alpha.Pc.v781, CFSG.KD.Fi24Alpha.Pc.v782, CFSG.KD.Fi24Alpha.Pc.v783, CFSG.KD.Fi24Alpha.Pc.v784, CFSG.KD.Fi24Alpha.Pc.v785, CFSG.KD.Fi24Alpha.Pc.v786, CFSG.KD.Fi24Alpha.Pc.v787]
theorem CFSG.KD.Fi24Alpha.Pc.p786 : Nat.beq (runC AR SD 780 (ckL CFSG.KD.Fi24Alpha.Pc.l788) 2 786 CFSG.KD.Fi24Alpha.Pc.l786) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v788 : Nat := CFSG.KD.Fi24Alpha.KV5 104
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v789 : Nat := CFSG.KD.Fi24Alpha.KV5 105
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l790 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v780, CFSG.KD.Fi24Alpha.Pc.v781, CFSG.KD.Fi24Alpha.Pc.v782, CFSG.KD.Fi24Alpha.Pc.v783, CFSG.KD.Fi24Alpha.Pc.v784, CFSG.KD.Fi24Alpha.Pc.v785, CFSG.KD.Fi24Alpha.Pc.v786, CFSG.KD.Fi24Alpha.Pc.v787, CFSG.KD.Fi24Alpha.Pc.v788, CFSG.KD.Fi24Alpha.Pc.v789]
theorem CFSG.KD.Fi24Alpha.Pc.p788 : Nat.beq (runC AR SD 780 (ckL CFSG.KD.Fi24Alpha.Pc.l790) 2 788 CFSG.KD.Fi24Alpha.Pc.l788) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v790 : Nat := CFSG.KD.Fi24Alpha.KV5 106
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v791 : Nat := CFSG.KD.Fi24Alpha.KV5 107
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l792 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v780, CFSG.KD.Fi24Alpha.Pc.v781, CFSG.KD.Fi24Alpha.Pc.v782, CFSG.KD.Fi24Alpha.Pc.v783, CFSG.KD.Fi24Alpha.Pc.v784, CFSG.KD.Fi24Alpha.Pc.v785, CFSG.KD.Fi24Alpha.Pc.v786, CFSG.KD.Fi24Alpha.Pc.v787, CFSG.KD.Fi24Alpha.Pc.v788, CFSG.KD.Fi24Alpha.Pc.v789, CFSG.KD.Fi24Alpha.Pc.v790, CFSG.KD.Fi24Alpha.Pc.v791]
theorem CFSG.KD.Fi24Alpha.Pc.p790 : Nat.beq (runC AR SD 780 (ckL CFSG.KD.Fi24Alpha.Pc.l792) 2 790 CFSG.KD.Fi24Alpha.Pc.l790) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v792 : Nat := CFSG.KD.Fi24Alpha.KV5 108
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v793 : Nat := CFSG.KD.Fi24Alpha.KV5 109
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l794 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v780, CFSG.KD.Fi24Alpha.Pc.v781, CFSG.KD.Fi24Alpha.Pc.v782, CFSG.KD.Fi24Alpha.Pc.v783, CFSG.KD.Fi24Alpha.Pc.v784, CFSG.KD.Fi24Alpha.Pc.v785, CFSG.KD.Fi24Alpha.Pc.v786, CFSG.KD.Fi24Alpha.Pc.v787, CFSG.KD.Fi24Alpha.Pc.v788, CFSG.KD.Fi24Alpha.Pc.v789, CFSG.KD.Fi24Alpha.Pc.v790, CFSG.KD.Fi24Alpha.Pc.v791, CFSG.KD.Fi24Alpha.Pc.v792, CFSG.KD.Fi24Alpha.Pc.v793]
theorem CFSG.KD.Fi24Alpha.Pc.p792 : Nat.beq (runC AR SD 780 (ckL CFSG.KD.Fi24Alpha.Pc.l794) 2 792 CFSG.KD.Fi24Alpha.Pc.l792) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v794 : Nat := CFSG.KD.Fi24Alpha.KV5 110
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v795 : Nat := CFSG.KD.Fi24Alpha.KV5 111
theorem CFSG.KD.Fi24Alpha.Pc.f56 : Nat.beq (runC AR SD 780 (finC AR SD (nat_lit 56) 780 796) 2 794 CFSG.KD.Fi24Alpha.Pc.l794) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk56 : chk (nat_lit 56) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 56) (lo := 780) (hi := 796) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 782) CFSG.KD.Fi24Alpha.Pc.p780 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 784) CFSG.KD.Fi24Alpha.Pc.p782 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 786) CFSG.KD.Fi24Alpha.Pc.p784 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 788) CFSG.KD.Fi24Alpha.Pc.p786 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 790) CFSG.KD.Fi24Alpha.Pc.p788 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 792) CFSG.KD.Fi24Alpha.Pc.p790 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 794) CFSG.KD.Fi24Alpha.Pc.p792 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f56

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v796 : Nat := CFSG.KD.Fi24Alpha.KV5 112
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v797 : Nat := CFSG.KD.Fi24Alpha.KV5 113
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l798 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v796, CFSG.KD.Fi24Alpha.Pc.v797]
theorem CFSG.KD.Fi24Alpha.Pc.p796 : Nat.beq (runC AR SD 796 (ckL CFSG.KD.Fi24Alpha.Pc.l798) 2 796 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v798 : Nat := CFSG.KD.Fi24Alpha.KV5 114
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v799 : Nat := CFSG.KD.Fi24Alpha.KV5 115
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l800 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v796, CFSG.KD.Fi24Alpha.Pc.v797, CFSG.KD.Fi24Alpha.Pc.v798, CFSG.KD.Fi24Alpha.Pc.v799]
theorem CFSG.KD.Fi24Alpha.Pc.p798 : Nat.beq (runC AR SD 796 (ckL CFSG.KD.Fi24Alpha.Pc.l800) 2 798 CFSG.KD.Fi24Alpha.Pc.l798) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v800 : Nat := CFSG.KD.Fi24Alpha.KV5 116
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v801 : Nat := CFSG.KD.Fi24Alpha.KV5 117
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l802 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v796, CFSG.KD.Fi24Alpha.Pc.v797, CFSG.KD.Fi24Alpha.Pc.v798, CFSG.KD.Fi24Alpha.Pc.v799, CFSG.KD.Fi24Alpha.Pc.v800, CFSG.KD.Fi24Alpha.Pc.v801]
theorem CFSG.KD.Fi24Alpha.Pc.p800 : Nat.beq (runC AR SD 796 (ckL CFSG.KD.Fi24Alpha.Pc.l802) 2 800 CFSG.KD.Fi24Alpha.Pc.l800) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v802 : Nat := CFSG.KD.Fi24Alpha.KV5 118
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v803 : Nat := CFSG.KD.Fi24Alpha.KV5 119
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l804 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v796, CFSG.KD.Fi24Alpha.Pc.v797, CFSG.KD.Fi24Alpha.Pc.v798, CFSG.KD.Fi24Alpha.Pc.v799, CFSG.KD.Fi24Alpha.Pc.v800, CFSG.KD.Fi24Alpha.Pc.v801, CFSG.KD.Fi24Alpha.Pc.v802, CFSG.KD.Fi24Alpha.Pc.v803]
theorem CFSG.KD.Fi24Alpha.Pc.p802 : Nat.beq (runC AR SD 796 (ckL CFSG.KD.Fi24Alpha.Pc.l804) 2 802 CFSG.KD.Fi24Alpha.Pc.l802) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v804 : Nat := CFSG.KD.Fi24Alpha.KV5 120
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v805 : Nat := CFSG.KD.Fi24Alpha.KV5 121
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l806 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v796, CFSG.KD.Fi24Alpha.Pc.v797, CFSG.KD.Fi24Alpha.Pc.v798, CFSG.KD.Fi24Alpha.Pc.v799, CFSG.KD.Fi24Alpha.Pc.v800, CFSG.KD.Fi24Alpha.Pc.v801, CFSG.KD.Fi24Alpha.Pc.v802, CFSG.KD.Fi24Alpha.Pc.v803, CFSG.KD.Fi24Alpha.Pc.v804, CFSG.KD.Fi24Alpha.Pc.v805]
theorem CFSG.KD.Fi24Alpha.Pc.p804 : Nat.beq (runC AR SD 796 (ckL CFSG.KD.Fi24Alpha.Pc.l806) 2 804 CFSG.KD.Fi24Alpha.Pc.l804) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v806 : Nat := CFSG.KD.Fi24Alpha.KV5 122
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v807 : Nat := CFSG.KD.Fi24Alpha.KV5 123
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l808 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v796, CFSG.KD.Fi24Alpha.Pc.v797, CFSG.KD.Fi24Alpha.Pc.v798, CFSG.KD.Fi24Alpha.Pc.v799, CFSG.KD.Fi24Alpha.Pc.v800, CFSG.KD.Fi24Alpha.Pc.v801, CFSG.KD.Fi24Alpha.Pc.v802, CFSG.KD.Fi24Alpha.Pc.v803, CFSG.KD.Fi24Alpha.Pc.v804, CFSG.KD.Fi24Alpha.Pc.v805, CFSG.KD.Fi24Alpha.Pc.v806, CFSG.KD.Fi24Alpha.Pc.v807]
theorem CFSG.KD.Fi24Alpha.Pc.p806 : Nat.beq (runC AR SD 796 (ckL CFSG.KD.Fi24Alpha.Pc.l808) 2 806 CFSG.KD.Fi24Alpha.Pc.l806) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v808 : Nat := CFSG.KD.Fi24Alpha.KV5 124
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v809 : Nat := CFSG.KD.Fi24Alpha.KV5 125
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l810 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v796, CFSG.KD.Fi24Alpha.Pc.v797, CFSG.KD.Fi24Alpha.Pc.v798, CFSG.KD.Fi24Alpha.Pc.v799, CFSG.KD.Fi24Alpha.Pc.v800, CFSG.KD.Fi24Alpha.Pc.v801, CFSG.KD.Fi24Alpha.Pc.v802, CFSG.KD.Fi24Alpha.Pc.v803, CFSG.KD.Fi24Alpha.Pc.v804, CFSG.KD.Fi24Alpha.Pc.v805, CFSG.KD.Fi24Alpha.Pc.v806, CFSG.KD.Fi24Alpha.Pc.v807, CFSG.KD.Fi24Alpha.Pc.v808, CFSG.KD.Fi24Alpha.Pc.v809]
theorem CFSG.KD.Fi24Alpha.Pc.p808 : Nat.beq (runC AR SD 796 (ckL CFSG.KD.Fi24Alpha.Pc.l810) 2 808 CFSG.KD.Fi24Alpha.Pc.l808) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v810 : Nat := CFSG.KD.Fi24Alpha.KV5 126
theorem CFSG.KD.Fi24Alpha.Pc.f57 : Nat.beq (runC AR SD 796 (finC AR SD (nat_lit 57) 796 811) 1 810 CFSG.KD.Fi24Alpha.Pc.l810) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk57 : chk (nat_lit 57) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 57) (lo := 796) (hi := 811) (m := 15) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 15) (m2 := 13) (j2 := 798) CFSG.KD.Fi24Alpha.Pc.p796 rfl rfl).trans ((runC_seq (m := 13) (m2 := 11) (j2 := 800) CFSG.KD.Fi24Alpha.Pc.p798 rfl rfl).trans ((runC_seq (m := 11) (m2 := 9) (j2 := 802) CFSG.KD.Fi24Alpha.Pc.p800 rfl rfl).trans ((runC_seq (m := 9) (m2 := 7) (j2 := 804) CFSG.KD.Fi24Alpha.Pc.p802 rfl rfl).trans ((runC_seq (m := 7) (m2 := 5) (j2 := 806) CFSG.KD.Fi24Alpha.Pc.p804 rfl rfl).trans ((runC_seq (m := 5) (m2 := 3) (j2 := 808) CFSG.KD.Fi24Alpha.Pc.p806 rfl rfl).trans (runC_seq (m := 3) (m2 := 1) (j2 := 810) CFSG.KD.Fi24Alpha.Pc.p808 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f57

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v811 : Nat := CFSG.KD.Fi24Alpha.KV5 127
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l812 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v811]
theorem CFSG.KD.Fi24Alpha.Pc.p811 : Nat.beq (runC AR SD 811 (ckL CFSG.KD.Fi24Alpha.Pc.l812) 1 811 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v812 : Nat := CFSG.KD.Fi24Alpha.KV5 128
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l813 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v811, CFSG.KD.Fi24Alpha.Pc.v812]
theorem CFSG.KD.Fi24Alpha.Pc.p812 : Nat.beq (runC AR SD 811 (ckL CFSG.KD.Fi24Alpha.Pc.l813) 1 812 CFSG.KD.Fi24Alpha.Pc.l812) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v813 : Nat := CFSG.KD.Fi24Alpha.KV5 129
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l814 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v811, CFSG.KD.Fi24Alpha.Pc.v812, CFSG.KD.Fi24Alpha.Pc.v813]
theorem CFSG.KD.Fi24Alpha.Pc.p813 : Nat.beq (runC AR SD 811 (ckL CFSG.KD.Fi24Alpha.Pc.l814) 1 813 CFSG.KD.Fi24Alpha.Pc.l813) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v814 : Nat := CFSG.KD.Fi24Alpha.KV5 130
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l815 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v811, CFSG.KD.Fi24Alpha.Pc.v812, CFSG.KD.Fi24Alpha.Pc.v813, CFSG.KD.Fi24Alpha.Pc.v814]
theorem CFSG.KD.Fi24Alpha.Pc.p814 : Nat.beq (runC AR SD 811 (ckL CFSG.KD.Fi24Alpha.Pc.l815) 1 814 CFSG.KD.Fi24Alpha.Pc.l814) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v815 : Nat := CFSG.KD.Fi24Alpha.KV5 131
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l816 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v811, CFSG.KD.Fi24Alpha.Pc.v812, CFSG.KD.Fi24Alpha.Pc.v813, CFSG.KD.Fi24Alpha.Pc.v814, CFSG.KD.Fi24Alpha.Pc.v815]
theorem CFSG.KD.Fi24Alpha.Pc.p815 : Nat.beq (runC AR SD 811 (ckL CFSG.KD.Fi24Alpha.Pc.l816) 1 815 CFSG.KD.Fi24Alpha.Pc.l815) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v816 : Nat := CFSG.KD.Fi24Alpha.KV5 132
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l817 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v811, CFSG.KD.Fi24Alpha.Pc.v812, CFSG.KD.Fi24Alpha.Pc.v813, CFSG.KD.Fi24Alpha.Pc.v814, CFSG.KD.Fi24Alpha.Pc.v815, CFSG.KD.Fi24Alpha.Pc.v816]
theorem CFSG.KD.Fi24Alpha.Pc.p816 : Nat.beq (runC AR SD 811 (ckL CFSG.KD.Fi24Alpha.Pc.l817) 1 816 CFSG.KD.Fi24Alpha.Pc.l816) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v817 : Nat := CFSG.KD.Fi24Alpha.KV5 133
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l818 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v811, CFSG.KD.Fi24Alpha.Pc.v812, CFSG.KD.Fi24Alpha.Pc.v813, CFSG.KD.Fi24Alpha.Pc.v814, CFSG.KD.Fi24Alpha.Pc.v815, CFSG.KD.Fi24Alpha.Pc.v816, CFSG.KD.Fi24Alpha.Pc.v817]
theorem CFSG.KD.Fi24Alpha.Pc.p817 : Nat.beq (runC AR SD 811 (ckL CFSG.KD.Fi24Alpha.Pc.l818) 1 817 CFSG.KD.Fi24Alpha.Pc.l817) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v818 : Nat := CFSG.KD.Fi24Alpha.KV5 134
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v819 : Nat := CFSG.KD.Fi24Alpha.KV5 135
theorem CFSG.KD.Fi24Alpha.Pc.f58 : Nat.beq (runC AR SD 811 (finC AR SD (nat_lit 58) 811 820) 2 818 CFSG.KD.Fi24Alpha.Pc.l818) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk58 : chk (nat_lit 58) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 58) (lo := 811) (hi := 820) (m := 9) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 9) (m2 := 8) (j2 := 812) CFSG.KD.Fi24Alpha.Pc.p811 rfl rfl).trans ((runC_seq (m := 8) (m2 := 7) (j2 := 813) CFSG.KD.Fi24Alpha.Pc.p812 rfl rfl).trans ((runC_seq (m := 7) (m2 := 6) (j2 := 814) CFSG.KD.Fi24Alpha.Pc.p813 rfl rfl).trans ((runC_seq (m := 6) (m2 := 5) (j2 := 815) CFSG.KD.Fi24Alpha.Pc.p814 rfl rfl).trans ((runC_seq (m := 5) (m2 := 4) (j2 := 816) CFSG.KD.Fi24Alpha.Pc.p815 rfl rfl).trans ((runC_seq (m := 4) (m2 := 3) (j2 := 817) CFSG.KD.Fi24Alpha.Pc.p816 rfl rfl).trans (runC_seq (m := 3) (m2 := 2) (j2 := 818) CFSG.KD.Fi24Alpha.Pc.p817 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f58

@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v820 : Nat := CFSG.KD.Fi24Alpha.KV5 136
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v821 : Nat := CFSG.KD.Fi24Alpha.KV5 137
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l822 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v820, CFSG.KD.Fi24Alpha.Pc.v821]
theorem CFSG.KD.Fi24Alpha.Pc.p820 : Nat.beq (runC AR SD 820 (ckL CFSG.KD.Fi24Alpha.Pc.l822) 2 820 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v822 : Nat := CFSG.KD.Fi24Alpha.KV5 138
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v823 : Nat := CFSG.KD.Fi24Alpha.KV5 139
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l824 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v820, CFSG.KD.Fi24Alpha.Pc.v821, CFSG.KD.Fi24Alpha.Pc.v822, CFSG.KD.Fi24Alpha.Pc.v823]
theorem CFSG.KD.Fi24Alpha.Pc.p822 : Nat.beq (runC AR SD 820 (ckL CFSG.KD.Fi24Alpha.Pc.l824) 2 822 CFSG.KD.Fi24Alpha.Pc.l822) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v824 : Nat := CFSG.KD.Fi24Alpha.KV5 140
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v825 : Nat := CFSG.KD.Fi24Alpha.KV5 141
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l826 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v820, CFSG.KD.Fi24Alpha.Pc.v821, CFSG.KD.Fi24Alpha.Pc.v822, CFSG.KD.Fi24Alpha.Pc.v823, CFSG.KD.Fi24Alpha.Pc.v824, CFSG.KD.Fi24Alpha.Pc.v825]
theorem CFSG.KD.Fi24Alpha.Pc.p824 : Nat.beq (runC AR SD 820 (ckL CFSG.KD.Fi24Alpha.Pc.l826) 2 824 CFSG.KD.Fi24Alpha.Pc.l824) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v826 : Nat := CFSG.KD.Fi24Alpha.KV5 142
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v827 : Nat := CFSG.KD.Fi24Alpha.KV5 143
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l828 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v820, CFSG.KD.Fi24Alpha.Pc.v821, CFSG.KD.Fi24Alpha.Pc.v822, CFSG.KD.Fi24Alpha.Pc.v823, CFSG.KD.Fi24Alpha.Pc.v824, CFSG.KD.Fi24Alpha.Pc.v825, CFSG.KD.Fi24Alpha.Pc.v826, CFSG.KD.Fi24Alpha.Pc.v827]
theorem CFSG.KD.Fi24Alpha.Pc.p826 : Nat.beq (runC AR SD 820 (ckL CFSG.KD.Fi24Alpha.Pc.l828) 2 826 CFSG.KD.Fi24Alpha.Pc.l826) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v828 : Nat := CFSG.KD.Fi24Alpha.KV5 144
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v829 : Nat := CFSG.KD.Fi24Alpha.KV5 145
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l830 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v820, CFSG.KD.Fi24Alpha.Pc.v821, CFSG.KD.Fi24Alpha.Pc.v822, CFSG.KD.Fi24Alpha.Pc.v823, CFSG.KD.Fi24Alpha.Pc.v824, CFSG.KD.Fi24Alpha.Pc.v825, CFSG.KD.Fi24Alpha.Pc.v826, CFSG.KD.Fi24Alpha.Pc.v827, CFSG.KD.Fi24Alpha.Pc.v828, CFSG.KD.Fi24Alpha.Pc.v829]
theorem CFSG.KD.Fi24Alpha.Pc.p828 : Nat.beq (runC AR SD 820 (ckL CFSG.KD.Fi24Alpha.Pc.l830) 2 828 CFSG.KD.Fi24Alpha.Pc.l828) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v830 : Nat := CFSG.KD.Fi24Alpha.KV5 146
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v831 : Nat := CFSG.KD.Fi24Alpha.KV5 147
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l832 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v820, CFSG.KD.Fi24Alpha.Pc.v821, CFSG.KD.Fi24Alpha.Pc.v822, CFSG.KD.Fi24Alpha.Pc.v823, CFSG.KD.Fi24Alpha.Pc.v824, CFSG.KD.Fi24Alpha.Pc.v825, CFSG.KD.Fi24Alpha.Pc.v826, CFSG.KD.Fi24Alpha.Pc.v827, CFSG.KD.Fi24Alpha.Pc.v828, CFSG.KD.Fi24Alpha.Pc.v829, CFSG.KD.Fi24Alpha.Pc.v830, CFSG.KD.Fi24Alpha.Pc.v831]
theorem CFSG.KD.Fi24Alpha.Pc.p830 : Nat.beq (runC AR SD 820 (ckL CFSG.KD.Fi24Alpha.Pc.l832) 2 830 CFSG.KD.Fi24Alpha.Pc.l830) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v832 : Nat := CFSG.KD.Fi24Alpha.KV5 148
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v833 : Nat := CFSG.KD.Fi24Alpha.KV5 149
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.l834 : List Nat := [CFSG.KD.Fi24Alpha.Pc.v820, CFSG.KD.Fi24Alpha.Pc.v821, CFSG.KD.Fi24Alpha.Pc.v822, CFSG.KD.Fi24Alpha.Pc.v823, CFSG.KD.Fi24Alpha.Pc.v824, CFSG.KD.Fi24Alpha.Pc.v825, CFSG.KD.Fi24Alpha.Pc.v826, CFSG.KD.Fi24Alpha.Pc.v827, CFSG.KD.Fi24Alpha.Pc.v828, CFSG.KD.Fi24Alpha.Pc.v829, CFSG.KD.Fi24Alpha.Pc.v830, CFSG.KD.Fi24Alpha.Pc.v831, CFSG.KD.Fi24Alpha.Pc.v832, CFSG.KD.Fi24Alpha.Pc.v833]
theorem CFSG.KD.Fi24Alpha.Pc.p832 : Nat.beq (runC AR SD 820 (ckL CFSG.KD.Fi24Alpha.Pc.l834) 2 832 CFSG.KD.Fi24Alpha.Pc.l832) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v834 : Nat := CFSG.KD.Fi24Alpha.KV5 150
@[expose] noncomputable def CFSG.KD.Fi24Alpha.Pc.v835 : Nat := CFSG.KD.Fi24Alpha.KV5 151
theorem CFSG.KD.Fi24Alpha.Pc.f59 : Nat.beq (runC AR SD 820 (finC AR SD (nat_lit 59) 820 836) 2 834 CFSG.KD.Fi24Alpha.Pc.l834) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Alpha.chk59 : chk (nat_lit 59) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 59) (lo := 820) (hi := 836) (m := 16) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 16) (m2 := 14) (j2 := 822) CFSG.KD.Fi24Alpha.Pc.p820 rfl rfl).trans ((runC_seq (m := 14) (m2 := 12) (j2 := 824) CFSG.KD.Fi24Alpha.Pc.p822 rfl rfl).trans ((runC_seq (m := 12) (m2 := 10) (j2 := 826) CFSG.KD.Fi24Alpha.Pc.p824 rfl rfl).trans ((runC_seq (m := 10) (m2 := 8) (j2 := 828) CFSG.KD.Fi24Alpha.Pc.p826 rfl rfl).trans ((runC_seq (m := 8) (m2 := 6) (j2 := 830) CFSG.KD.Fi24Alpha.Pc.p828 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 832) CFSG.KD.Fi24Alpha.Pc.p830 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 834) CFSG.KD.Fi24Alpha.Pc.p832 rfl rfl))))))))).trans CFSG.KD.Fi24Alpha.Pc.f59

end
