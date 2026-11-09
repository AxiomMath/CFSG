module

public import Certificates.Kernel.Sporadic.Fi24Tc.Data
public import CFSG.Certificates.Kernel.Ssa3Split
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

#kc_repo #kc_ktree CFSG.KD.Fi24Tc KV5 "Certificates/Kernel/Sporadic/Fi24Tc/data/v5.bin" 152491 4 14944118 16094075966058617647

public section

open CFSG.KD.Fi24Tc CFSG.KC.Ssa3 CFSG.KC.Ssa3Split

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v694 : Nat := CFSG.KD.Fi24Tc.KV5 92
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l695 : List Nat := [CFSG.KD.Fi24Tc.Pc.v694]
theorem CFSG.KD.Fi24Tc.Pc.p694 : Nat.beq (runC AR SD 694 (ckL CFSG.KD.Fi24Tc.Pc.l695) 1 694 []) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f100 : Nat.beq (runC AR SD 694 (finC AR SD (nat_lit 100) 694 697) 2 695 CFSG.KD.Fi24Tc.Pc.l695) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk100 : chk (nat_lit 100) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 100) (lo := 694) (hi := 697) (m := 3) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_seq (m := 3) (m2 := 2) (j2 := 695) CFSG.KD.Fi24Tc.Pc.p694 rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f100

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a697_2 : Nat := CFSG.KD.Fi24Tc.KV5 93
theorem CFSG.KD.Fi24Tc.Pc.q697_2 : Nat.beq (powTop AR.mul (getV AR SD 697 [] (SD.na.getD 697 0)) (SD.nk.getD 697 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a697_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a697_1 : Nat := CFSG.KD.Fi24Tc.KV5 94
theorem CFSG.KD.Fi24Tc.Pc.q697_1 : Nat.beq (powTop AR.mul (getV AR SD 697 [] (SD.na.getD 697 0)) (SD.nk.getD 697 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a697_1) 1 CFSG.KD.Fi24Tc.Pc.a697_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v697 : Nat := CFSG.KD.Fi24Tc.KV5 95
theorem CFSG.KD.Fi24Tc.Pc.r697 : Nat.beq (powR AR.mul AR.one (getV AR SD 697 [] (SD.na.getD 697 0)) (SD.nk.getD 697 1) 1 CFSG.KD.Fi24Tc.Pc.a697_1 true) CFSG.KD.Fi24Tc.Pc.v697 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l698 : List Nat := [CFSG.KD.Fi24Tc.Pc.v697]
theorem CFSG.KD.Fi24Tc.Pc.f101 : Nat.beq (runC AR SD 697 (finC AR SD (nat_lit 101) 697 698) 0 698 CFSG.KD.Fi24Tc.Pc.l698) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk101 : chk (nat_lit 101) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 101) (lo := 697) (hi := 698) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 698) (Lr := CFSG.KD.Fi24Tc.Pc.l698) ((nodeV_pow (R := AR) (D := SD) (lo := 697) (L := []) (j := 697) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 697 [] (SD.na.getD 697 0)) (SD.nk.getD 697 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q697_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q697_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r697))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f101

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a698_3 : Nat := CFSG.KD.Fi24Tc.KV5 0
theorem CFSG.KD.Fi24Tc.Pc.q698_3 : Nat.beq (powTop AR.mul (getV AR SD 698 [] (SD.na.getD 698 0)) (SD.nk.getD 698 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a698_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a698_1 : Nat := CFSG.KD.Fi24Tc.KV5 1
theorem CFSG.KD.Fi24Tc.Pc.q698_1 : Nat.beq (powTop AR.mul (getV AR SD 698 [] (SD.na.getD 698 0)) (SD.nk.getD 698 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a698_1) 2 CFSG.KD.Fi24Tc.Pc.a698_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v698 : Nat := CFSG.KD.Fi24Tc.KV5 2
theorem CFSG.KD.Fi24Tc.Pc.r698 : Nat.beq (powR AR.mul AR.one (getV AR SD 698 [] (SD.na.getD 698 0)) (SD.nk.getD 698 1) 1 CFSG.KD.Fi24Tc.Pc.a698_1 true) CFSG.KD.Fi24Tc.Pc.v698 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l699 : List Nat := [CFSG.KD.Fi24Tc.Pc.v698]
theorem CFSG.KD.Fi24Tc.Pc.f102 : Nat.beq (runC AR SD 698 (finC AR SD (nat_lit 102) 698 699) 0 699 CFSG.KD.Fi24Tc.Pc.l699) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk102 : chk (nat_lit 102) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 102) (lo := 698) (hi := 699) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 699) (Lr := CFSG.KD.Fi24Tc.Pc.l699) ((nodeV_pow (R := AR) (D := SD) (lo := 698) (L := []) (j := 698) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 698 [] (SD.na.getD 698 0)) (SD.nk.getD 698 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q698_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q698_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r698))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f102

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a699_3 : Nat := CFSG.KD.Fi24Tc.KV5 3
theorem CFSG.KD.Fi24Tc.Pc.q699_3 : Nat.beq (powTop AR.mul (getV AR SD 699 [] (SD.na.getD 699 0)) (SD.nk.getD 699 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a699_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a699_2 : Nat := CFSG.KD.Fi24Tc.KV5 4
theorem CFSG.KD.Fi24Tc.Pc.q699_2 : Nat.beq (powTop AR.mul (getV AR SD 699 [] (SD.na.getD 699 0)) (SD.nk.getD 699 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a699_2) 1 CFSG.KD.Fi24Tc.Pc.a699_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a699_1 : Nat := CFSG.KD.Fi24Tc.KV5 5
theorem CFSG.KD.Fi24Tc.Pc.q699_1 : Nat.beq (powTop AR.mul (getV AR SD 699 [] (SD.na.getD 699 0)) (SD.nk.getD 699 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a699_1) 1 CFSG.KD.Fi24Tc.Pc.a699_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v699 : Nat := CFSG.KD.Fi24Tc.KV5 6
theorem CFSG.KD.Fi24Tc.Pc.r699 : Nat.beq (powR AR.mul AR.one (getV AR SD 699 [] (SD.na.getD 699 0)) (SD.nk.getD 699 1) 1 CFSG.KD.Fi24Tc.Pc.a699_1 true) CFSG.KD.Fi24Tc.Pc.v699 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l700 : List Nat := [CFSG.KD.Fi24Tc.Pc.v699]
theorem CFSG.KD.Fi24Tc.Pc.f103 : Nat.beq (runC AR SD 699 (finC AR SD (nat_lit 103) 699 700) 0 700 CFSG.KD.Fi24Tc.Pc.l700) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk103 : chk (nat_lit 103) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 103) (lo := 699) (hi := 700) (m := 1) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 1) (m2 := 0) (j2 := 700) (Lr := CFSG.KD.Fi24Tc.Pc.l700) ((nodeV_pow (R := AR) (D := SD) (lo := 699) (L := []) (j := 699) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 699 [] (SD.na.getD 699 0)) (SD.nk.getD 699 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q699_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q699_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q699_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r699)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f103

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a700_3 : Nat := CFSG.KD.Fi24Tc.KV5 7
theorem CFSG.KD.Fi24Tc.Pc.q700_3 : Nat.beq (powTop AR.mul (getV AR SD 700 [] (SD.na.getD 700 0)) (SD.nk.getD 700 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a700_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a700_2 : Nat := CFSG.KD.Fi24Tc.KV5 8
theorem CFSG.KD.Fi24Tc.Pc.q700_2 : Nat.beq (powTop AR.mul (getV AR SD 700 [] (SD.na.getD 700 0)) (SD.nk.getD 700 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a700_2) 1 CFSG.KD.Fi24Tc.Pc.a700_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a700_1 : Nat := CFSG.KD.Fi24Tc.KV5 9
theorem CFSG.KD.Fi24Tc.Pc.q700_1 : Nat.beq (powTop AR.mul (getV AR SD 700 [] (SD.na.getD 700 0)) (SD.nk.getD 700 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a700_1) 1 CFSG.KD.Fi24Tc.Pc.a700_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v700 : Nat := CFSG.KD.Fi24Tc.KV5 10
theorem CFSG.KD.Fi24Tc.Pc.r700 : Nat.beq (powR AR.mul AR.one (getV AR SD 700 [] (SD.na.getD 700 0)) (SD.nk.getD 700 1) 1 CFSG.KD.Fi24Tc.Pc.a700_1 true) CFSG.KD.Fi24Tc.Pc.v700 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l701 : List Nat := [CFSG.KD.Fi24Tc.Pc.v700]
theorem CFSG.KD.Fi24Tc.Pc.f104 : Nat.beq (runC AR SD 700 (finC AR SD (nat_lit 104) 700 702) 1 701 CFSG.KD.Fi24Tc.Pc.l701) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk104 : chk (nat_lit 104) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 104) (lo := 700) (hi := 702) (m := 2) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 2) (m2 := 1) (j2 := 701) (Lr := CFSG.KD.Fi24Tc.Pc.l701) ((nodeV_pow (R := AR) (D := SD) (lo := 700) (L := []) (j := 700) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 700 [] (SD.na.getD 700 0)) (SD.nk.getD 700 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q700_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q700_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q700_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r700)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f104

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v702 : Nat := CFSG.KD.Fi24Tc.KV5 11
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v703 : Nat := CFSG.KD.Fi24Tc.KV5 12
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l704 : List Nat := [CFSG.KD.Fi24Tc.Pc.v702, CFSG.KD.Fi24Tc.Pc.v703]
theorem CFSG.KD.Fi24Tc.Pc.p702 : Nat.beq (runC AR SD 702 (ckL CFSG.KD.Fi24Tc.Pc.l704) 2 702 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v704 : Nat := CFSG.KD.Fi24Tc.KV5 13
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v705 : Nat := CFSG.KD.Fi24Tc.KV5 14
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l706 : List Nat := [CFSG.KD.Fi24Tc.Pc.v702, CFSG.KD.Fi24Tc.Pc.v703, CFSG.KD.Fi24Tc.Pc.v704, CFSG.KD.Fi24Tc.Pc.v705]
theorem CFSG.KD.Fi24Tc.Pc.p704 : Nat.beq (runC AR SD 702 (ckL CFSG.KD.Fi24Tc.Pc.l706) 2 704 CFSG.KD.Fi24Tc.Pc.l704) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v706 : Nat := CFSG.KD.Fi24Tc.KV5 15
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v707 : Nat := CFSG.KD.Fi24Tc.KV5 16
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l708 : List Nat := [CFSG.KD.Fi24Tc.Pc.v702, CFSG.KD.Fi24Tc.Pc.v703, CFSG.KD.Fi24Tc.Pc.v704, CFSG.KD.Fi24Tc.Pc.v705, CFSG.KD.Fi24Tc.Pc.v706, CFSG.KD.Fi24Tc.Pc.v707]
theorem CFSG.KD.Fi24Tc.Pc.p706 : Nat.beq (runC AR SD 702 (ckL CFSG.KD.Fi24Tc.Pc.l708) 2 706 CFSG.KD.Fi24Tc.Pc.l706) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f105 : Nat.beq (runC AR SD 702 (finC AR SD (nat_lit 105) 702 710) 2 708 CFSG.KD.Fi24Tc.Pc.l708) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk105 : chk (nat_lit 105) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 105) (lo := 702) (hi := 710) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 704) CFSG.KD.Fi24Tc.Pc.p702 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 706) CFSG.KD.Fi24Tc.Pc.p704 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 708) CFSG.KD.Fi24Tc.Pc.p706 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f105

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v710 : Nat := CFSG.KD.Fi24Tc.KV5 17
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v711 : Nat := CFSG.KD.Fi24Tc.KV5 18
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l712 : List Nat := [CFSG.KD.Fi24Tc.Pc.v710, CFSG.KD.Fi24Tc.Pc.v711]
theorem CFSG.KD.Fi24Tc.Pc.p710 : Nat.beq (runC AR SD 710 (ckL CFSG.KD.Fi24Tc.Pc.l712) 2 710 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v712 : Nat := CFSG.KD.Fi24Tc.KV5 19
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v713 : Nat := CFSG.KD.Fi24Tc.KV5 20
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l714 : List Nat := [CFSG.KD.Fi24Tc.Pc.v710, CFSG.KD.Fi24Tc.Pc.v711, CFSG.KD.Fi24Tc.Pc.v712, CFSG.KD.Fi24Tc.Pc.v713]
theorem CFSG.KD.Fi24Tc.Pc.p712 : Nat.beq (runC AR SD 710 (ckL CFSG.KD.Fi24Tc.Pc.l714) 2 712 CFSG.KD.Fi24Tc.Pc.l712) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v714 : Nat := CFSG.KD.Fi24Tc.KV5 21
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v715 : Nat := CFSG.KD.Fi24Tc.KV5 22
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l716 : List Nat := [CFSG.KD.Fi24Tc.Pc.v710, CFSG.KD.Fi24Tc.Pc.v711, CFSG.KD.Fi24Tc.Pc.v712, CFSG.KD.Fi24Tc.Pc.v713, CFSG.KD.Fi24Tc.Pc.v714, CFSG.KD.Fi24Tc.Pc.v715]
theorem CFSG.KD.Fi24Tc.Pc.p714 : Nat.beq (runC AR SD 710 (ckL CFSG.KD.Fi24Tc.Pc.l716) 2 714 CFSG.KD.Fi24Tc.Pc.l714) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f106 : Nat.beq (runC AR SD 710 (finC AR SD (nat_lit 106) 710 718) 2 716 CFSG.KD.Fi24Tc.Pc.l716) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk106 : chk (nat_lit 106) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 106) (lo := 710) (hi := 718) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 712) CFSG.KD.Fi24Tc.Pc.p710 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 714) CFSG.KD.Fi24Tc.Pc.p712 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 716) CFSG.KD.Fi24Tc.Pc.p714 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f106

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v718 : Nat := CFSG.KD.Fi24Tc.KV5 23
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v719 : Nat := CFSG.KD.Fi24Tc.KV5 24
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l720 : List Nat := [CFSG.KD.Fi24Tc.Pc.v718, CFSG.KD.Fi24Tc.Pc.v719]
theorem CFSG.KD.Fi24Tc.Pc.p718 : Nat.beq (runC AR SD 718 (ckL CFSG.KD.Fi24Tc.Pc.l720) 2 718 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v720 : Nat := CFSG.KD.Fi24Tc.KV5 25
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v721 : Nat := CFSG.KD.Fi24Tc.KV5 26
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l722 : List Nat := [CFSG.KD.Fi24Tc.Pc.v718, CFSG.KD.Fi24Tc.Pc.v719, CFSG.KD.Fi24Tc.Pc.v720, CFSG.KD.Fi24Tc.Pc.v721]
theorem CFSG.KD.Fi24Tc.Pc.p720 : Nat.beq (runC AR SD 718 (ckL CFSG.KD.Fi24Tc.Pc.l722) 2 720 CFSG.KD.Fi24Tc.Pc.l720) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v722 : Nat := CFSG.KD.Fi24Tc.KV5 27
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v723 : Nat := CFSG.KD.Fi24Tc.KV5 28
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l724 : List Nat := [CFSG.KD.Fi24Tc.Pc.v718, CFSG.KD.Fi24Tc.Pc.v719, CFSG.KD.Fi24Tc.Pc.v720, CFSG.KD.Fi24Tc.Pc.v721, CFSG.KD.Fi24Tc.Pc.v722, CFSG.KD.Fi24Tc.Pc.v723]
theorem CFSG.KD.Fi24Tc.Pc.p722 : Nat.beq (runC AR SD 718 (ckL CFSG.KD.Fi24Tc.Pc.l724) 2 722 CFSG.KD.Fi24Tc.Pc.l722) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f107 : Nat.beq (runC AR SD 718 (finC AR SD (nat_lit 107) 718 726) 2 724 CFSG.KD.Fi24Tc.Pc.l724) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk107 : chk (nat_lit 107) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 107) (lo := 718) (hi := 726) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 720) CFSG.KD.Fi24Tc.Pc.p718 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 722) CFSG.KD.Fi24Tc.Pc.p720 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 724) CFSG.KD.Fi24Tc.Pc.p722 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f107

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v726 : Nat := CFSG.KD.Fi24Tc.KV5 29
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v727 : Nat := CFSG.KD.Fi24Tc.KV5 30
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l728 : List Nat := [CFSG.KD.Fi24Tc.Pc.v726, CFSG.KD.Fi24Tc.Pc.v727]
theorem CFSG.KD.Fi24Tc.Pc.p726 : Nat.beq (runC AR SD 726 (ckL CFSG.KD.Fi24Tc.Pc.l728) 2 726 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v728 : Nat := CFSG.KD.Fi24Tc.KV5 31
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v729 : Nat := CFSG.KD.Fi24Tc.KV5 32
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l730 : List Nat := [CFSG.KD.Fi24Tc.Pc.v726, CFSG.KD.Fi24Tc.Pc.v727, CFSG.KD.Fi24Tc.Pc.v728, CFSG.KD.Fi24Tc.Pc.v729]
theorem CFSG.KD.Fi24Tc.Pc.p728 : Nat.beq (runC AR SD 726 (ckL CFSG.KD.Fi24Tc.Pc.l730) 2 728 CFSG.KD.Fi24Tc.Pc.l728) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v730 : Nat := CFSG.KD.Fi24Tc.KV5 33
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v731 : Nat := CFSG.KD.Fi24Tc.KV5 34
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l732 : List Nat := [CFSG.KD.Fi24Tc.Pc.v726, CFSG.KD.Fi24Tc.Pc.v727, CFSG.KD.Fi24Tc.Pc.v728, CFSG.KD.Fi24Tc.Pc.v729, CFSG.KD.Fi24Tc.Pc.v730, CFSG.KD.Fi24Tc.Pc.v731]
theorem CFSG.KD.Fi24Tc.Pc.p730 : Nat.beq (runC AR SD 726 (ckL CFSG.KD.Fi24Tc.Pc.l732) 2 730 CFSG.KD.Fi24Tc.Pc.l730) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f108 : Nat.beq (runC AR SD 726 (finC AR SD (nat_lit 108) 726 734) 2 732 CFSG.KD.Fi24Tc.Pc.l732) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk108 : chk (nat_lit 108) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 108) (lo := 726) (hi := 734) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 728) CFSG.KD.Fi24Tc.Pc.p726 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 730) CFSG.KD.Fi24Tc.Pc.p728 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 732) CFSG.KD.Fi24Tc.Pc.p730 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f108

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v734 : Nat := CFSG.KD.Fi24Tc.KV5 35
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v735 : Nat := CFSG.KD.Fi24Tc.KV5 36
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l736 : List Nat := [CFSG.KD.Fi24Tc.Pc.v734, CFSG.KD.Fi24Tc.Pc.v735]
theorem CFSG.KD.Fi24Tc.Pc.p734 : Nat.beq (runC AR SD 734 (ckL CFSG.KD.Fi24Tc.Pc.l736) 2 734 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v736 : Nat := CFSG.KD.Fi24Tc.KV5 37
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v737 : Nat := CFSG.KD.Fi24Tc.KV5 38
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l738 : List Nat := [CFSG.KD.Fi24Tc.Pc.v734, CFSG.KD.Fi24Tc.Pc.v735, CFSG.KD.Fi24Tc.Pc.v736, CFSG.KD.Fi24Tc.Pc.v737]
theorem CFSG.KD.Fi24Tc.Pc.p736 : Nat.beq (runC AR SD 734 (ckL CFSG.KD.Fi24Tc.Pc.l738) 2 736 CFSG.KD.Fi24Tc.Pc.l736) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v738 : Nat := CFSG.KD.Fi24Tc.KV5 39
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v739 : Nat := CFSG.KD.Fi24Tc.KV5 40
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l740 : List Nat := [CFSG.KD.Fi24Tc.Pc.v734, CFSG.KD.Fi24Tc.Pc.v735, CFSG.KD.Fi24Tc.Pc.v736, CFSG.KD.Fi24Tc.Pc.v737, CFSG.KD.Fi24Tc.Pc.v738, CFSG.KD.Fi24Tc.Pc.v739]
theorem CFSG.KD.Fi24Tc.Pc.p738 : Nat.beq (runC AR SD 734 (ckL CFSG.KD.Fi24Tc.Pc.l740) 2 738 CFSG.KD.Fi24Tc.Pc.l738) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f109 : Nat.beq (runC AR SD 734 (finC AR SD (nat_lit 109) 734 742) 2 740 CFSG.KD.Fi24Tc.Pc.l740) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk109 : chk (nat_lit 109) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 109) (lo := 734) (hi := 742) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 736) CFSG.KD.Fi24Tc.Pc.p734 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 738) CFSG.KD.Fi24Tc.Pc.p736 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 740) CFSG.KD.Fi24Tc.Pc.p738 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f109

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v742 : Nat := CFSG.KD.Fi24Tc.KV5 41
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l743 : List Nat := [CFSG.KD.Fi24Tc.Pc.v742]
theorem CFSG.KD.Fi24Tc.Pc.p742 : Nat.beq (runC AR SD 742 (ckL CFSG.KD.Fi24Tc.Pc.l743) 1 742 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a743_3 : Nat := CFSG.KD.Fi24Tc.KV5 42
theorem CFSG.KD.Fi24Tc.Pc.q743_3 : Nat.beq (powTop AR.mul (getV AR SD 742 CFSG.KD.Fi24Tc.Pc.l743 (SD.na.getD 743 0)) (SD.nk.getD 743 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a743_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a743_2 : Nat := CFSG.KD.Fi24Tc.KV5 43
theorem CFSG.KD.Fi24Tc.Pc.q743_2 : Nat.beq (powTop AR.mul (getV AR SD 742 CFSG.KD.Fi24Tc.Pc.l743 (SD.na.getD 743 0)) (SD.nk.getD 743 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a743_2) 1 CFSG.KD.Fi24Tc.Pc.a743_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a743_1 : Nat := CFSG.KD.Fi24Tc.KV5 44
theorem CFSG.KD.Fi24Tc.Pc.q743_1 : Nat.beq (powTop AR.mul (getV AR SD 742 CFSG.KD.Fi24Tc.Pc.l743 (SD.na.getD 743 0)) (SD.nk.getD 743 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a743_1) 1 CFSG.KD.Fi24Tc.Pc.a743_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v743 : Nat := CFSG.KD.Fi24Tc.KV5 45
theorem CFSG.KD.Fi24Tc.Pc.r743 : Nat.beq (powR AR.mul AR.one (getV AR SD 742 CFSG.KD.Fi24Tc.Pc.l743 (SD.na.getD 743 0)) (SD.nk.getD 743 1) 1 CFSG.KD.Fi24Tc.Pc.a743_1 true) CFSG.KD.Fi24Tc.Pc.v743 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l744 : List Nat := [CFSG.KD.Fi24Tc.Pc.v742, CFSG.KD.Fi24Tc.Pc.v743]
theorem CFSG.KD.Fi24Tc.Pc.f110 : Nat.beq (runC AR SD 742 (finC AR SD (nat_lit 110) 742 744) 0 744 CFSG.KD.Fi24Tc.Pc.l744) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk110 : chk (nat_lit 110) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 110) (lo := 742) (hi := 744) (m := 2) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 2) (m2 := 1) (j2 := 743) CFSG.KD.Fi24Tc.Pc.p742 rfl rfl).trans (runC_node (m := 1) (m2 := 0) (j2 := 744) (Lr := CFSG.KD.Fi24Tc.Pc.l744) ((nodeV_pow (R := AR) (D := SD) (lo := 742) (L := CFSG.KD.Fi24Tc.Pc.l743) (j := 743) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 742 CFSG.KD.Fi24Tc.Pc.l743 (SD.na.getD 743 0)) (SD.nk.getD 743 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q743_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q743_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q743_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r743)))))) (by quickRfl) rfl rfl rfl)))).trans CFSG.KD.Fi24Tc.Pc.f110

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v744 : Nat := CFSG.KD.Fi24Tc.KV5 46
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v745 : Nat := CFSG.KD.Fi24Tc.KV5 47
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l746 : List Nat := [CFSG.KD.Fi24Tc.Pc.v744, CFSG.KD.Fi24Tc.Pc.v745]
theorem CFSG.KD.Fi24Tc.Pc.p744 : Nat.beq (runC AR SD 744 (ckL CFSG.KD.Fi24Tc.Pc.l746) 2 744 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v746 : Nat := CFSG.KD.Fi24Tc.KV5 48
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v747 : Nat := CFSG.KD.Fi24Tc.KV5 49
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l748 : List Nat := [CFSG.KD.Fi24Tc.Pc.v744, CFSG.KD.Fi24Tc.Pc.v745, CFSG.KD.Fi24Tc.Pc.v746, CFSG.KD.Fi24Tc.Pc.v747]
theorem CFSG.KD.Fi24Tc.Pc.p746 : Nat.beq (runC AR SD 744 (ckL CFSG.KD.Fi24Tc.Pc.l748) 2 746 CFSG.KD.Fi24Tc.Pc.l746) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v748 : Nat := CFSG.KD.Fi24Tc.KV5 50
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v749 : Nat := CFSG.KD.Fi24Tc.KV5 51
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l750 : List Nat := [CFSG.KD.Fi24Tc.Pc.v744, CFSG.KD.Fi24Tc.Pc.v745, CFSG.KD.Fi24Tc.Pc.v746, CFSG.KD.Fi24Tc.Pc.v747, CFSG.KD.Fi24Tc.Pc.v748, CFSG.KD.Fi24Tc.Pc.v749]
theorem CFSG.KD.Fi24Tc.Pc.p748 : Nat.beq (runC AR SD 744 (ckL CFSG.KD.Fi24Tc.Pc.l750) 2 748 CFSG.KD.Fi24Tc.Pc.l748) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f111 : Nat.beq (runC AR SD 744 (finC AR SD (nat_lit 111) 744 752) 2 750 CFSG.KD.Fi24Tc.Pc.l750) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk111 : chk (nat_lit 111) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 111) (lo := 744) (hi := 752) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 746) CFSG.KD.Fi24Tc.Pc.p744 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 748) CFSG.KD.Fi24Tc.Pc.p746 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 750) CFSG.KD.Fi24Tc.Pc.p748 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f111

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v752 : Nat := CFSG.KD.Fi24Tc.KV5 52
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v753 : Nat := CFSG.KD.Fi24Tc.KV5 53
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l754 : List Nat := [CFSG.KD.Fi24Tc.Pc.v752, CFSG.KD.Fi24Tc.Pc.v753]
theorem CFSG.KD.Fi24Tc.Pc.p752 : Nat.beq (runC AR SD 752 (ckL CFSG.KD.Fi24Tc.Pc.l754) 2 752 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v754 : Nat := CFSG.KD.Fi24Tc.KV5 54
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v755 : Nat := CFSG.KD.Fi24Tc.KV5 55
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l756 : List Nat := [CFSG.KD.Fi24Tc.Pc.v752, CFSG.KD.Fi24Tc.Pc.v753, CFSG.KD.Fi24Tc.Pc.v754, CFSG.KD.Fi24Tc.Pc.v755]
theorem CFSG.KD.Fi24Tc.Pc.p754 : Nat.beq (runC AR SD 752 (ckL CFSG.KD.Fi24Tc.Pc.l756) 2 754 CFSG.KD.Fi24Tc.Pc.l754) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v756 : Nat := CFSG.KD.Fi24Tc.KV5 56
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v757 : Nat := CFSG.KD.Fi24Tc.KV5 57
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l758 : List Nat := [CFSG.KD.Fi24Tc.Pc.v752, CFSG.KD.Fi24Tc.Pc.v753, CFSG.KD.Fi24Tc.Pc.v754, CFSG.KD.Fi24Tc.Pc.v755, CFSG.KD.Fi24Tc.Pc.v756, CFSG.KD.Fi24Tc.Pc.v757]
theorem CFSG.KD.Fi24Tc.Pc.p756 : Nat.beq (runC AR SD 752 (ckL CFSG.KD.Fi24Tc.Pc.l758) 2 756 CFSG.KD.Fi24Tc.Pc.l756) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f112 : Nat.beq (runC AR SD 752 (finC AR SD (nat_lit 112) 752 760) 2 758 CFSG.KD.Fi24Tc.Pc.l758) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk112 : chk (nat_lit 112) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 112) (lo := 752) (hi := 760) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 754) CFSG.KD.Fi24Tc.Pc.p752 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 756) CFSG.KD.Fi24Tc.Pc.p754 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 758) CFSG.KD.Fi24Tc.Pc.p756 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f112

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v760 : Nat := CFSG.KD.Fi24Tc.KV5 58
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v761 : Nat := CFSG.KD.Fi24Tc.KV5 59
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l762 : List Nat := [CFSG.KD.Fi24Tc.Pc.v760, CFSG.KD.Fi24Tc.Pc.v761]
theorem CFSG.KD.Fi24Tc.Pc.p760 : Nat.beq (runC AR SD 760 (ckL CFSG.KD.Fi24Tc.Pc.l762) 2 760 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v762 : Nat := CFSG.KD.Fi24Tc.KV5 60
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l763 : List Nat := [CFSG.KD.Fi24Tc.Pc.v760, CFSG.KD.Fi24Tc.Pc.v761, CFSG.KD.Fi24Tc.Pc.v762]
theorem CFSG.KD.Fi24Tc.Pc.p762 : Nat.beq (runC AR SD 760 (ckL CFSG.KD.Fi24Tc.Pc.l763) 1 762 CFSG.KD.Fi24Tc.Pc.l762) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a763_2 : Nat := CFSG.KD.Fi24Tc.KV5 61
theorem CFSG.KD.Fi24Tc.Pc.q763_2 : Nat.beq (powTop AR.mul (getV AR SD 760 CFSG.KD.Fi24Tc.Pc.l763 (SD.na.getD 763 0)) (SD.nk.getD 763 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a763_2) 14 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a763_1 : Nat := CFSG.KD.Fi24Tc.KV5 62
theorem CFSG.KD.Fi24Tc.Pc.q763_1 : Nat.beq (powTop AR.mul (getV AR SD 760 CFSG.KD.Fi24Tc.Pc.l763 (SD.na.getD 763 0)) (SD.nk.getD 763 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a763_1) 1 CFSG.KD.Fi24Tc.Pc.a763_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v763 : Nat := CFSG.KD.Fi24Tc.KV5 63
theorem CFSG.KD.Fi24Tc.Pc.r763 : Nat.beq (powR AR.mul AR.one (getV AR SD 760 CFSG.KD.Fi24Tc.Pc.l763 (SD.na.getD 763 0)) (SD.nk.getD 763 1) 1 CFSG.KD.Fi24Tc.Pc.a763_1 true) CFSG.KD.Fi24Tc.Pc.v763 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l764 : List Nat := [CFSG.KD.Fi24Tc.Pc.v760, CFSG.KD.Fi24Tc.Pc.v761, CFSG.KD.Fi24Tc.Pc.v762, CFSG.KD.Fi24Tc.Pc.v763]
theorem CFSG.KD.Fi24Tc.Pc.f113 : Nat.beq (runC AR SD 760 (finC AR SD (nat_lit 113) 760 765) 1 764 CFSG.KD.Fi24Tc.Pc.l764) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk113 : chk (nat_lit 113) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 113) (lo := 760) (hi := 765) (m := 5) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 5) (m2 := 3) (j2 := 762) CFSG.KD.Fi24Tc.Pc.p760 rfl rfl).trans ((runC_seq (m := 3) (m2 := 2) (j2 := 763) CFSG.KD.Fi24Tc.Pc.p762 rfl rfl).trans (runC_node (m := 2) (m2 := 1) (j2 := 764) (Lr := CFSG.KD.Fi24Tc.Pc.l764) ((nodeV_pow (R := AR) (D := SD) (lo := 760) (L := CFSG.KD.Fi24Tc.Pc.l763) (j := 763) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 760 CFSG.KD.Fi24Tc.Pc.l763 (SD.na.getD 763 0)) (SD.nk.getD 763 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q763_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q763_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r763))))) (by quickRfl) rfl rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f113

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v765 : Nat := CFSG.KD.Fi24Tc.KV5 64
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v766 : Nat := CFSG.KD.Fi24Tc.KV5 65
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l767 : List Nat := [CFSG.KD.Fi24Tc.Pc.v765, CFSG.KD.Fi24Tc.Pc.v766]
theorem CFSG.KD.Fi24Tc.Pc.p765 : Nat.beq (runC AR SD 765 (ckL CFSG.KD.Fi24Tc.Pc.l767) 2 765 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v767 : Nat := CFSG.KD.Fi24Tc.KV5 66
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v768 : Nat := CFSG.KD.Fi24Tc.KV5 67
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l769 : List Nat := [CFSG.KD.Fi24Tc.Pc.v765, CFSG.KD.Fi24Tc.Pc.v766, CFSG.KD.Fi24Tc.Pc.v767, CFSG.KD.Fi24Tc.Pc.v768]
theorem CFSG.KD.Fi24Tc.Pc.p767 : Nat.beq (runC AR SD 765 (ckL CFSG.KD.Fi24Tc.Pc.l769) 2 767 CFSG.KD.Fi24Tc.Pc.l767) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v769 : Nat := CFSG.KD.Fi24Tc.KV5 68
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v770 : Nat := CFSG.KD.Fi24Tc.KV5 69
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l771 : List Nat := [CFSG.KD.Fi24Tc.Pc.v765, CFSG.KD.Fi24Tc.Pc.v766, CFSG.KD.Fi24Tc.Pc.v767, CFSG.KD.Fi24Tc.Pc.v768, CFSG.KD.Fi24Tc.Pc.v769, CFSG.KD.Fi24Tc.Pc.v770]
theorem CFSG.KD.Fi24Tc.Pc.p769 : Nat.beq (runC AR SD 765 (ckL CFSG.KD.Fi24Tc.Pc.l771) 2 769 CFSG.KD.Fi24Tc.Pc.l769) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f114 : Nat.beq (runC AR SD 765 (finC AR SD (nat_lit 114) 765 773) 2 771 CFSG.KD.Fi24Tc.Pc.l771) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk114 : chk (nat_lit 114) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 114) (lo := 765) (hi := 773) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 767) CFSG.KD.Fi24Tc.Pc.p765 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 769) CFSG.KD.Fi24Tc.Pc.p767 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 771) CFSG.KD.Fi24Tc.Pc.p769 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f114

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v773 : Nat := CFSG.KD.Fi24Tc.KV5 70
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v774 : Nat := CFSG.KD.Fi24Tc.KV5 71
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l775 : List Nat := [CFSG.KD.Fi24Tc.Pc.v773, CFSG.KD.Fi24Tc.Pc.v774]
theorem CFSG.KD.Fi24Tc.Pc.p773 : Nat.beq (runC AR SD 773 (ckL CFSG.KD.Fi24Tc.Pc.l775) 2 773 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v775 : Nat := CFSG.KD.Fi24Tc.KV5 72
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v776 : Nat := CFSG.KD.Fi24Tc.KV5 73
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l777 : List Nat := [CFSG.KD.Fi24Tc.Pc.v773, CFSG.KD.Fi24Tc.Pc.v774, CFSG.KD.Fi24Tc.Pc.v775, CFSG.KD.Fi24Tc.Pc.v776]
theorem CFSG.KD.Fi24Tc.Pc.p775 : Nat.beq (runC AR SD 773 (ckL CFSG.KD.Fi24Tc.Pc.l777) 2 775 CFSG.KD.Fi24Tc.Pc.l775) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v777 : Nat := CFSG.KD.Fi24Tc.KV5 74
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v778 : Nat := CFSG.KD.Fi24Tc.KV5 75
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l779 : List Nat := [CFSG.KD.Fi24Tc.Pc.v773, CFSG.KD.Fi24Tc.Pc.v774, CFSG.KD.Fi24Tc.Pc.v775, CFSG.KD.Fi24Tc.Pc.v776, CFSG.KD.Fi24Tc.Pc.v777, CFSG.KD.Fi24Tc.Pc.v778]
theorem CFSG.KD.Fi24Tc.Pc.p777 : Nat.beq (runC AR SD 773 (ckL CFSG.KD.Fi24Tc.Pc.l779) 2 777 CFSG.KD.Fi24Tc.Pc.l777) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f115 : Nat.beq (runC AR SD 773 (finC AR SD (nat_lit 115) 773 781) 2 779 CFSG.KD.Fi24Tc.Pc.l779) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk115 : chk (nat_lit 115) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 115) (lo := 773) (hi := 781) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 775) CFSG.KD.Fi24Tc.Pc.p773 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 777) CFSG.KD.Fi24Tc.Pc.p775 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 779) CFSG.KD.Fi24Tc.Pc.p777 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f115

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v781 : Nat := CFSG.KD.Fi24Tc.KV5 76
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v782 : Nat := CFSG.KD.Fi24Tc.KV5 77
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l783 : List Nat := [CFSG.KD.Fi24Tc.Pc.v781, CFSG.KD.Fi24Tc.Pc.v782]
theorem CFSG.KD.Fi24Tc.Pc.p781 : Nat.beq (runC AR SD 781 (ckL CFSG.KD.Fi24Tc.Pc.l783) 2 781 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v783 : Nat := CFSG.KD.Fi24Tc.KV5 78
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v784 : Nat := CFSG.KD.Fi24Tc.KV5 79
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l785 : List Nat := [CFSG.KD.Fi24Tc.Pc.v781, CFSG.KD.Fi24Tc.Pc.v782, CFSG.KD.Fi24Tc.Pc.v783, CFSG.KD.Fi24Tc.Pc.v784]
theorem CFSG.KD.Fi24Tc.Pc.p783 : Nat.beq (runC AR SD 781 (ckL CFSG.KD.Fi24Tc.Pc.l785) 2 783 CFSG.KD.Fi24Tc.Pc.l783) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v785 : Nat := CFSG.KD.Fi24Tc.KV5 80
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v786 : Nat := CFSG.KD.Fi24Tc.KV5 81
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l787 : List Nat := [CFSG.KD.Fi24Tc.Pc.v781, CFSG.KD.Fi24Tc.Pc.v782, CFSG.KD.Fi24Tc.Pc.v783, CFSG.KD.Fi24Tc.Pc.v784, CFSG.KD.Fi24Tc.Pc.v785, CFSG.KD.Fi24Tc.Pc.v786]
theorem CFSG.KD.Fi24Tc.Pc.p785 : Nat.beq (runC AR SD 781 (ckL CFSG.KD.Fi24Tc.Pc.l787) 2 785 CFSG.KD.Fi24Tc.Pc.l785) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f116 : Nat.beq (runC AR SD 781 (finC AR SD (nat_lit 116) 781 789) 2 787 CFSG.KD.Fi24Tc.Pc.l787) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk116 : chk (nat_lit 116) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 116) (lo := 781) (hi := 789) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 783) CFSG.KD.Fi24Tc.Pc.p781 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 785) CFSG.KD.Fi24Tc.Pc.p783 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 787) CFSG.KD.Fi24Tc.Pc.p785 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f116

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v789 : Nat := CFSG.KD.Fi24Tc.KV5 96
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v790 : Nat := CFSG.KD.Fi24Tc.KV5 97
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l791 : List Nat := [CFSG.KD.Fi24Tc.Pc.v789, CFSG.KD.Fi24Tc.Pc.v790]
theorem CFSG.KD.Fi24Tc.Pc.p789 : Nat.beq (runC AR SD 789 (ckL CFSG.KD.Fi24Tc.Pc.l791) 2 789 []) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f117 : Nat.beq (runC AR SD 789 (finC AR SD (nat_lit 117) 789 793) 2 791 CFSG.KD.Fi24Tc.Pc.l791) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk117 : chk (nat_lit 117) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 117) (lo := 789) (hi := 793) (m := 4) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_seq (m := 4) (m2 := 2) (j2 := 791) CFSG.KD.Fi24Tc.Pc.p789 rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f117

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a793_3 : Nat := CFSG.KD.Fi24Tc.KV5 82
theorem CFSG.KD.Fi24Tc.Pc.q793_3 : Nat.beq (powTop AR.mul (getV AR SD 793 [] (SD.na.getD 793 0)) (SD.nk.getD 793 1) 3 (ckP CFSG.KD.Fi24Tc.Pc.a793_3) 13 AR.one false) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a793_2 : Nat := CFSG.KD.Fi24Tc.KV5 83
theorem CFSG.KD.Fi24Tc.Pc.q793_2 : Nat.beq (powTop AR.mul (getV AR SD 793 [] (SD.na.getD 793 0)) (SD.nk.getD 793 1) 2 (ckP CFSG.KD.Fi24Tc.Pc.a793_2) 1 CFSG.KD.Fi24Tc.Pc.a793_3 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.a793_1 : Nat := CFSG.KD.Fi24Tc.KV5 84
theorem CFSG.KD.Fi24Tc.Pc.q793_1 : Nat.beq (powTop AR.mul (getV AR SD 793 [] (SD.na.getD 793 0)) (SD.nk.getD 793 1) 1 (ckP CFSG.KD.Fi24Tc.Pc.a793_1) 1 CFSG.KD.Fi24Tc.Pc.a793_2 true) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v793 : Nat := CFSG.KD.Fi24Tc.KV5 85
theorem CFSG.KD.Fi24Tc.Pc.r793 : Nat.beq (powR AR.mul AR.one (getV AR SD 793 [] (SD.na.getD 793 0)) (SD.nk.getD 793 1) 1 CFSG.KD.Fi24Tc.Pc.a793_1 true) CFSG.KD.Fi24Tc.Pc.v793 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l794 : List Nat := [CFSG.KD.Fi24Tc.Pc.v793]
theorem CFSG.KD.Fi24Tc.Pc.f118 : Nat.beq (runC AR SD 793 (finC AR SD (nat_lit 118) 793 796) 2 794 CFSG.KD.Fi24Tc.Pc.l794) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk118 : chk (nat_lit 118) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 118) (lo := 793) (hi := 796) (m := 3) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) (runC_node (m := 3) (m2 := 2) (j2 := 794) (Lr := CFSG.KD.Fi24Tc.Pc.l794) ((nodeV_pow (R := AR) (D := SD) (lo := 793) (L := []) (j := 793) rfl).trans ((powT_eq AR.mul AR.one (getV AR SD 793 [] (SD.na.getD 793 0)) (SD.nk.getD 793 1)).trans ((powR_seq (n := 16) CFSG.KD.Fi24Tc.Pc.q793_3 rfl).trans ((powR_seq (n := 3) CFSG.KD.Fi24Tc.Pc.q793_2 rfl).trans ((powR_seq (n := 2) CFSG.KD.Fi24Tc.Pc.q793_1 rfl).trans (powR_last CFSG.KD.Fi24Tc.Pc.r793)))))) (by quickRfl) rfl rfl rfl))).trans CFSG.KD.Fi24Tc.Pc.f118

@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v796 : Nat := CFSG.KD.Fi24Tc.KV5 86
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v797 : Nat := CFSG.KD.Fi24Tc.KV5 87
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l798 : List Nat := [CFSG.KD.Fi24Tc.Pc.v796, CFSG.KD.Fi24Tc.Pc.v797]
theorem CFSG.KD.Fi24Tc.Pc.p796 : Nat.beq (runC AR SD 796 (ckL CFSG.KD.Fi24Tc.Pc.l798) 2 796 []) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v798 : Nat := CFSG.KD.Fi24Tc.KV5 88
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v799 : Nat := CFSG.KD.Fi24Tc.KV5 89
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l800 : List Nat := [CFSG.KD.Fi24Tc.Pc.v796, CFSG.KD.Fi24Tc.Pc.v797, CFSG.KD.Fi24Tc.Pc.v798, CFSG.KD.Fi24Tc.Pc.v799]
theorem CFSG.KD.Fi24Tc.Pc.p798 : Nat.beq (runC AR SD 796 (ckL CFSG.KD.Fi24Tc.Pc.l800) 2 798 CFSG.KD.Fi24Tc.Pc.l798) 1 = true := by quickRfl
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v800 : Nat := CFSG.KD.Fi24Tc.KV5 90
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.v801 : Nat := CFSG.KD.Fi24Tc.KV5 91
@[expose] noncomputable def CFSG.KD.Fi24Tc.Pc.l802 : List Nat := [CFSG.KD.Fi24Tc.Pc.v796, CFSG.KD.Fi24Tc.Pc.v797, CFSG.KD.Fi24Tc.Pc.v798, CFSG.KD.Fi24Tc.Pc.v799, CFSG.KD.Fi24Tc.Pc.v800, CFSG.KD.Fi24Tc.Pc.v801]
theorem CFSG.KD.Fi24Tc.Pc.p800 : Nat.beq (runC AR SD 796 (ckL CFSG.KD.Fi24Tc.Pc.l802) 2 800 CFSG.KD.Fi24Tc.Pc.l800) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.Pc.f119 : Nat.beq (runC AR SD 796 (finC AR SD (nat_lit 119) 796 804) 2 802 CFSG.KD.Fi24Tc.Pc.l802) 1 = true := by quickRfl
theorem CFSG.KD.Fi24Tc.chk119 : chk (nat_lit 119) = true :=
  ((chunkOK_eq (R := AR) (D := SD) (c := nat_lit 119) (lo := 796) (hi := 804) (m := 8) rfl rfl rfl).trans (congrArg (fun x => Nat.beq x 1) ((runC_seq (m := 8) (m2 := 6) (j2 := 798) CFSG.KD.Fi24Tc.Pc.p796 rfl rfl).trans ((runC_seq (m := 6) (m2 := 4) (j2 := 800) CFSG.KD.Fi24Tc.Pc.p798 rfl rfl).trans (runC_seq (m := 4) (m2 := 2) (j2 := 802) CFSG.KD.Fi24Tc.Pc.p800 rfl rfl))))).trans CFSG.KD.Fi24Tc.Pc.f119

end
