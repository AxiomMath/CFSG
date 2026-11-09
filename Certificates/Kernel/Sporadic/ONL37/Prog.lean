module

public import Certificates.Kernel.Sporadic.ONL37.ProgSplit
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option maxHeartbeats 0
set_option Elab.async false

namespace CertificateChecks.KernelSpor.ONL37

theorem l37P_init : CFSG.KS.ONC.initS (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf initL initL.length = true := by
  quickRfl

#kc_regs P37R1 := packR (nat_lit 260876) (Prod.fst (runSt (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf
    (List.take (nat_lit 1) (List.drop (nat_lit 0) CFSG.RankThree.Native.ONTriple.progM)) (initL, true))) width 260876 count 9

theorem l37P_0 : CFSG.KS.ONC.runS (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf (fun s => stOK s P37R1)
    (List.take (nat_lit 1) (List.drop (nat_lit 0) CFSG.RankThree.Native.ONTriple.progM)) (initL, true) = true := by
  quickRfl

#kc_regs_keep P37R2 := packR (nat_lit 260876) (Prod.fst (runSt (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf
    (List.take (nat_lit 1) (List.drop (nat_lit 1) CFSG.RankThree.Native.ONTriple.progM)) (P37R1, true))) width 260876 count 10 keep P37R1 9

theorem l37P_1 : CFSG.KS.ONC.runS (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf (fun s => stOK s P37R2)
    (List.take (nat_lit 1) (List.drop (nat_lit 1) CFSG.RankThree.Native.ONTriple.progM)) (P37R1, true) = true := by
  quickRfl

#kc_regs_keep P37R3 := packR (nat_lit 260876) (Prod.fst (runSt (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf
    (List.take (nat_lit 21) (List.drop (nat_lit 2) CFSG.RankThree.Native.ONTriple.progM)) (P37R2, true))) width 260876 count 31 keep P37R2 10

theorem l37P_2 : CFSG.KS.ONC.runS (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf (fun s => stOK s P37R3)
    (List.take (nat_lit 21) (List.drop (nat_lit 2) CFSG.RankThree.Native.ONTriple.progM)) (P37R2, true) = true := by
  quickRfl

#kc_regs_keep P37R4 := packR (nat_lit 260876) (Prod.fst (runSt (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf
    (List.take (nat_lit 42) (List.drop (nat_lit 23) CFSG.RankThree.Native.ONTriple.progM)) (P37R3, true))) width 260876 count 73 keep P37R3 31

theorem l37P_3 : CFSG.KS.ONC.runS (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf (fun s => stOK s P37R4)
    (List.take (nat_lit 42) (List.drop (nat_lit 23) CFSG.RankThree.Native.ONTriple.progM)) (P37R3, true) = true := by
  quickRfl

#kc_regs_keep P37R5 := packR (nat_lit 260876) (Prod.fst (runSt (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf
    (List.take (nat_lit 43) (List.drop (nat_lit 65) CFSG.RankThree.Native.ONTriple.progM)) (P37R4, true))) width 260876 count 116 keep P37R4 73

theorem l37P_4 : CFSG.KS.ONC.runS (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf (fun s => stOK s P37R5)
    (List.take (nat_lit 43) (List.drop (nat_lit 65) CFSG.RankThree.Native.ONTriple.progM)) (P37R4, true) = true := by
  quickRfl

#kc_regs_keep P37R6 := packR (nat_lit 260876) (Prod.fst (runSt (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf
    (List.take (nat_lit 43) (List.drop (nat_lit 108) CFSG.RankThree.Native.ONTriple.progM)) (P37R5, true))) width 260876 count 159 keep P37R5 116

theorem l37P_5 : CFSG.KS.ONC.runS (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf (fun s => stOK s P37R6)
    (List.take (nat_lit 43) (List.drop (nat_lit 108) CFSG.RankThree.Native.ONTriple.progM)) (P37R5, true) = true := by
  quickRfl

#kc_regs_keep P37R7 := packR (nat_lit 260876) (Prod.fst (runSt (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf
    (List.take (nat_lit 17) (List.drop (nat_lit 151) CFSG.RankThree.Native.ONTriple.progM)) (P37R6, true))) width 260876 count 176 keep P37R6 159

theorem l37P_6 : CFSG.KS.ONC.runS (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf (fun s => stOK s P37R7)
    (List.take (nat_lit 17) (List.drop (nat_lit 151) CFSG.RankThree.Native.ONTriple.progM)) (P37R6, true) = true := by
  quickRfl

#kc_regs_keep P37R8 := packR (nat_lit 260876) (Prod.fst (runSt (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf
    (List.take (nat_lit 15) (List.drop (nat_lit 168) CFSG.RankThree.Native.ONTriple.progM)) (P37R7, true))) width 260876 count 191 keep P37R7 176

theorem l37P_7 : CFSG.KS.ONC.runS (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf (fun s => stOK s P37R8)
    (List.take (nat_lit 15) (List.drop (nat_lit 168) CFSG.RankThree.Native.ONTriple.progM)) (P37R7, true) = true := by
  quickRfl

theorem l37P_8 : CFSG.KS.ONC.runS (CFSG.KS.ONC.mul3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH CFSG.KS.ONC.CM CFSG.KS.ONC.RM)
    (CFSG.KS.ONC.vld3 CFSG.KS.ONC.LL CFSG.KS.ONC.HH) CFSG.KS.ONC.ONE VIf finL
    (List.drop (nat_lit 183) CFSG.RankThree.Native.ONTriple.progM) (P37R8, true) = true := by
  quickRfl

theorem l37Prog_ok : l37Prog = true :=
  sopK_of l37P_init
    (runS_seg CFSG.RankThree.Native.ONTriple.progM (nat_lit 0) (nat_lit 1) (nat_lit 1) rfl P37R1 l37P_0
      (runS_seg CFSG.RankThree.Native.ONTriple.progM (nat_lit 1) (nat_lit 1) (nat_lit 2) rfl P37R2 l37P_1
      (runS_seg CFSG.RankThree.Native.ONTriple.progM (nat_lit 2) (nat_lit 21) (nat_lit 23) rfl P37R3 l37P_2
      (runS_seg CFSG.RankThree.Native.ONTriple.progM (nat_lit 23) (nat_lit 42) (nat_lit 65) rfl P37R4 l37P_3
      (runS_seg CFSG.RankThree.Native.ONTriple.progM (nat_lit 65) (nat_lit 43) (nat_lit 108) rfl P37R5 l37P_4
      (runS_seg CFSG.RankThree.Native.ONTriple.progM (nat_lit 108) (nat_lit 43) (nat_lit 151) rfl P37R6 l37P_5
      (runS_seg CFSG.RankThree.Native.ONTriple.progM (nat_lit 151) (nat_lit 17) (nat_lit 168) rfl P37R7 l37P_6
      (runS_seg CFSG.RankThree.Native.ONTriple.progM (nat_lit 168) (nat_lit 15) (nat_lit 183) rfl P37R8 l37P_7
      l37P_8))))))))

end CertificateChecks.KernelSpor.ONL37

end
