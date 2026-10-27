module

public import Certificates.Kernel.HSA312.CY1
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0set_option Elab.async false

public noncomputable section

namespace CFSG.KD.HSA312

open CFSG.KC.Enum CFSG.KC.HSA312 CFSG.KC.LQT.PcW CFSG.Quasithin.A312S CFSG.Quasithin.A312S.HS

@[expose] def W (i : Nat) : Nat := TF (Nat.add 139 i)

@[expose] def W3 (i : Nat) : Nat := TF (Nat.add 142 i)

@[expose] def V (i : Nat) : Nat := TF (Nat.add 145 i)

@[expose] def R (i : Nat) : Nat := TF (Nat.add 148 i)

@[expose] def K (i : Nat) : Nat := TF (Nat.add 150 i)

@[expose] def Ki (i : Nat) : Nat := TF (Nat.add 154 i)

@[expose] def Ws : List Nat := [W 0, W 1, W 2]

@[expose] def W3s : List Nat := [W3 0, W3 1, W3 2]

@[expose] def Vs : List Nat := [V 0, V 1, V 2]

@[expose] def Ks : List Nat := [K 0, K 1, K 2, K 3]

@[expose] def Kis : List Nat := [Ki 0, Ki 1, Ki 2, Ki 3]

@[expose] def L2s : List Nat := (List.range 4).map CFSG.KD.LQT.H4089.L2c

theorem wW : ((List.range hsWWords.length).all fun i =>
    Nat.beq (wordPB 1100 11 2047 CFSG.KD.LQT.H4089.L2c (hsWWords.getD i []) I) (Ws.getD i 0)) =
    true := by
  quickRfl

theorem w3P : ((List.range Ws.length).all fun i =>
    Nat.beq (powS 1100 11 2047 I (Ws.getD i 0) 3) (W3s.getD i 0)) = true := by
  quickRfl

theorem vW : ((List.range hsVWords.length).all fun i =>
    Nat.beq (wordPB 1100 11 2047 CFSG.KD.LQT.H4089.L2c (hsVWords.getD i []) I) (Vs.getD i 0)) =
    true := by
  quickRfl

theorem rQ : ((List.range hsQuot2.length).all fun i => Nat.beq (qtW 1100 11 2047 I CFSG.KD.LQT.H4089.L2c
    (hsQuot2.getD i default).w (hsQuot2.getD i default).k) (R i)) = true := by
  quickRfl

theorem kG : ((List.range hsKer.length).all fun i => Nat.beq (powS 1100 11 2047 I
    (wordPB 1100 11 2047 R (hsKer.getD i default).u I) (hsKer.getD i default).k) (Ks.getD i 0)) =
    true := by
  quickRfl

theorem kI : ((List.range hsKer.length).all fun i => Nat.beq (powS 1100 11 2047 I (Ks.getD i 0)
    (2 ^ (hsKer.getD i default).e - 1)) (Kis.getD i 0)) = true := by
  quickRfl

theorem e8 : e8C 1100 11 2047 I Vs L2s hsVMats = true := by quickRfl

theorem rOrd : ((List.range hsQuot2.length).all fun i => [0, 1, 2].all fun b =>
    pg 11 2047 (powS 1100 11 2047 I (R i) (hsQuot2.getD i default).m) b == b) = true := by
  quickRfl

theorem kOrd : ((List.range hsKer.length).all fun i => [0, 1, 2].all fun b =>
    pg 11 2047 (powS 1100 11 2047 I (Ks.getD i 0) (2 ^ (hsKer.getD i default).e)) b == b) =
    true := by
  quickRfl

theorem kV : (Ks.all fun k => Vs.all fun v => pcS 1100 11 2047 k v == pcS 1100 11 2047 v k) =
    true := by
  quickRfl

theorem enumK : baseEnumC 1100 11 2047 [0, 1, 2] Ks Kis J.KTs J.Kpar J.Kcl = true := by quickRfl

theorem fixW : (Ws.all fun c => labsK 1100 11 2047 c (CFSG.KD.HSDc.Om 2).lbl.toList) = true := by
  quickRfl

theorem w4 : (Ws.all fun c => powS 1100 11 2047 I c 4 == I) = true := by quickRfl

theorem wc : (Ws.all fun c => Ws.all fun d => pcS 1100 11 2047 c d == pcS 1100 11 2047 d c) =
    true := by
  quickRfl

theorem enumW : baseEnumC 1100 11 2047 [0, 1, 2] Ws W3s J.WTs J.Wpar J.Wcl = true := by quickRfl

theorem sizes2 : (J.KTs.size == 64 && J.WTs.size == 64) = true := by quickRfl

end CFSG.KD.HSA312

end
