module

public import Certificates.Kernel.HSA312.D
public import Certificates.Kernel.LocalQT.HS4089.L
public import Certificates.Data.Kernel.HSA312.Defs
public import Certificates.Data.Kernel.HSA312.Data
public import Certificates.Data.Kernel.HSDc.Defs
public import CFSG.Quasithin.Background.A312SporHSInputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000
set_option maxHeartbeats 0set_option Elab.async false

public noncomputable section

namespace CFSG.KD.HSA312

open CFSG.KC.HSA312 CFSG.KC.LQT.PcW CFSG.Quasithin.A312S.HS

@[expose] def I : Nat := CFSG.KD.LQT.H4089.TF 0

@[expose] def Z : Nat := TF 128

@[expose] def E (i : Nat) : Nat := TF (Nat.add 129 i)

@[expose] def Z2 : Nat := TF 133

@[expose] def Z3 : Nat := TF 134

@[expose] def E3 (i : Nat) : Nat := TF (Nat.add 135 i)

@[expose] def Es : List Nat := [E 0, E 1, E 2, E 3]

@[expose] def E3s : List Nat := [E3 0, E3 1, E3 2, E3 3]

theorem zW : Nat.beq (wordPB 1100 11 2047 CFSG.KD.LQT.H4089.L1c hsZ4Word I) Z = true := by
  quickRfl

theorem eW : ((List.range hsEWords.length).all fun i =>
    Nat.beq (wordPB 1100 11 2047 CFSG.KD.LQT.H4089.L1c (hsEWords.getD i []) I) (Es.getD i 0)) =
    true := by
  quickRfl

theorem z2P : Nat.beq (pcS 1100 11 2047 Z Z) Z2 = true := by quickRfl

theorem z3P : Nat.beq (powS 1100 11 2047 I Z 3) Z3 = true := by quickRfl

theorem e3P : ((List.range Es.length).all fun i =>
    Nat.beq (powS 1100 11 2047 I (Es.getD i 0) 3) (E3s.getD i 0)) = true := by
  quickRfl

theorem fixL : ((Z :: Es).all fun c => labsK 1100 11 2047 c (CFSG.KD.HSDc.Om 1).lbl.toList) =
    true := by
  quickRfl

theorem enumE : baseEnumC 1100 11 2047 [0, 1, 2] Es E3s J.ETs J.Epar J.Ecl = true := by quickRfl

theorem enumV : baseEnumC 1100 11 2047 [0, 1, 2] (Z :: Es) (Z3 :: E3s) J.VTs J.Vpar J.Vcl = true := by
  quickRfl

theorem sizes : (J.ETs.size == 32 && J.VTs.size == 64) = true := by quickRfl

theorem ez : (Es.all fun e => pcS 1100 11 2047 e Z2 == pcS 1100 11 2047 Z2 e) = true := by quickRfl

theorem zz : (pcS 1100 11 2047 Z2 Z2 == I) = true := by quickRfl

theorem zne : (!(Z2 == I)) = true := by quickRfl

theorem zin : J.ETs.toList.contains (appC 11 2047 Z2 (ptsC 11 2047 [0, 1, 2] Es)) = true := by
  quickRfl

theorem sq : (Es.all fun e => pcS 1100 11 2047 e e == I || pcS 1100 11 2047 e e == Z2) = true := by
  quickRfl

theorem cm : (Es.all fun e => Es.all fun f => pcS 1100 11 2047 e f == pcS 1100 11 2047 f e ||
    pcS 1100 11 2047 e f == pcS 1100 11 2047 Z2 (pcS 1100 11 2047 f e)) = true := by
  quickRfl

theorem ext : extraC 11 2047 [0, 1, 2] Es Z2 J.ETs = true := by quickRfl

theorem z4 : (powS 1100 11 2047 I Z 4 == I) = true := by quickRfl

theorem zc : (Es.all fun e => pcS 1100 11 2047 Z e == pcS 1100 11 2047 e Z) = true := by quickRfl

theorem znot : (!J.ETs.toList.contains (appC 11 2047 Z (ptsC 11 2047 [0, 1, 2] Es))) = true := by
  quickRfl

end CFSG.KD.HSA312

end
