module

public import Certificates.Data.Kernel.LocalQT.LatM
public import Certificates.Data.Kernel.LocalQT.ChainInj
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7LatticeInputs
public import CFSG.Certificates.Kernel.LocalQTListLemmas
public import CFSG.Certificates.Kernel.LocalQTPermSound
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.EachUnfold

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

public section

namespace CFSG.KD.LQT.C4058

open CFSG.KC.LQT.L CFSG.KC.LQT.S CFSG.KC.LQT.P CFSG.QuasithinUnique.Vol2Native.A312L.Seven

@[expose] def C : List Lvl :=
  [(0, [6614517792, 5574330369, 6614516738, 5574296579, 6613435396, 4499506181, 5506139142], [0, 1, 2, 3, 4, 5, 6], 7),
    (1, [0, 6614517792, 5574329408, 6614484064, 5573248128, 6579881120, 4465951936], [0, 0, 1, 2, 3, 4, 5], 6),
    (2, [0, 0, 6614517792, 5574298656, 6613438496, 4499510304, 5506144288], [0, 0, 0, 1, 2, 3, 4], 5),
    (3, [0, 0, 0, 6614517792, 5573314592, 6579980320, 4466083872], [0, 0, 0, 0, 1, 2, 3], 4),
    (4, [0, 0, 0, 0, 6614517792, 4501637152, 5509318688], [0, 0, 0, 0, 0, 1, 2], 3)]

@[expose] noncomputable def k1cF (i : Nat) : Bool := closed7 C depth ((latGens.getD i []).map code)

#kc_each_unfold k1cF 0 12 as CFSG.KD.LQT.C4058.k1c
theorem k1 : allA latGens (fun G => closed7 C depth (G.map code)) = true :=
  allA_of_getD latGens _ [] (fun i hi => match i, hi with
    | 0, _ => k1c0
    | 1, _ => k1c1
    | 2, _ => k1c2
    | 3, _ => k1c3
    | 4, _ => k1c4
    | 5, _ => k1c5
    | 6, _ => k1c6
    | 7, _ => k1c7
    | 8, _ => k1c8
    | 9, _ => k1c9
    | 10, _ => k1c10
    | 11, _ => k1c11
    | k + 12, h => absurd h (by
      have : latGens.length = 12 := rfl
      omega))
theorem k2 : sizes7 C depth (latGens.map (List.map code)) [8, 24, 24, 24, 24, 24, 72, 120, 168, 168, 360, 2520] = true := by
  quickRfl
theorem k3 : cover7 C depth (dGens.map code) (reps.map code) = true := by quickRfl
theorem k4c0 : isLat7 C depth ((dGens ++ [reps.getD 0 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c1 : isLat7 C depth ((dGens ++ [reps.getD 1 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c2 : isLat7 C depth ((dGens ++ [reps.getD 2 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c3 : isLat7 C depth ((dGens ++ [reps.getD 3 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c4 : isLat7 C depth ((dGens ++ [reps.getD 4 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c5 : isLat7 C depth ((dGens ++ [reps.getD 5 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c6 : isLat7 C depth ((dGens ++ [reps.getD 6 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c7 : isLat7 C depth ((dGens ++ [reps.getD 7 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c8 : isLat7 C depth ((dGens ++ [reps.getD 8 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c9 : isLat7 C depth ((dGens ++ [reps.getD 9 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c10 : isLat7 C depth ((dGens ++ [reps.getD 10 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c11 : isLat7 C depth ((dGens ++ [reps.getD 11 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c12 : isLat7 C depth ((dGens ++ [reps.getD 12 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c13 : isLat7 C depth ((dGens ++ [reps.getD 13 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c14 : isLat7 C depth ((dGens ++ [reps.getD 14 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c15 : isLat7 C depth ((dGens ++ [reps.getD 15 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c16 : isLat7 C depth ((dGens ++ [reps.getD 16 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c17 : isLat7 C depth ((dGens ++ [reps.getD 17 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c18 : isLat7 C depth ((dGens ++ [reps.getD 18 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c19 : isLat7 C depth ((dGens ++ [reps.getD 19 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c20 : isLat7 C depth ((dGens ++ [reps.getD 20 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c21 : isLat7 C depth ((dGens ++ [reps.getD 21 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c22 : isLat7 C depth ((dGens ++ [reps.getD 22 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c23 : isLat7 C depth ((dGens ++ [reps.getD 23 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c24 : isLat7 C depth ((dGens ++ [reps.getD 24 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c25 : isLat7 C depth ((dGens ++ [reps.getD 25 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c26 : isLat7 C depth ((dGens ++ [reps.getD 26 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c27 : isLat7 C depth ((dGens ++ [reps.getD 27 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c28 : isLat7 C depth ((dGens ++ [reps.getD 28 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c29 : isLat7 C depth ((dGens ++ [reps.getD 29 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c30 : isLat7 C depth ((dGens ++ [reps.getD 30 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c31 : isLat7 C depth ((dGens ++ [reps.getD 31 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c32 : isLat7 C depth ((dGens ++ [reps.getD 32 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c33 : isLat7 C depth ((dGens ++ [reps.getD 33 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c34 : isLat7 C depth ((dGens ++ [reps.getD 34 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c35 : isLat7 C depth ((dGens ++ [reps.getD 35 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c36 : isLat7 C depth ((dGens ++ [reps.getD 36 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c37 : isLat7 C depth ((dGens ++ [reps.getD 37 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c38 : isLat7 C depth ((dGens ++ [reps.getD 38 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c39 : isLat7 C depth ((dGens ++ [reps.getD 39 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c40 : isLat7 C depth ((dGens ++ [reps.getD 40 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c41 : isLat7 C depth ((dGens ++ [reps.getD 41 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c42 : isLat7 C depth ((dGens ++ [reps.getD 42 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c43 : isLat7 C depth ((dGens ++ [reps.getD 43 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c44 : isLat7 C depth ((dGens ++ [reps.getD 44 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c45 : isLat7 C depth ((dGens ++ [reps.getD 45 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c46 : isLat7 C depth ((dGens ++ [reps.getD 46 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c47 : isLat7 C depth ((dGens ++ [reps.getD 47 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4c48 : isLat7 C depth ((dGens ++ [reps.getD 48 1]).map code) (latGens.map (List.map code)) = true := by
  quickRfl
theorem k4 : allA reps (fun r => isLat7 C depth ((dGens ++ [r]).map code) (latGens.map (List.map code))) = true :=
  allA_of_getD reps _ 1 (fun i hi => match i, hi with
    | 0, _ => k4c0
    | 1, _ => k4c1
    | 2, _ => k4c2
    | 3, _ => k4c3
    | 4, _ => k4c4
    | 5, _ => k4c5
    | 6, _ => k4c6
    | 7, _ => k4c7
    | 8, _ => k4c8
    | 9, _ => k4c9
    | 10, _ => k4c10
    | 11, _ => k4c11
    | 12, _ => k4c12
    | 13, _ => k4c13
    | 14, _ => k4c14
    | 15, _ => k4c15
    | 16, _ => k4c16
    | 17, _ => k4c17
    | 18, _ => k4c18
    | 19, _ => k4c19
    | 20, _ => k4c20
    | 21, _ => k4c21
    | 22, _ => k4c22
    | 23, _ => k4c23
    | 24, _ => k4c24
    | 25, _ => k4c25
    | 26, _ => k4c26
    | 27, _ => k4c27
    | 28, _ => k4c28
    | 29, _ => k4c29
    | 30, _ => k4c30
    | 31, _ => k4c31
    | 32, _ => k4c32
    | 33, _ => k4c33
    | 34, _ => k4c34
    | 35, _ => k4c35
    | 36, _ => k4c36
    | 37, _ => k4c37
    | 38, _ => k4c38
    | 39, _ => k4c39
    | 40, _ => k4c40
    | 41, _ => k4c41
    | 42, _ => k4c42
    | 43, _ => k4c43
    | 44, _ => k4c44
    | 45, _ => k4c45
    | 46, _ => k4c46
    | 47, _ => k4c47
    | 48, _ => k4c48
    | k + 49, h => absurd h (by
      have : reps.length = 49 := rfl
      omega))
theorem k5c0 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 0 [] ++ G₂).map code) (latGens.map (List.map code))) = true := by quickRfl
theorem k5c1 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 1 [] ++ G₂).map code) (latGens.map (List.map code))) = true := by quickRfl
theorem k5c2 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 2 [] ++ G₂).map code) (latGens.map (List.map code))) = true := by quickRfl
theorem k5c3 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 3 [] ++ G₂).map code) (latGens.map (List.map code))) = true := by quickRfl
theorem k5c4 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 4 [] ++ G₂).map code) (latGens.map (List.map code))) = true := by quickRfl
theorem k5c5 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 5 [] ++ G₂).map code) (latGens.map (List.map code))) = true := by quickRfl
theorem k5c6 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 6 [] ++ G₂).map code) (latGens.map (List.map code))) = true := by quickRfl
theorem k5c7 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 7 [] ++ G₂).map code) (latGens.map (List.map code))) = true := by quickRfl
theorem k5c8 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 8 [] ++ G₂).map code) (latGens.map (List.map code))) = true := by quickRfl
theorem k5c9 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 9 [] ++ G₂).map code) (latGens.map (List.map code))) = true := by quickRfl
theorem k5c10 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 10 [] ++ G₂).map code) (latGens.map (List.map code))) = true := by quickRfl
theorem k5c11 : allA latGens (fun G₂ => isLat7 C depth
    ((latGens.getD 11 [] ++ G₂).map code) (latGens.map (List.map code))) = true := by quickRfl
theorem k5 : allA latGens (fun G₁ => allA latGens fun G₂ =>
    isLat7 C depth ((G₁ ++ G₂).map code) (latGens.map (List.map code))) = true :=
  allA_of_getD latGens _ [] (fun i hi => match i, hi with
    | 0, _ => k5c0
    | 1, _ => k5c1
    | 2, _ => k5c2
    | 3, _ => k5c3
    | 4, _ => k5c4
    | 5, _ => k5c5
    | 6, _ => k5c6
    | 7, _ => k5c7
    | 8, _ => k5c8
    | 9, _ => k5c9
    | 10, _ => k5c10
    | 11, _ => k5c11
    | k + 12, h => absurd h (by
      have : latGens.length = 12 := rfl
      omega))
theorem inj : chainInj 7 C = true := by quickRfl

end CFSG.KD.LQT.C4058

end
