module

public import Certificates.Data.Kernel.IdxFourLbarK
public import CFSG.GF2Type.Smith1979.IdxFourModelData

set_option maxRecDepth 100000

public section

namespace CFSG.KD.IF4L

open CFSG.KC.IF4C CFSG.KC.IF4R CFSG.KC.IF4L CFSG.GF2Type.Smith1979.IdxFour

@[expose] noncomputable def CM : List (List Nat) := [[27, 10, 7, 23, 15], [1, 2, 4, 8, 27], [1, 2, 7, 8, 19]]

@[expose] noncomputable def INN : List Nat := [3, 5, 6, 8, 11, 13, 14, 17, 18, 20, 23, 25, 26, 28, 31]

@[expose] noncomputable def OW : List (List Nat) :=
  [[], [0, 2, 0], [2, 0, 2, 0], [0, 0, 0], [0, 2, 0, 1, 0, 0], [2, 0, 1, 0, 0], [0, 1, 0, 0], [0],
    [2, 0], [0, 0], [0, 0, 0, 0], [2, 1, 0], [1, 0], [0, 0, 2, 0], [1, 0, 0]]

@[expose] noncomputable def TAU : List Nat := [3, 6, 14, 25]

@[expose] noncomputable def TT : List (List (List Nat)) :=
  [[[], [0, 2, 0], [2, 0, 2, 0], [0, 0, 0], [0, 0, 2, 0, 2, 0], [0, 2, 0, 2, 0], [0, 1, 0, 0], [0],
      [2, 0], [0, 0], [0, 0, 0, 0], [2, 1, 0], [1, 0], [0, 0, 2, 0], [1, 0, 0]],
    [[2], [], [0, 1, 0, 2, 1, 0, 1, 0], [0, 0, 0, 2, 0, 0, 0], [1, 0, 2, 1, 0], [2, 1, 0, 2, 1, 0],
      [2, 0, 2, 1, 0], [0, 2, 1, 0]],
    [[], [1, 0, 0, 0, 0, 2, 0, 0], [0, 0, 0, 0, 2, 0, 0]],
    [[1], []]]

@[expose] noncomputable def WB : List Nat := [16, 32, 1024, 2048, 3, 5, 9, 192, 320, 576]

@[expose] noncomputable def WC : List Nat := [1, 64]

@[expose] noncomputable def Bi : Nat := 43562290827944414624833729720094059201536

@[expose] noncomputable def CO : List Nat :=
  [8, 8, 40, 32, 0, 0, 0, 1, 2, 4, 8, 8, 40, 32, 0, 7, 7, 1, 21, 19, 8, 8, 40, 32, 7, 7, 0, 22, 21,
    4, 7, 7, 16, 16, 0, 7, 7, 0, 16, 16, 24, 31, 47, 48, 7, 0, 7, 22, 2, 19]

@[expose] noncomputable def VW : List Nat := [128, 256, 512, 1, 262784, 5]

theorem cf17608comm : commOK (lbarGens.map packR) = true := by decide +kernel

theorem cf17608sub : subOK (lbarGens.map packR) = true := by decide +kernel

theorem cf17608conj : conjOK (sGens.map packR) (lbarGens.map packR) CM = true := by decide +kernel

theorem cf17608orb : orbOK CM 3 OW INN = true := by decide +kernel

theorem cf17608chain : chainOK CM INN TAU TT 720 = true := by decide +kernel

theorem cf17608w :
    wOK (lbarGens.map packR) vtBasis WB WC Bi CO VW 15 960 = true := by
  decide +kernel

end CFSG.KD.IF4L

end
