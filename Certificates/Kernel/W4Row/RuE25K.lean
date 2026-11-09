module

public import Certificates.Data.Kernel.W4Row.InvPackK
public import Certificates.Data.Kernel.SporSch.IntLines
public import Certificates.Data.Kernel.CF23L34.Slp
public import Certificates.Data.Kernel.W4Row.RuE25Ckpt
public import Certificates.Data.W4RowRuE25
public import Certificates.Kernel.SporSch.Ru.Gens
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLits

public section

set_option maxRecDepth 400000

namespace CFSG.KD.W4E.RuE25

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.W4E CFSG.KC.IntLines
  CFSG.KC.LQT.Cov CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
  CertificateChecks.KernelSporSch.RuG CFSG.KC.CF23L34

@[expose] def strsC : List (List Char) :=
  [ruE25WYStr.toList, ruE25WWStr.toList, ruE25WHStr.toList]

theorem strs : (strsC.all fun l => (intsSK (tokK l)).isSome) = true := by
  unfold strsC
  str_lits ruE25WYStr
  str_lits ruE25WWStr
  str_lits ruE25WHStr
  simp only [String.toList_ofList]
  quickRfl

@[expose] def ruE25Prog : List (ℤ × ℤ) :=
  [(-1, -2), (-3, -3), (-2, 1), (-1, -1), (2, -3), (-4, -2), (-5, -5), (-7, -7), (-6, -6), (-2, -2),
    (-4, -5), (-8, -8), (-4, -7), (-11, 8), (-10, -16), (-17, -7), (11, -18), (-19, 15), (13, -20),
    (-21, 14), (3, -22), (3, -5), (3, -4), (7, -24), (-9, 5), (2, -12), (-23, -2), (-23, 12),
    (-9, 4), (1, -3), (7, -13), (8, -27), (-34, 4), (-12, -30), (-1, -3), (-25, -9), (-13, -25),
    (5, -9), (3, -13), (41, -24), (42, -10), (43, -2), (44, 22), (45, -12), (46, 13), (47, -31),
    (48, -4), (49, -32), (50, -26), (51, -5), (52, -4), (53, -1), (54, -25), (55, 5), (56, 33),
    (57, -3), (58, -8), (59, -3), (60, 7), (61, 14), (62, 2), (63, 8), (64, 9), (65, 9), (66, -3),
    (67, 35), (68, -28), (-3, 26), (70, 27), (71, -28), (72, 29), (73, -23), (74, -28), (75, -36),
    (76, 29), (77, 3), (78, 9), (79, 15), (80, 37), (81, -24), (82, 33), (83, -28), (84, -1),
    (85, 3), (86, -36), (87, 30), (88, -23), (89, 32), (90, 7), (91, -9), (92, 14), (93, 26),
    (94, 5), (95, -2), (96, -9), (97, 31), (98, 38), (99, 39), (100, 35), (101, -2), (24, -3),
    (103, -10), (104, 26), (105, 12), (106, 12), (107, 29), (108, 29), (109, 22), (110, -25),
    (111, -24), (112, -8), (113, 38), (114, 12), (115, -7), (116, -40), (117, -37), (118, -9),
    (119, 39), (120, 27), (121, -2), (122, -40), (123, -7)]

theorem words : ((slpX ruE25Prog [] 50 69 == lineInts ruE25WYStr.toList) &&
    (slpX ruE25Prog [] 50 102 == lineInts ruE25WWStr.toList) &&
    (slpX ruE25Prog [] 50 124 == lineInts ruE25WHStr.toList) &&
    ((lineInts ruE25WYStr.toList).all fun z => decide (z.natAbs ≤ 2)) &&
    ((lineInts ruE25WWStr.toList).all fun z => decide (z.natAbs ≤ 2)) &&
    ((lineInts ruE25WHStr.toList).all fun z => decide (z.natAbs ≤ 2))) = true := by
  str_lits ruE25WYStr
  str_lits ruE25WWStr
  str_lits ruE25WHStr
  simp only [String.toList_ofList]
  quickRfl

@[expose] def ruE25P1 : List (ℤ × ℤ) := ruE25Prog.take 41

@[expose] def ruE25P2 : List (ℤ × ℤ) := (ruE25Prog.drop 41).take 41

@[expose] def ruE25P3 : List (ℤ × ℤ) := ruE25Prog.drop 82

theorem ruE25Prog_split : ruE25Prog = ruE25P1 ++ (ruE25P2 ++ ruE25P3) := by decide +kernel

theorem ruE25IdOK : idK 4060 12 (mask 12) = true := by quickRfl

theorem ruE25GensOK : gensTc 4060 12 [A0, A1] [A0I, A1I] = true := by quickRfl

theorem ruE25Pack1 : runP 4060 12 (pidn 4060 12) ruE25P1
    (fun a b c => (a == ruE25S1a && b == ruE25S1b) && Nat.beq c 43)
    [A0, A1].reverse [A0I, A1I].reverse [A0, A1].length = true := by
  quickRfl

theorem ruE25Pack2 : runP 4060 12 (pidn 4060 12) ruE25P2
    (fun a b c => (a == ruE25S2a && b == ruE25S2b) && Nat.beq c 84) ruE25S1a ruE25S1b 43 = true := by
  quickRfl

theorem ruE25Pack3 : runP 4060 12 (pidn 4060 12) ruE25P3 (fun r1 r2 len =>
    invPackK 4060 12 (pidn 4060 12) 5 (pcomp 4060 12 (mask 12) A1 A1) (pcomp 4060 12 (mask 12) A1 A1)
      (regTc (pidn 4060 12) r1 len 68) (regTc (pidn 4060 12) r2 len 68)
      (regTc (pidn 4060 12) r1 len 101) (regTc (pidn 4060 12) r2 len 101)
      (regTc (pidn 4060 12) r1 len 123) (regTc (pidn 4060 12) r2 len 123) ruE25Conj)
    ruE25S2a ruE25S2b 84 = true := by
  quickRfl

end CFSG.KD.W4E.RuE25

end
