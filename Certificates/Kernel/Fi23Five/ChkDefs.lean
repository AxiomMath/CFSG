module

public import Certificates.Data.Kernel.Fi23Five.Defs
public import Certificates.Kernel.Fi23K.Tabs
public import Certificates.Kernel.Fi23Five.Tabs

public section

namespace CFSG.KD.Fi23Five

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KC.Fi23Five CFSG.KD.Fi23K

@[expose] def eW : List Nat := [40, 40, 39, 40, 40, 39, 40, 39, 40, 39, 40, 39, 40, 39, 40, 39]

@[expose] def path : List Nat := [777, 11568, 8258, 17218]

@[expose] def fW : List Nat := [17346, 8386, 11696, 905]

@[expose] def lE : List Nat := [777, 5884, 8258, 8416, 11568, 13556, 13878, 16982, 17218, 19080,
  22376, 22697, 24612, 25209, 25263, 26283, 28419, 28722, 30308, 30317, 30717]
@[expose] def lF : List Nat := [221, 465, 1462, 3765, 5641, 6581, 7404, 12276, 13116, 13434,
  13862, 18009, 21802, 21809, 24576, 25380, 26588, 27198, 27270, 27920, 30317]
@[expose] def lEF : List Nat := [4201, 10339, 11074, 11520, 11764, 11849, 12239, 15885, 16301,
  17062, 18375, 18379, 18575, 21346, 24294, 25959, 26148, 29912, 30317, 30732, 31079]
@[expose] def lEF2 : List Nat := [1542, 2326, 5215, 5216, 6649, 7103, 8465, 12945, 15182, 16027,
  19260, 19796, 21512, 23817, 24864, 25983, 26143, 27302, 28557, 28765, 30317]
@[expose] def lEF3 : List Nat := [509, 1041, 2268, 3395, 3727, 3999, 6094, 6518, 6904, 7363,
  10040, 11338, 11351, 14957, 15424, 15441, 16204, 22959, 25418, 27155, 30317]
@[expose] def lEF4 : List Nat := [2085, 3481, 3941, 6370, 7078, 7561, 7675, 7743, 8606, 10917,
  11880, 14112, 15834, 18287, 18457, 18936, 19842, 25443, 26572, 28101, 30317]

@[expose] noncomputable def eReg (lo c : Nat) : Bool := regSl H G 0 eW lo c
@[expose] noncomputable def fReg (lo c : Nat) : Bool := regSl H G 1 fW lo c

@[expose] noncomputable def fixE : Bool := fixK H [0] lE
@[expose] noncomputable def fixF : Bool := fixK H [1] lF
@[expose] noncomputable def fixEF : Bool := fixK H [0, 1] lEF
@[expose] noncomputable def fixEF2 : Bool := fixK H [0, 1, 1] lEF2
@[expose] noncomputable def fixEF3 : Bool := fixK H [0, 1, 1, 1] lEF3
@[expose] noncomputable def fixEF4 : Bool := fixK H [0, 1, 1, 1, 1] lEF4

@[expose] noncomputable def grE : Bool := graphK (cmK G) lE
@[expose] noncomputable def grF : Bool := graphK (cmK G) lF
@[expose] noncomputable def grEF : Bool := graphK (cmK G) lEF
@[expose] noncomputable def grEF2 : Bool := graphK (cmK G) lEF2
@[expose] noncomputable def grEF3 : Bool := graphK (cmK G) lEF3
@[expose] noncomputable def grEF4 : Bool := graphK (cmK G) lEF4

@[expose] noncomputable def pathOK : Bool := pathK (cmK G) lE == path

@[expose] noncomputable def smallK : Bool :=
  eqB G (powW 5 eW) [] && eqB G (powW 5 fW) [] && eqB G (eW ++ fW) (fW ++ eW) &&
    !eqB G eW [] && [0, 1, 2, 3, 4].all fun k => !eqB G fW (powW k eW)

end CFSG.KD.Fi23Five

end
