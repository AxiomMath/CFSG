module

public import Certificates.Kernel.HSStd.U43Z4Data
public import Certificates.Data.Kernel.U43Case
public import Certificates.Data.Kernel.Lnth

public section

namespace CertificateChecks.KernelHSStd.U43Z4

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KC.U43Case CertificateChecks.KernelHSStd

@[expose] noncomputable def z4IC : List (List Nat) :=
  [[6, 26, 34, 119, 127, 143], [246, 320, 326, 371, 373, 386, 426, 437], [585],
    [802, 935, 959, 964], [1001, 1041, 1054, 1157, 1178, 1179], [1287, 1292, 1351, 1395, 1419],
    [1525, 1683, 1689],
    [1710, 1724, 1775, 1776, 1787, 1819, 1826, 1828, 1833, 1843, 1873, 1915, 1916, 1939, 1940]]

@[expose] noncomputable def z4KG : List (List (Nat × List Nat)) :=
  [[(6, []), (26, []), (34, []), (119, []), (127, []), (143, []), (246, []), (320, []), (326, []),
      (371, []), (373, []), (386, [])],
    [(426, []), (437, []), (585, []), (802, []), (935, []), (959, []), (964, []), (1001, []),
      (1041, []), (1054, []), (1157, [604, 922, 998]), (1178, [])],
    [(1179, []), (1287, []), (1292, [553, 806, 1034]), (1351, [604, 922, 998]), (1395, []),
      (1419, []), (1525, []), (1683, []), (1689, []), (1710, []), (1724, []), (1775, [])],
    [(1776, []), (1787, []), (1819, []), (1826, []), (1828, []), (1833, []), (1843, []),
      (1873, []), (1915, [553, 806, 1034]), (1916, []), (1939, []), (1940, [])]]

@[expose] noncomputable def z4CG : List (List (Nat × Nat)) :=
  [[(1157, 604), (1157, 922), (1157, 998)], [(1292, 553), (1292, 806), (1292, 1034)],
    [(1351, 604), (1351, 922), (1351, 998)], [(1915, 553), (1915, 806), (1915, 1034)]]

@[expose] noncomputable def ksCand (s : Nat) : Bool :=
  ((List.range' (243 * s) 243).filter fun i => candP 820 10 (Z4P 0) (Z4P 1) (Z4Y.T i)) ==
    lnth [] z4IC s

@[expose] noncomputable def ksK (g : Nat) : Bool :=
  (lnth [] z4KG g).all fun e =>
    ((List.range Z4Y.cnt).filter fun j => kP 820 10 (Z4P 0) (Z4Y.T e.1) (Z4Y.T j)) == e.2

@[expose] noncomputable def ksC (g : Nat) : Bool :=
  (lnth [] z4CG g).all fun p => cent5P 820 10 (Z4P 0) Z4Y.cnt Z4Y.T (Z4Y.T p.1) (Z4Y.T p.2) == 3

end CertificateChecks.KernelHSStd.U43Z4
