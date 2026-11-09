module

public import Certificates.Kernel.HSStd.U43VbData
public import Certificates.Data.Kernel.U43CasePt
public import Certificates.Data.Kernel.Lnth

public section

namespace CertificateChecks.KernelHSStd.U43Vb

open CFSG.KC CFSG.KC.Enum CFSG.KS CFSG.KC.U43Case CertificateChecks.KernelHSStd

@[expose] noncomputable def vbIC : List (List Nat) :=
  [[6, 26, 34, 119, 127, 143], [246, 320, 326, 371, 373, 386, 426, 437], [585],
    [802, 935, 959, 964], [1001, 1041, 1054, 1157, 1178, 1179], [1287, 1292, 1351, 1395, 1419],
    [1525, 1683, 1689],
    [1710, 1724, 1775, 1776, 1787, 1819, 1826, 1828, 1833, 1843, 1873, 1915, 1916, 1939, 1940]]

@[expose] noncomputable def vbKG : List (List (Nat × List Nat)) :=
  [[(6, []), (26, []), (34, []), (119, []), (127, []), (143, []), (246, []), (320, []), (326, []),
      (371, []), (373, []), (386, [])],
    [(426, []), (437, []), (585, []), (802, []), (935, []), (959, []), (964, []), (1001, []),
      (1041, []), (1054, []), (1157, [604, 922, 998]), (1178, [])],
    [(1179, []), (1287, []), (1292, [553, 806, 1034]), (1351, [604, 922, 998]), (1395, []),
      (1419, []), (1525, []), (1683, []), (1689, []), (1710, []), (1724, []), (1775, [])],
    [(1776, []), (1787, []), (1819, []), (1826, []), (1828, []), (1833, []), (1843, []),
      (1873, []), (1915, [553, 806, 1034]), (1916, []), (1939, []), (1940, [])]]

@[expose] noncomputable def vbCG : List (List (Nat × Nat)) :=
  [[(1157, 604)], [(1157, 922)], [(1157, 998)], [(1292, 553)], [(1292, 806)], [(1292, 1034)],
    [(1351, 604)], [(1351, 922)], [(1351, 998)], [(1915, 553)], [(1915, 806)], [(1915, 1034)]]

@[expose] noncomputable def ksCand (s : Nat) : Bool :=
  ((List.range' (243 * s) 243).filter fun i => candQ 820 10 (VbP 0) (VbP 1) (VbY.T i)) ==
    lnth [] vbIC s

@[expose] noncomputable def ksK (g : Nat) : Bool :=
  (lnth [] vbKG g).all fun e =>
    ((List.range VbY.cnt).filter fun j => kQ 820 10 (VbP 0) (VbY.T e.1) (VbY.T j)) == e.2

@[expose] noncomputable def ksC (g : Nat) : Bool :=
  (lnth [] vbCG g).all fun p => cent5Q 820 10 (VbP 0) VbY.cnt VbY.T (VbY.T p.1) (VbY.T p.2) == 3

end CertificateChecks.KernelHSStd.U43Vb
