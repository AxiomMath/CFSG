module

public import Certificates.Data.Kernel.EvenBN.Thm49ETO
public import Certificates.Kernel.Misc.Tits.Text
public import Certificates.Kernel.SporSch.Tits.Common
public import Certificates.Kernel.EvenBN.Thm49EF6
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_natLines CertificateChecks.KernelT49 Tab
  "Certificates/Kernel/EvenBN/data/t49tab.txt" 81054 11528388652020273966
#kc_repo #kc_natLines CertificateChecks.KernelT49 Perm
  "Certificates/Kernel/EvenBN/data/t49perm.txt" 69754 13487810814556874947
#kc_repo #kc_natList CertificateChecks.KernelT49 KARows
  "Certificates/Kernel/EvenBN/data/t49ka.txt" 99824 2875681260930346346

public section

namespace CertificateChecks.KernelT49

open CFSG.KC.Enum CFSG.KS CFSG.KD.T49

@[expose] noncomputable def w43 : TOW where
  F := w42.F
  FI := w42.FI
  D := w42.D
  DI := w42.DI
  Z := w42.Z
  ew := w42.ew
  e1w := w42.e1w
  e1iw := w42.e1iw
  yp := 6
  r2 := 1
  fz := w42.fz
  lb := [0, 2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
  lw := [[], [], [1], [1, 2], [-1, -2], [-2], [], [-2, 1], [-2, -2, 1, 2], [-2, -2], [-2, 1, 1, -2],
    [1], [2, 2], [-1, 2], [1, 1], [-2, -1, 2, 2, -1], [1, 2], [2], [2, 2, 1, -2, 1], [2, 2, 1, -2],
    [-1, -2, -1], [1, 1, 1], [-1, -2, -1, -1], [-2], [2, 1], [1, 1, 1, 1], [1, 2, 1, 1], [1, 2, -1],
    [2, -1, 2, -1], [-1, -1], [-1, -1, -1], [-1, -2, 1], [-1, -2], [-2, 1, 1], [2, 1, 2, 2],
    [2, 2, -1], [2, 1, -2], [2, 1, -2, -1, -1], [-2, -2], [2, -1, -1, 2], [1, 2, 1, 1, 1, 1],
    [1, 2, 2, 1], [-2, 1, 1, 1], [-2, 1], [-1, 2, -1], [-2, -2, -1, -2], [2, 2, -1, -1],
    [-1, -2, 1, 1], [-2, 1, 1, 1, 1], [1, 2, 2], [2, 1, 2, 1, 1], [-1], [2, 2, 1], [1, 1, 2],
    [-1, 2], [2, -1, -2], [-2, -2, -1], [2], [1, 2, -1, -1], [2, 1, -2, 1], [-1, 2, 1],
    [1, -2, -1, -1], [1, -2], [1, -2, 1, 1, 1, 1], [-2, 1, 2], [-2, -2, -2, -1], [-2, -1, -1],
    [-2, -1], [1, -2, 1], [-1, -1, 2, 2, 1], [2, 2, 2, 1], [2, 1, 1], [2, 2, 1, 1, 1],
    [1, 1, 2, 1, 1], [1, -2, 1, 1], [-2, -2, -1, -1], [-2, -1, -2], [-1, 2, 2, -1],
    [2, -1, -1, -1], [-1, 2, 2, 1], [-1, -1, 2], [1, 1, -2], [-2, -1, -1, 2], [2, -1], [2, 1],
    [-2, -1, -2, -1, -1], [2, 1, 1, 1], [2, 1, 1, 1, 1], [-1, -1, -2, 1], [2, -1, -1],
    [-2, 1, 2, -1, -1]]
  s1 := 24
  s2 := 12
  igs := 15611314304
  steps := [50067, 66445, 35374, 68129, 40216, 56620, 68000, 34471, 50867, 71490, 37055, 53438,
    52303, 38486, 36933, 53324, 54203, 39317, 72098, 41280, 57675, 57264, 73643, 40732, 42918,
    75726, 60189, 76629, 58011, 74428, 42543, 75345, 40403, 73128, 51910, 68235, 37192, 53581,
    57367, 73796, 42421, 75190, 38983, 71711, 38356, 52793, 69136, 54081, 70455, 59185, 69293,
    43698, 36285, 69007, 40537, 71582, 43227, 59600, 59817, 76227, 42661, 68492, 41559, 55992,
    72355, 58313, 59946, 72906, 56228, 39128, 38545, 70810, 41434, 53970, 74932, 70166, 67721]
  psteps := [148354, 363011, 280196, 594053, 478214, 628232, 742282, 925582, 1072402, 1419161]
  MT := Tab.n0
  PT := Tab.n1
  a := 4
  b := 20
  ABT := Tab.n2
  tree := Tab.n3
  T := Tab.n4
  Y := Tab.n5
  RK := Tab.n6
  KA := KARows
  b1 := 45
  mc1 := 19
  t0 := 1
  t1 := 390
  cl0 := [1, 96, 106, 161]
  cl1 := [362, 371, 390, 399]

@[expose] noncomputable def p43 : MPerms where
  u1 := Perm.n0
  u2 := Perm.n1
  u1i := Perm.n2
  u2i := Perm.n3
  zp := Perm.n4
  l1 := Perm.n5

@[expose] noncomputable def q43 : KPerms where
  h1 := Perm.n6
  h2 := Perm.n7
  la := Perm.n8
  lbb := Perm.n9
  y0 := Perm.n10
  y0i := Perm.n11
  zp := Perm.n4

end CertificateChecks.KernelT49

end
