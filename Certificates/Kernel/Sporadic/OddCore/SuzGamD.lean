module

public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Sporadic.SuzOddCore.GammaStageInputs
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore.SGamM

open CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore.Native

meta def nbrM : Array (List Nat) := gammaNbr

meta def rowsM : Array (Array Nat) := nbrM.map List.toArray

meta def gensM : Array (Array Nat) := #[certArr 0, certArr 1]

meta def treeM : Array (Array Nat) := Id.run do
  let g := gensM
  let mut rcs : Array Nat := Array.replicate 22880 0
  let mut seen : Array Bool := (Array.replicate 22880 false).set! 0 true
  let mut dep : Array Nat := Array.replicate 22880 0
  let mut q : Array Nat := #[0]
  let mut h := 0
  for _ in [0:22880] do
    if h < q.size then
      let x := q[h]!
      h := h + 1
      for k in [0:2] do
        let y := (g[k]!)[x]!
        if !seen[y]! then
          seen := seen.set! y true
          dep := dep.set! y (dep[x]! + 1)
          rcs := rcs.set! y (x + (k <<< 16) + ((dep[x]! + 1) <<< 24))
          q := q.push y
  return rcs.map fun r => #[r]

meta def step (c : Array Nat) : Array Nat := stepT 22880 nbrM (idA 22880) c

meta def base (c u e : Array Nat) : Array Nat := gammaBaseCol c u e

meta def g0 : Array Nat := Array.replicate 22880 1
meta def x0 : Array Nat := initT 22880 (idA 22880) [0]
meta def x1 : Array Nat := step x0
meta def e0 : Array Nat := step x1
meta def g1 : Array Nat := base g0 (gammaMover 0) e0
meta def p2 : Array Nat := base g1 (gammaMover 1) e0
meta def y1 : Array Nat := step p2
meta def g2 : Array Nat := step y1
meta def p3 : Array Nat := base g2 (gammaMover 2) e0
meta def g3 : Array Nat := step p3
meta def p4 : Array Nat := base g3 (gammaMover 3) e0
meta def w1 : Array Nat := step p4
meta def g4 : Array Nat := step w1

meta def salt (a : Array Nat) : Array Nat := (Array.range a.size).map fun i => a[i]! + (i <<< 32)

meta def colsM : Array (Array Nat) :=
  let cs := #[g0, x0, x1, e0, g1, p2, y1, g2, p3, g3, p4, w1, g4]
  let hs := #[x0, x1, p2, y1, p3, p4, w1].map fun c => c.map hcol
  (cs ++ hs).map salt

meta def ordM : Array (Array Nat) :=
  #[((List.range 22880).toArray.qsort fun a b => g4[a]! < g4[b]!)]

end CertificateChecks.KernelSpor.OddCore.SGamM

#kmisc_packarrs CertificateChecks.KernelSpor.SuzGamR CertificateChecks.KernelSpor.OddCore.SGamM.rowsM 16
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGamG CertificateChecks.KernelSpor.OddCore.SGamM.gensM 15
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGamT CertificateChecks.KernelSpor.OddCore.SGamM.treeM 64
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGamC CertificateChecks.KernelSpor.OddCore.SGamM.colsM 48
#kmisc_packarrs CertificateChecks.KernelSpor.SuzGamO CertificateChecks.KernelSpor.OddCore.SGamM.ordM 16

end
