module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.TabFi22Cent
public meta import Certificates.Data.TabFi22Cent
public meta import CFSG.Monster.B.Fischer.PinnedChainData

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.Fi22C17336T
  CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.hex
#kmisc_hexflat CertificateChecks.KernelSpor.Fi22C17336T
  CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.hex 3 3510 12 2

namespace CertificateChecks.KernelSpor.Fi22CentR

meta def invL (a : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate a.size 0
  for i in [0:a.size] do
    r := r.set! a[i]! i
  return r

meta def gensL : Array (Array Nat) :=
  let g1 := CFSG.Monster.B.Fischer.fi22ChainGen 1
  #[CFSG.Monster.B.Fischer.fi22ChainGen 0, g1, invL g1]

meta def treeL : Array (Array Nat) := Id.run do
  let G := gensL
  let mut par := Array.replicate 3510 0
  let mut lab := Array.replicate 3510 0
  let mut dep := Array.replicate 3510 0
  let mut seen := (Array.replicate 3510 false).set! 0 true
  let mut queue : Array Nat := #[0]
  for i in [0:3510] do
    if h : i < queue.size then
      let u := queue[i]
      for j in [0:3] do
        let v := (G[j]!)[u]!
        unless seen[v]! do
          seen := seen.set! v true
          par := par.set! v u
          lab := lab.set! v j
          dep := dep.set! v (dep[u]! + 1)
          queue := queue.push v
  return #[par, lab, dep]

meta def tAppL (G : Array (Array Nat)) (par lab : Array Nat) : Nat → Nat → Nat → Nat
  | 0, _, y => y
  | f + 1, p, y => if p == 0 then y else (G[lab[p]!]!)[tAppL G par lab f par[p]! y]!

meta def tInvL (Gi : Array (Array Nat)) (par lab : Array Nat) : Nat → Nat → Nat → Nat
  | 0, _, y => y
  | f + 1, p, y => if p == 0 then y else tInvL Gi par lab f par[p]! ((Gi[lab[p]!]!)[y]!)

meta def rowsL : Array (Array Nat) := Id.run do
  let T := treeL
  let par := T[0]!
  let lab := T[1]!
  let G := gensL
  let Gi : Array (Array Nat) := #[invL G[0]!, G[2]!, G[1]!]
  let D := CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.dArr ()
  let X := CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.xArr ()
  let dp := fun p y => tAppL G par lab 64 p D[tInvL Gi par lab 64 p y]!
  let mut w := Array.replicate 3510 0
  for p in [0:3510] do
    if !(p == 0 || p == 1 || p == X[1]!) then
      let mut found := 3510
      for q in [0:3510] do
        if found == 3510 then
          if dp p X[dp p X[q]!]! != q then
            found := q
      w := w.set! p found
  return #[par, lab, T[2]!, w]

end CertificateChecks.KernelSpor.Fi22CentR

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22CentR.R
  CertificateChecks.KernelSpor.Fi22CentR.rowsL 12
