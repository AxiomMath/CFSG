module

public import Certificates.Kernel.Sporadic.ConjTreeGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.Fi24K.P2077
public import Certificates.Data.Kernel.Spor.Fi24F4
public meta import CFSG.Sporadic.FischerOddCore.Fi24R2Data
public meta import Certificates.Kernel.Sporadic.RawGen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi24PY

open CFSG.KS.RawGen

meta def gM : Array (Array Nat) := CFSG.Sporadic.FischerOddCore.fi24PStrong.extract 0 2

meta def s0 : Array Nat := Id.run do
  let p := gM[0]!
  let q := gM[1]!
  let lt := fun (z : Int) => if z = 1 then p else if z = -1 then inv 378 p
    else if z = 2 then q else inv 378 q
  let w : List Int := [1, 2, 2, 2, 2, 1, 1, 1, -2, -1, -2, -1]
  let x := w.foldr (fun z acc => comp 378 (lt z) acc) (Array.range 378)
  return comp 378 x (comp 378 x (comp 378 x x))

meta def search : Array (Array Nat) × Array Nat × Array (Array Nat) := Id.run do
  let gi := gM.map (inv 378)
  let mut mem : Array (Array Nat) := #[s0]
  let mut idx : Std.HashMap (Array Nat) Nat := (∅ : Std.HashMap (Array Nat) Nat).insert s0 0
  let mut tree : Array Nat := #[]
  let mut act : Array (Array Nat) := #[#[], #[]]
  let mut k := 0
  while k < mem.size do
    for l in [0:2] do
      let c := comp 378 gM[l]! (comp 378 mem[k]! gi[l]!)
      match idx[c]? with
      | some j => act := act.set! l (act[l]!.push j)
      | none =>
        idx := idx.insert c mem.size
        act := act.set! l (act[l]!.push mem.size)
        tree := tree.push (2 * k + l)
        mem := mem.push c
    k := k + 1
  return (mem, tree, act)

meta def tree : Array Nat := search.2.1

meta def treeRow : Array (Array Nat) := #[search.2.1]

meta def acts : Array (Array Nat) := search.2.2

end CertificateChecks.KernelSpor.Fi24PY

#kmisc_packarrs CertificateChecks.KernelSpor.Fi24PY.TreeP CertificateChecks.KernelSpor.Fi24PY.treeRow 13
#kmisc_packarrs CertificateChecks.KernelSpor.Fi24PY.PA CertificateChecks.KernelSpor.Fi24PY.acts 12

namespace CertificateChecks.KernelSpor.Fi24PY

@[expose] noncomputable def TF : Nat := TreeP 0

end CertificateChecks.KernelSpor.Fi24PY

#ks_conjtree CertificateChecks.KernelSpor.Fi24PY 378 9 2 64 CertificateChecks.KernelSpor.Fi24PY.gM
  CertificateChecks.KernelSpor.Fi24PY.s0 CertificateChecks.KernelSpor.Fi24PY.tree
  CertificateChecks.KernelSpor.Fi24PC.S CertificateChecks.KernelSpor.Fi24PC.SI
  CertificateChecks.KernelSpor.Fi24PY.TF 13 CertificateChecks.KernelSpor.Fi24PY.PA 12

namespace CertificateChecks.KernelSpor.Fi24PY

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.Fi24F4

theorem yRec : recOK 378 9 (mask 9) (T 0) Fi24PC.S Fi24PC.SI
    [1, 2, 2, 2, 2, 1, 1, 1, -2, -1, -2, -1, 1, 2, 2, 2, 2, 1, 1, 1, -2, -1, -2, -1,
      1, 2, 2, 2, 2, 1, 1, 1, -2, -1, -2, -1, 1, 2, 2, 2, 2, 1, 1, 1, -2, -1, -2, -1] = true := by
  quickRfl

end CertificateChecks.KernelSpor.Fi24PY

end
