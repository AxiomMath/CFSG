module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.Sporadic.SuzRecog.LevelTwoCoverCheck
meta import CFSG.Sporadic.SuzRecog.LevelTwoCoverCheck
public import Mathlib
meta import Mathlib

public section

namespace CertificateChecks.KernelSpor.L2CPins

open CFSG.Sporadic.SuzRecog.LevelTwoCover

meta def rounds : Array Nat × Array Nat := Id.run do
  let unset := 255
  let mut rk : Array Nat := Array.replicate (8991 * 36) unset
  let mut apx : Array Nat := Array.replicate (8991 * 36) 0
  let tids := treeEidsOf nbrC treeParC
  for z in [1:8991] do
    rk := rk.set! tids[z]! 0
  let cs := cellsC.1
  let ids := cellsC.2
  let mut r := 0
  let mut changed := true
  for _ in [0:15] do
    if changed then
      r := r + 1
      changed := false
      let mut new : Array (Nat × Nat) := #[]
      for c in [0:cs.size] do
        let (e₁, e₂, e₃) := ids[c]!
        let (a, b, v) := cs[c]!
        let u₁ := rk[e₁]! == unset
        let u₂ := rk[e₂]! == unset
        let u₃ := rk[e₃]! == unset
        if u₁ && !u₂ && !u₃ then new := new.push (e₁, v)
        else if !u₁ && u₂ && !u₃ then new := new.push (e₂, b)
        else if !u₁ && !u₂ && u₃ then new := new.push (e₃, a)
      for (e, z) in new do
        if rk[e]! == unset then
          rk := rk.set! e r
          apx := apx.set! e z
          changed := true
  return (rk, apx)

meta def posC (x y : Nat) : Nat := posOf nbrC x y

meta def recs (u : Nat) : Array Nat :=
  (nbrC[u]!).map fun y =>
    let e := eidOf nbrC u y
    let r := rounds.1[e]!
    if r == 0 then 0 else
      let z := rounds.2[e]!
      let b := if z % 2997 < 2835 then posC z y else posC y z
      r + 16 * posC u z + 1024 * b

meta def rPin : Array (Array Nat) := (Array.range 8991).map recs

meta def tPin : Array (Array Nat) := #[treeParC, treeDepC]

end CertificateChecks.KernelSpor.L2CPins

#kmisc_packarrs CertificateChecks.KernelSpor.L2CT CertificateChecks.KernelSpor.L2CPins.tPin 14
#kmisc_packarrs CertificateChecks.KernelSpor.L2CR CertificateChecks.KernelSpor.L2CPins.rPin 16

end
