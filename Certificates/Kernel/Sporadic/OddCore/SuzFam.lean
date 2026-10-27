module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Kernel.Sporadic.OddCore.TBfsCmd
public import CFSG.Sporadic.SuzOddCore.FamilyCheckInputs
meta import CFSG.Sporadic.SuzOddCore.FamilyCheckInputs
import CFSG.Sporadic.SuzOddCore.Arrays

public section

set_option maxRecDepth 400000

#ks_chars CertificateChecks.KernelSpor.SuzSeedT CFSG.Sporadic.SuzOddCore.familySeedText

#kmisc_hexflat CertificateChecks.KernelSpor.SuzSeedT CFSG.Sporadic.SuzOddCore.familySeedText
  4 2080 15 1

namespace CertificateChecks.KernelSpor.SuzFamD

open CFSG.Sporadic.SuzOddCore

meta def famM : Array (Array Nat) := suzFam.map (·.toArray)

meta def piM : Array (Array Nat) := Id.run do
  let F := famM
  let gs := #[certArr 0, certArr 1]
  let bs := #[b0Arr, b1Arr]
  let mut out : Array (Array Nat) := #[]
  for d in [0:1782] do
    for k in [0:2] do
      let L := F[(bs[k]!)[d]!]!
      let mut pos : Array Nat := Array.replicate 22880 0
      for i in [0:L.size] do
        pos := pos.set! L[i]! i
      let g := gs[k]!
      out := out.push ((F[d]!).map fun x => pos[g[x]!]!)
  return out

meta def difM : Array (Array Nat) :=
  let F := famM
  (List.range 1782).toArray.map fun d =>
    #[((List.range 2080).find? fun j => (F[d]!)[j]! != (F[0]!)[j]!).getD 0]

meta def treeM : Array (Array Nat) × Array (Array Nat) := Id.run do
  let bs := #[b0Arr, b1Arr]
  let mut seen : Array Bool := (Array.replicate 1782 false).set! 0 true
  let mut tp : Array Nat := Array.replicate 1782 0
  let mut rk : Array Nat := Array.replicate 1782 0
  let mut queue : Array Nat := #[0]
  let mut head := 0
  for _ in [0:1782] do
    if head < queue.size then
      let d := queue[head]!
      head := head + 1
      for k in [0:2] do
        let e := (bs[k]!)[d]!
        if !seen[e]! then
          seen := seen.set! e true
          tp := tp.set! e (2 * d + k)
          rk := rk.set! e queue.size
          queue := queue.push e
  return (tp.map fun x => #[x], rk.map fun x => #[x])

meta def tpM : Array (Array Nat) := treeM.1
meta def rkM : Array (Array Nat) := treeM.2

meta def smallLettersM : Array CFSG.Sporadic.Th.Native.Table := smallLetters
meta def smallLvM : Array Nat := #[0, 1, 2, 3]

end CertificateChecks.KernelSpor.SuzFamD

#kmisc_packarrs CertificateChecks.KernelSpor.SuzFamD.FAM CertificateChecks.KernelSpor.SuzFamD.famM 15
#kmisc_packarrs CertificateChecks.KernelSpor.SuzFamD.PI CertificateChecks.KernelSpor.SuzFamD.piM 12
#kmisc_packarrs CertificateChecks.KernelSpor.SuzFamD.DIF CertificateChecks.KernelSpor.SuzFamD.difM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzFamD.TP CertificateChecks.KernelSpor.SuzFamD.tpM 32
#kmisc_packarrs CertificateChecks.KernelSpor.SuzFamD.RK CertificateChecks.KernelSpor.SuzFamD.rkM 32
#ktbfs CertificateChecks.KernelSpor.SuzFamD.ST 1782 0 CertificateChecks.KernelSpor.SuzFamD.smallLettersM
  CertificateChecks.KernelSpor.SuzFamD.smallLvM

end
