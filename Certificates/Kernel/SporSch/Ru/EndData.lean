module

public import Certificates.Kernel.SporSch.GenPerms
public import Certificates.Kernel.Sporadic.RawGenSplit
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuEndTests
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicRuEndTests
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Monster.Code.Weights
public import CFSG.Sporadic.Schreier.RuWitArrays
meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
meta import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
meta import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
meta import CFSG.Monster.Code.Weights
meta import CFSG.Sporadic.Schreier.RuWitArrays

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuEnd

open CFSG.ComponentClassification.RankTwoSporadic.Ru CFSG.Sporadic.RuSchreier
  CFSG.Monster.B.Co2.Native

@[expose] def noDerivs : List (List Int) := []

meta def ruEndTWords : List (List Nat) :=
  [[0, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1],
   [1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0],
   [0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1]]

meta def bM : Array Nat := ruEndB0

meta def biM : Array Nat := ruInv ruEndB0

meta def xM : Array (Array Nat) := ruEndLeaves

meta def xiM : Array (Array Nat) := ruEndLeaves.map ruInv

meta def commM (x y : Array Nat) : Array Nat :=
  compA 4060 (compA 4060 (compA 4060 x y) (ruInv x)) (ruInv y)

meta def yM : Array (Array Nat) :=
  let l := (Array.range 4).map fun i => commM ruEndLeaves[2 * i]! ruEndLeaves[2 * i + 1]!
  l ++ #[commM l[0]! l[1]!, commM l[2]! l[3]!]

meta def yiM : Array (Array Nat) := yM.map ruInv

meta def riM : Array Nat := ruInv ruE0[1]!

meta def labM : Array Nat := Id.run do
  let mut lab : Array Nat := Array.replicate 4060 4060
  let mut k := 0
  for p in [0:4060] do
    if lab[p]! == 4060 then
      lab := lab.set! p k
      let mut q : Array Nat := #[p]
      for h in [0:4060] do
        if h < q.size then
          for g in ruEndN0 do
            let y := g[q[h]!]!
            if lab[y]! == 4060 then
              lab := lab.set! y k
              q := q.push y
      k := k + 1
  return lab

meta def repM : Array Nat := Id.run do
  let mut r : Array Nat := #[]
  for p in [0:4060] do
    if labM[p]! == r.size then
      r := r.push p
  return r

meta def wordN (w : List Nat) : Array Nat :=
  w.foldl (fun acc i => compA 4060 ruEndN0[i]! acc) (idA 4060)

meta def sM : Array (Array Nat) := #[ruA0A, ruE0[1]!] ++ (ruEndTWords.map wordN).toArray

meta def baseM : Array Nat := #[0]

end CertificateChecks.KernelSporSch.RuEnd

#ks_perm CertificateChecks.KernelSporSch.RuEnd.B 12 CertificateChecks.KernelSporSch.RuEnd.bM
#ks_perm CertificateChecks.KernelSporSch.RuEnd.BI 12 CertificateChecks.KernelSporSch.RuEnd.biM
#ks_perm CertificateChecks.KernelSporSch.RuEnd.RI 12 CertificateChecks.KernelSporSch.RuEnd.riM
#ks_perm CertificateChecks.KernelSporSch.RuEnd.LAB 12 CertificateChecks.KernelSporSch.RuEnd.labM
#ks_perm CertificateChecks.KernelSporSch.RuEnd.REP 12 CertificateChecks.KernelSporSch.RuEnd.repM
#kss_perms CertificateChecks.KernelSporSch.RuEnd.X 12 CertificateChecks.KernelSporSch.RuEnd.xM
#kss_perms CertificateChecks.KernelSporSch.RuEnd.XI 12 CertificateChecks.KernelSporSch.RuEnd.xiM
#kss_perms CertificateChecks.KernelSporSch.RuEnd.Y 12 CertificateChecks.KernelSporSch.RuEnd.yM
#kss_perms CertificateChecks.KernelSporSch.RuEnd.YI 12 CertificateChecks.KernelSporSch.RuEnd.yiM

#ks_rawchain_sl2_data CertificateChecks.KernelSporSch.RuES 4060 12 4 64
  CertificateChecks.KernelSporSch.RuEnd.sM CertificateChecks.KernelSporSch.RuEnd.baseM 5
  CertificateChecks.KernelSporSch.RuEnd.noDerivs

end
