module

public import Certificates.Kernel.Sporadic.Fi22.X2069PT
public import Certificates.Kernel.Sporadic.Fi22.G3147
public import Certificates.Kernel.Sporadic.Fi22.Cert3149K
public import Certificates.Data.Kernel.Misc.MergeTree
public import Certificates.Data.Kernel.Misc.OrbLab
meta import CFSG.Monster.B.Fischer.PinnedChainData
meta import CFSG.Monster.B.Fischer.Fi22CertInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.F3155

open CFSG.Monster.B.Fischer

meta def jOfM (j : Nat) : Nat := if j = 0 then 0 else j + 1

meta def soL : Array Nat :=
  (List.range 3510).toArray.map fun k =>
    CFSG.Monster.B.Max2.Native.hexAt fi22StabOrbitsBytes (3 * k) 3

meta def otM : Array (Array Nat) := Id.run do
  let S := (List.range 18).toArray.map fun j => fi22ChainStrong (jOfM j)
  let mut pr := Array.replicate 3510 0
  let mut gn := Array.replicate 3510 0
  let mut dp := Array.replicate 3510 0
  let mut seen := Array.replicate 3510 false
  for h in [0, 1, 11] do
    seen := seen.set! h true
    let mut queue : Array Nat := #[h]
    let mut i := 0
    for _ in [0:3510] do
      if i < queue.size then
        let p := queue[i]!
        for j in [0:18] do
          let q := (S[j]!)[p]!
          unless seen[q]! do
            seen := seen.set! q true
            pr := pr.set! q p
            gn := gn.set! q j
            dp := dp.set! q (dp[p]! + 1)
            queue := queue.push q
        i := i + 1
  let mut ps := Array.replicate 3510 0
  for k in [0:3510] do
    ps := ps.set! soL[k]! k
  return #[pr, gn, dp, ps]

meta def mergeTree (m x : Nat) : Array (Array Nat) := Id.run do
  let g0 := fi22ChainGen 0
  let g1 := fi22ChainGen 1
  let mut uf := (List.range 3510).toArray
  let mut adj : Array (List (Nat × Nat)) := Array.replicate 3510 []
  for t in [0:3509] do
    let pq : Nat × Nat := if t = 0 then (0, x) else
      let r := fi22MergeRaw m (t - 1)
      let g := if r.1 % 2 = 0 then g0 else g1
      (g[r.2.1 % 3510]!, g[r.2.2 % 3510]!)
    let mut a := pq.1
    for _ in [0:3510] do
      if uf[a]! != a then a := uf[a]!
    let mut c := pq.2
    for _ in [0:3510] do
      if uf[c]! != c then c := uf[c]!
    if a != c then
      uf := uf.set! a c
      adj := adj.set! pq.1 ((pq.2, t) :: adj[pq.1]!)
      adj := adj.set! pq.2 ((pq.1, t) :: adj[pq.2]!)
  let mut par := Array.replicate 3510 0
  let mut tim := Array.replicate 3510 0
  let mut dep := Array.replicate 3510 0
  let mut seen := (Array.replicate 3510 false).set! 0 true
  let mut queue : Array Nat := #[0]
  let mut i := 0
  for _ in [0:3510] do
    if i < queue.size then
      let p := queue[i]!
      for (q, t) in adj[p]! do
        unless seen[q]! do
          seen := seen.set! q true
          par := par.set! q p
          tim := tim.set! q t
          dep := dep.set! q (dep[p]! + 1)
          queue := queue.push q
      i := i + 1
  return #[par, tim, dep]

meta def mtM : Array (Array Nat) := mergeTree 0 1 ++ mergeTree 1 11

end CertificateChecks.KernelSpor.F3155

#kmisc_packarrs CertificateChecks.KernelSpor.F3155.OT CertificateChecks.KernelSpor.F3155.otM 12
#kmisc_packarrs CertificateChecks.KernelSpor.F3155.MT CertificateChecks.KernelSpor.F3155.mtM 12

namespace CertificateChecks.KernelSpor.F3155

open CFSG.KC.Enum CFSG.KS CertificateChecks.KernelSpor.F3149 CFSG.Monster.B.Fischer
open CFSG.KC.MTree (mtOK)
open CFSG.KC.OrbLab (olOK)

@[expose] noncomputable def at12 (T y : Nat) : Nat := pg 12 (mask 12) T y

@[expose] noncomputable def jOf (j : Nat) : Nat := nIf(Nat.beq j 0, 0, Nat.succ j)

@[expose] noncomputable def fS (j y : Nat) : Nat := at12 (Fi22ChT.F (jOf j)) y

@[expose] noncomputable def blk (s : Nat) : Nat := nIf(Nat.blt s 1, 0, nIf(Nat.blt s 2817, 1, 2))

@[expose] noncomputable def hd (t : Nat) : Nat := nIf(Nat.beq t 0, 0, nIf(Nat.beq t 1, 1, 11))

@[expose] noncomputable def mI (m k : Nat) : Nat := D (7 * (3508 * m + k)) % 2

@[expose] noncomputable def mU (m k : Nat) : Nat := D3 (7 * (3508 * m + k) + 1) % 3510

@[expose] noncomputable def mV (m k : Nat) : Nat := D3 (7 * (3508 * m + k) + 4) % 3510

@[expose] noncomputable def mergeK (m x : Nat) : Bool :=
  mtOK 3510 12 Fi22CGT.F (mI m) (mU m) (mV m) 3508 0 x (at12 (MT (3 * m))) (at12 (MT (3 * m + 1)))
    (at12 (MT (3 * m + 2))) 0

@[expose] noncomputable def orbK (H : Nat → Nat) : Bool :=
  olOK 3510 18 fS G (at12 (OT 3)) blk 3 H (at12 (OT 0)) (at12 (OT 1)) (at12 (OT 2))

theorem idxOK : ((List.range 19).filter fun j => Nat.beq (at12 (Fi22ChT.F j) 0) 0) = fi22StabIdx := by
  decide +kernel

theorem jOfOK : ∀ j < 18, fi22StabIdx.getD j 0 = jOf j := by
  decide +kernel

theorem headsOK : bAnd(Nat.beq (G 0) 0, bAnd(Nat.beq (G 1) 1, Nat.beq (G 2817) 11)) = true := by
  quickRfl

theorem orbOK : orbK hd = true := by quickRfl

theorem merge0 : mergeK 0 1 = true := by quickRfl

theorem merge1 : mergeK 1 11 = true := by quickRfl

theorem neg : bAnd(bIf(orbK (fun t => nIf(Nat.beq t 0, 0, nIf(Nat.beq t 1, 1, 12))), false, true),
    bAnd(bIf(mergeK 0 2, false, true), bIf(mergeK 1 12, false, true))) = true := by
  quickRfl

end CertificateChecks.KernelSpor.F3155

end
