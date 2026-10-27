
module

public import Certificates.Kernel.Sporadic.ON.GenTab
public import Certificates.Kernel.Sporadic.ON.GenLv
public meta import CFSG.Sporadic.Schreier.ONCheckLocalBase
public meta import CFSG.Sporadic.Schreier.ONCheckAuxInputs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON4

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native

meta def closureM (gs : Array (Array Nat)) (base : Array Nat) : Array Nat := Id.run do
  let mut seen : Array Bool := Array.replicate 245520 false
  let mut q : Array Nat := #[]
  for b in base do
    if !seen[b]! then
      seen := seen.set! b true
      q := q.push b
  let mut h := 0
  for _ in [0:245520] do
    if h < q.size then
      let x := q[h]!
      h := h + 1
      for g in gs do
        let y := g[x]!
        if !seen[y]! then
          seen := seen.set! y true
          q := q.push y
  return q

meta def posM (X : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 245520 X.size
  for i in [0:X.size] do
    r := r.set! X[i]! i
  return r

meta def idxM (S : Array (Array Nat)) (X : Array Nat) : Array Nat := Id.run do
  let P := posM X
  let mut r : Array Nat := #[]
  for t in S do
    for x in X do
      r := r.push P[t[x]!]!
  return r

meta def mcS : Array (Array Nat) :=
  extendStrong nPts (commGens nPts (wordArrs Data.MWords) Data.MCommutatorSpecs)
    Data.McommChain.strongWords

meta def lcS : Array (Array Nat) :=
  extendStrong nPts (commGens nPts (wordArrs Data.LWords) Data.LCommutatorSpecs)
    Data.LcommChain.strongWords

meta def jS : Array (Array Nat) := extendStrong nPts jointArrs Data.jointChain.strongWords

meta def xT : Array Nat := closureM (wordArrs Data.TWords) Data.TChain.base
meta def xM : Array Nat := closureM (wordArrs Data.MWords) Data.MChain.base
meta def pT : Array Nat := posM xT
meta def pM : Array Nat := posM xM
meta def iT : Array Nat := idxM TStrong xT
meta def iTI : Array Nat := idxM (pinvs nPts TStrong) xT
meta def iM : Array Nat := idxM MStrong xM
meta def iMI : Array Nat := idxM (pinvs nPts MStrong) xM
meta def iL : Array Nat := idxM LStrong xM
meta def iLI : Array Nat := idxM (pinvs nPts LStrong) xM
meta def iMc : Array Nat := idxM mcS xM
meta def iMcI : Array Nat := idxM (pinvs nPts mcS) xM
meta def iLc : Array Nat := idxM lcS xM
meta def iLcI : Array Nat := idxM (pinvs nPts lcS) xM
meta def baseM : Array Nat := Data.TChain.base

meta def treeM (root : Nat) (st : Array (Array Nat)) (cheap : Array Nat) :
    Array Nat × Array Nat × Array Nat := Id.run do
  let n := 245520
  let other := (Array.range st.size).filter fun l => !cheap.contains l
  let mut pos : Array Nat := (Array.replicate n n).set! root 0
  let mut pts : Array Nat := #[root]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut h := 0
  let mut d := 0
  for _ in [0:2 * n + 2] do
    if h < pts.size then
      let x := pts[h]!
      for l in cheap do
        let y := st[l]![x]!
        if pos[y]! == n then
          pos := pos.set! y pts.size
          pts := pts.push y
          par := par.push h
          lab := lab.push l
      h := h + 1
    else if d < pts.size then
      let x := pts[d]!
      for l in other do
        let y := st[l]![x]!
        if pos[y]! == n then
          pos := pos.set! y pts.size
          pts := pts.push y
          par := par.push d
          lab := lab.push l
      d := d + 1
  return (pts, par, lab)

meta def jSteps (idx : Array Nat) : Array (Array Nat) :=
  idx.map (fun j => jS[j]!) ++ idx.map (fun j => pinvCand nPts jS[j]!)

meta def jt0 : Array Nat × Array Nat × Array Nat :=
  treeM 0 (jSteps #[0, 1, 2, 3, 4, 5, 6, 7, 8]) #[0, 1, 2, 3, 4, 5, 9, 10, 11, 12, 13, 14]

meta def jt1 : Array Nat × Array Nat × Array Nat :=
  treeM 227759 (jSteps #[0, 1, 6, 7, 8]) #[0, 1, 2, 5, 6, 7]

meta def jt2 : Array Nat × Array Nat × Array Nat := treeM 100817 (jSteps #[7, 8]) #[]

meta def jP0 : Array Nat := jt0.1
meta def jR0 : Array Nat := jt0.2.1
meta def jL0 : Array Nat := jt0.2.2
meta def jQ0 : Array Nat := posM jt0.1
meta def jP1 : Array Nat := jt1.1
meta def jR1 : Array Nat := jt1.2.1
meta def jL1 : Array Nat := jt1.2.2
meta def jQ1 : Array Nat := posM jt1.1
meta def jP2 : Array Nat := jt2.1
meta def jR2 : Array Nat := jt2.2.1
meta def jL2 : Array Nat := jt2.2.2
meta def jQ2 : Array Nat := posM jt2.1

end CertificateChecks.KernelSpor.ON4

#kon_table CertificateChecks.KernelSpor.ON4X.XT CertificateChecks.KernelSpor.ON4.xT
#kon_table CertificateChecks.KernelSpor.ON4X.XM CertificateChecks.KernelSpor.ON4.xM
#kon_table CertificateChecks.KernelSpor.ON4X.PT CertificateChecks.KernelSpor.ON4.pT
#kon_table CertificateChecks.KernelSpor.ON4X.PM CertificateChecks.KernelSpor.ON4.pM
#kon_table CertificateChecks.KernelSpor.ON4X.T CertificateChecks.KernelSpor.ON4.iT
#kon_table CertificateChecks.KernelSpor.ON4X.TI CertificateChecks.KernelSpor.ON4.iTI
#kon_table CertificateChecks.KernelSpor.ON4X.M CertificateChecks.KernelSpor.ON4.iM
#kon_table CertificateChecks.KernelSpor.ON4X.MI CertificateChecks.KernelSpor.ON4.iMI
#kon_table CertificateChecks.KernelSpor.ON4X.L CertificateChecks.KernelSpor.ON4.iL
#kon_table CertificateChecks.KernelSpor.ON4X.LI CertificateChecks.KernelSpor.ON4.iLI
#kon_table CertificateChecks.KernelSpor.ON4X.Mc CertificateChecks.KernelSpor.ON4.iMc
#kon_table CertificateChecks.KernelSpor.ON4X.McI CertificateChecks.KernelSpor.ON4.iMcI
#kon_table CertificateChecks.KernelSpor.ON4X.Lc CertificateChecks.KernelSpor.ON4.iLc
#kon_table CertificateChecks.KernelSpor.ON4X.LcI CertificateChecks.KernelSpor.ON4.iLcI
#kon_table CertificateChecks.KernelSpor.ON4J.P0 CertificateChecks.KernelSpor.ON4.jP0
#kon_table CertificateChecks.KernelSpor.ON4J.R0 CertificateChecks.KernelSpor.ON4.jR0
#kon_table CertificateChecks.KernelSpor.ON4J.L0 CertificateChecks.KernelSpor.ON4.jL0
#kon_table CertificateChecks.KernelSpor.ON4J.Q0 CertificateChecks.KernelSpor.ON4.jQ0
#kon_table CertificateChecks.KernelSpor.ON4J.P1 CertificateChecks.KernelSpor.ON4.jP1
#kon_table CertificateChecks.KernelSpor.ON4J.R1 CertificateChecks.KernelSpor.ON4.jR1
#kon_table CertificateChecks.KernelSpor.ON4J.L1 CertificateChecks.KernelSpor.ON4.jL1
#kon_table CertificateChecks.KernelSpor.ON4J.Q1 CertificateChecks.KernelSpor.ON4.jQ1
#kon_table CertificateChecks.KernelSpor.ON4J.P2 CertificateChecks.KernelSpor.ON4.jP2
#kon_table CertificateChecks.KernelSpor.ON4J.R2 CertificateChecks.KernelSpor.ON4.jR2
#kon_table CertificateChecks.KernelSpor.ON4J.L2 CertificateChecks.KernelSpor.ON4.jL2
#kon_table CertificateChecks.KernelSpor.ON4J.Q2 CertificateChecks.KernelSpor.ON4.jQ2

#kon_levels CertificateChecks.KernelSpor.ON4LMc CertificateChecks.KernelSpor.ON4.mcS
  CertificateChecks.KernelSpor.ON4.baseM 3

#kon_levels CertificateChecks.KernelSpor.ON4LLc CertificateChecks.KernelSpor.ON4.lcS
  CertificateChecks.KernelSpor.ON4.baseM 3
