module

public import Certificates.Kernel.Sporadic.OddCore.TBfsCmd
public import Certificates.Kernel.Sporadic.OddCore.RowsCmd
public import Certificates.Kernel.Sporadic.OrbRecGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLData
public meta import CFSG.ClassicalInvolution.SmallCases.Sporadic.McLData
public meta import Certificates.Data.CFSGNative.Perm.Chain
public meta import Std.Data.HashMap

public section

namespace CertificateChecks.KernelSpor.McLC

open CFSG.Sporadic.Th.Native CFSG.Perm.Native

meta def cmp (a b : Array Nat) : Array Nat := b.map fun x => a[x]!

meta def inv (a : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 275 0
  for i in [0:275] do
    r := r.set! a[i]! i
  return r

meta def idP : Array Nat := Array.range 275

meta def kgM : Array (Array Nat) :=
  CFSG.ClassicalInvolution.McLData.kgens.toArray.map fun t => t.map (·.toNat)

abbrev PW := Array Nat × List Nat

meta def pwMul (a b : PW) : PW := (cmp a.1 b.1, a.2 ++ b.2)

meta def pwInv (a : PW) : PW := (inv a.1, a.2.reverse.map fun c => c ^^^ 1)

meta def orbitTr (gs : Array PW) (b : Nat) : Array Nat × Std.HashMap Nat PW := Id.run do
  let mut pts : Array Nat := #[b]
  let mut u : Std.HashMap Nat PW := (∅ : Std.HashMap Nat PW).insert b (idP, [])
  let mut h := 0
  while h < pts.size do
    let p := pts[h]!
    let up := u.getD p (idP, [])
    for g in gs do
      let q := g.1[p]!
      if !(u.contains q) then
        u := u.insert q (pwMul g up)
        pts := pts.push q
    h := h + 1
  return (pts, u)

meta def schreier (gs : Array PW) (b : Nat) : Array PW := Id.run do
  let (pts, u) := orbitTr gs b
  let mut out : Array PW := #[]
  for p in pts do
    for g in gs do
      let s := pwMul (pwInv (u.getD (g.1[p]!) (idP, []))) (pwMul g (u.getD p (idP, [])))
      if s.1 != idP then out := out.push s
  return out

meta def gW : Array PW := #[(kgM[0]!, [0]), (kgM[1]!, [2])]

meta def s1M : Array PW := Id.run do
  let mut S : Array PW := #[]
  let mut sz := 1
  for s in schreier gW 0 do
    if sz < 56 then
      let sz' := (orbitTr (S.push s) 14).1.size
      if sz < sz' then
        S := S.push s
        sz := sz'
  return S

meta def s2M : Array PW :=
  ((schreier s1M 14).filter fun s => s.1[2]! != 2).extract 0 1

meta def evM : Array PW := gW ++ s1M ++ s2M

meta def lettersP : Array (Array Nat) := evM.foldl (fun acc s => (acc.push s.1).push (inv s.1)) #[]

meta def lettersM : Array Table := lettersP.map fun t => t.map UInt32.ofNat

meta def ltM : Array Nat := lettersP.flatten

meta def wcM : Array Nat := ((evM.extract 2 evM.size).toList.flatMap (·.2)).toArray

meta def wsM : Array Nat :=
  ((evM.extract 2 evM.size).foldl (fun (acc : Array Nat × Nat) s => (acc.1.push acc.2,
    acc.2 + s.2.length)) (#[0, 0], 0)).1

meta def wnM : Array Nat := #[0, 0] ++ (evM.extract 2 evM.size).map (·.2.length)

meta def baseM : Array Nat := #[0, 14, 2]

meta def lv0M : Array Nat := levelLetters lettersM baseM 0
meta def lv1M : Array Nat := levelLetters lettersM baseM 1
meta def lv2M : Array Nat := levelLetters lettersM baseM 2

meta def trM (i : Nat) : Array (Array Nat) := Id.run do
  let T := treeBFS 275 baseM[i]! lettersM (levelLetters lettersM baseM i)
  let mut ts : Array (Array Nat) := #[idP]
  for k in [1:T.pts.size] do
    ts := ts.push (cmp lettersP[(T.lab[k]!).toNat]! ts[(T.par[k]!).toNat]!)
  return ts

meta def t0M : Array (Array Nat) := trM 0
meta def t1M : Array (Array Nat) := trM 1
meta def t2M : Array (Array Nat) := trM 2
meta def t0IM : Array (Array Nat) := t0M.map inv
meta def t1IM : Array (Array Nat) := t1M.map inv
meta def t2IM : Array (Array Nat) := t2M.map inv

meta def repM : Array (Array Nat) :=
  CFSG.ClassicalInvolution.McLData.repTbls.toArray.map fun t => t.map (·.toNat)

meta def alM : Array Nat := CFSG.ClassicalInvolution.McLData.Ta.map (·.toNat)

meta def witM : Array Nat := Id.run do
  let n0 := t0M.size
  let n1 := t1M.size
  let n2 := t2M.size
  let key := fun (a b c : Nat) => (a * 275 + b) * 275 + c
  let mut idx : Std.HashMap Nat Nat := ∅
  for i0 in [0:n0] do
    for i1 in [0:n1] do
      for i2 in [0:n2] do
        let f := fun y => t0M[i0]![t1M[i1]![t2M[i2]![y]!]!]!
        idx := idx.insert (key (f 0) (f 14) (f 2)) ((i0 * n1 + i1) * n2 + i2)
  let N := n0 * n1 * n2
  let mut W : Array Nat := Array.replicate N 0
  let mut done : Array Bool := Array.replicate N false
  let iT := idx.getD (key 0 14 2) 0
  W := W.set! iT 21
  done := done.set! iT true
  let iA := idx.getD (key alM[0]! alM[14]! alM[2]!) 0
  W := W.set! iA 22
  done := done.set! iA true
  for j in [0:repM.size] do
    let r := repM[j]!
    for c0 in [0:n0] do
      for c1 in [0:n1] do
        for c2 in [0:n2] do
          let c := fun y => t0M[c0]![t1M[c1]![t2M[c2]![y]!]!]!
          let ci := fun y => t2IM[c2]![t1IM[c1]![t0IM[c0]![y]!]!]!
          let z := fun y => c r[ci y]!
          let t := idx.getD (key (z 0) (z 14) (z 2)) 0
          if !done[t]! then
            W := W.set! t (j ||| (c0 <<< 5) ||| (c1 <<< 13) ||| (c2 <<< 19))
            done := done.set! t true
  if done.all id then return W else return #[]

end CertificateChecks.KernelSpor.McLC

#krows CertificateChecks.KernelSpor.McLC.LT CertificateChecks.KernelSpor.McLC.ltM
#kc_nattree CertificateChecks.KernelSpor.McLC.WC CertificateChecks.KernelSpor.McLC.wcM
#kc_nattree CertificateChecks.KernelSpor.McLC.WS CertificateChecks.KernelSpor.McLC.wsM
#kc_nattree CertificateChecks.KernelSpor.McLC.WN CertificateChecks.KernelSpor.McLC.wnM

#ktbfs CertificateChecks.KernelSpor.McLC.CT0 275 0 CertificateChecks.KernelSpor.McLC.lettersM
  CertificateChecks.KernelSpor.McLC.lv0M
#ktbfs CertificateChecks.KernelSpor.McLC.CT1 275 14 CertificateChecks.KernelSpor.McLC.lettersM
  CertificateChecks.KernelSpor.McLC.lv1M
#ktbfs CertificateChecks.KernelSpor.McLC.CT2 275 2 CertificateChecks.KernelSpor.McLC.lettersM
  CertificateChecks.KernelSpor.McLC.lv2M

#kmisc_packarrs CertificateChecks.KernelSpor.McLC.T0 CertificateChecks.KernelSpor.McLC.t0M 9
#kmisc_packarrs CertificateChecks.KernelSpor.McLC.T1 CertificateChecks.KernelSpor.McLC.t1M 9
#kmisc_packarrs CertificateChecks.KernelSpor.McLC.T2 CertificateChecks.KernelSpor.McLC.t2M 9
#kmisc_packarrs CertificateChecks.KernelSpor.McLC.T0I CertificateChecks.KernelSpor.McLC.t0IM 9
#kmisc_packarrs CertificateChecks.KernelSpor.McLC.T1I CertificateChecks.KernelSpor.McLC.t1IM 9
#kmisc_packarrs CertificateChecks.KernelSpor.McLC.T2I CertificateChecks.KernelSpor.McLC.t2IM 9
#kmisc_packarrs CertificateChecks.KernelSpor.McLC.RP CertificateChecks.KernelSpor.McLC.repM 9

#krows CertificateChecks.KernelSpor.McLC.WT CertificateChecks.KernelSpor.McLC.witM

end
