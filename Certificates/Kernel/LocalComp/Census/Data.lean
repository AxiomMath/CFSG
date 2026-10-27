module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.SpanPin
public import Certificates.Data.Kernel.CensusForm
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3CensusInputs

namespace CertificateChecks.KernelLC.Census

open CFSG.ComponentClassification.AS81.Census CFSG.PSL3Four.Native

meta def insertRow (B : Array Nat) (v : Nat) : Array Nat := Id.run do
  let mut v := v
  for r in B do
    if v >>> Nat.log2 r % 2 == 1 then v := v ^^^ r
  if v == 0 then return B
  let p := Nat.log2 v
  return (B.map fun r => if r >>> p % 2 == 1 then r ^^^ v else r).push v

meta def formKey (t : Array Nat) : Nat := Id.run do
  let B := (t.foldl insertRow #[]).qsort fun a b => a < b
  let mut acc := 0
  for k in [0:B.size] do
    acc := acc ||| (B[k]! <<< (12 * k)) ||| (Nat.log2 B[k]! <<< (72 + 8 * k))
  return acc

meta def orbs : Array Enum := orbits

meta def offs : Array Nat := (orbs.foldl (fun a e => a.push (a.back! + e.tabs.size)) #[0])

meta def allTabs : Array Tab := orbs.foldl (fun a e => a ++ e.tabs) #[]

meta def keys : Array Nat := allTabs.map formKey

meta def wRows : Array Nat := Id.run do
  let mut out := #[]
  for e in orbs do
    let idx : Std.HashMap Tab Nat := (Array.range e.tabs.size).foldl
      (fun m i => m.insert e.tabs[i]! i) {}
    for i in [0:e.tabs.size] do
      let t := e.tabs[i]!
      let p0 := idx.getD (orbitStep 0 t) 65535
      let p1 := idx.getD (orbitStep 1 t) 65535
      out := out.push (p0 ||| (p1 <<< 16) ||| (e.par[i]! <<< 32) ||| (e.lab[i]! <<< 48))
  return out

meta def srRows : Array Nat := Id.run do
  let n := keys.size
  let order := (Array.range n).qsort fun a b => keys[a]! < keys[b]!
  let mut inv := Array.replicate n 0
  for k in [0:n] do
    inv := inv.set! order[k]! k
  return (Array.range n).map fun i => order[i]! ||| (inv[i]! <<< 16)

meta def by8 (v : Array Nat) : Array (Array Nat) :=
  (Array.range ((v.size + 7) / 8)).map fun g => v.extract (8 * g) (8 * g + 8)

meta def keyLeaves : Array (Array Nat) := by8 keys
meta def wLeaves : Array (Array Nat) := by8 wRows
meta def srLeaves : Array (Array Nat) := by8 srRows

meta def badMat (x : Nat × Nat × List Nat) : Array Nat :=
  let (j, e, w) := x
  let h := if e = 0 then (rootsM[j]!).1 else matMul (rootsM[j]!).1 tauM
  let hi := if e = 0 then (rootsM[j]!).2 else matMul tauM (rootsM[j]!).2
  wordMat #[g1M, g2M, h, hi] w

meta def mats : Array (Array Nat) :=
  #[x0M, tauM, cM, b3M, b5M, g1M, g2M, g1iM, g2iM] ++
    (rootsM.foldl (fun a r => a.push r.1 |>.push r.2) #[]) ++
    (goodData.foldl (fun a x => a.push x.2.1 |>.push x.2.2) #[]) ++
    (badData.toArray.map badMat)

meta def imRows : Array (Array Nat) := mats

meta def lpRows : Array (Array Nat) := #[f2perm tauM, f2perm cM]

meta def mbRows : Array (Array Nat) :=
  mats.map fun M => (Array.range 12).map fun b => applyC M (1 <<< b)
meta def mlRows : Array (Array Nat) := mats.map fun M => (Array.range 64).map fun s => applyC M s
meta def mhRows : Array (Array Nat) :=
  mats.map fun M => (Array.range 64).map fun s => applyC M (64 * s)

meta def qtRows : Array (Array Nat) := #[(Array.range 4096).map fun n => (qF (decodeV n)).code.val]

meta def n0Rows : Array (Array Nat) := #[#[formKey n0Tab]]

meta def g1L : Array (Array Nat) := #[mlRows[5]!]
meta def g1H : Array (Array Nat) := #[mhRows[5]!]
meta def g2L : Array (Array Nat) := #[mlRows[6]!]
meta def g2H : Array (Array Nat) := #[mhRows[6]!]
meta def b3L : Array (Array Nat) := #[mlRows[3]!]
meta def b3H : Array (Array Nat) := #[mhRows[3]!]
meta def b5L : Array (Array Nat) := #[mlRows[4]!]
meta def b5H : Array (Array Nat) := #[mhRows[4]!]

meta def gIdx : Std.HashMap Tab Nat :=
  (Array.range allTabs.size).foldl (fun m i => m.insert allTabs[i]! i) {}

meta def bqRows : Array (Array Nat) :=
  badData.toArray.map fun x => #[gIdx.getD (formStep (badMat x) n0Tab) 0]
meta def bjRows : Array (Array Nat) := bqRows.map fun r =>
  #[(Array.range 20).foldl (fun a j => if offs[j]! ≤ r[0]! then j else a) 0]

meta def ofRows : Array (Array Nat) := offs.map fun o => #[o]
meta def cnRows : Array (Array Nat) := orbs.map fun e => #[e.tabs.size]

meta def slices : Array (Nat × Nat) :=
  (Array.range 20).foldl (fun a j =>
    a ++ (Array.range (((orbs[j]!).tabs.size + 1259) / 1260)).map fun t => (j, t)) #[]

meta def sjRows : Array (Array Nat) := slices.map fun x => #[x.1]
meta def stRows : Array (Array Nat) := slices.map fun x => #[x.2]

end CertificateChecks.KernelLC.Census

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelLC.CensusD.KT
  CertificateChecks.KernelLC.Census.keyLeaves 120
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.WT CertificateChecks.KernelLC.Census.wLeaves 64
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.SRT CertificateChecks.KernelLC.Census.srLeaves 32
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.IM CertificateChecks.KernelLC.Census.imRows 12
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.LP CertificateChecks.KernelLC.Census.lpRows 7
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.MB CertificateChecks.KernelLC.Census.mbRows 12
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.ML CertificateChecks.KernelLC.Census.mlRows 12
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.MH CertificateChecks.KernelLC.Census.mhRows 12
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.QT CertificateChecks.KernelLC.Census.qtRows 2
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.N0K CertificateChecks.KernelLC.Census.n0Rows 128
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.G1L CertificateChecks.KernelLC.Census.g1L 12
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.G1H CertificateChecks.KernelLC.Census.g1H 12
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.G2L CertificateChecks.KernelLC.Census.g2L 12
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.G2H CertificateChecks.KernelLC.Census.g2H 12
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.B3L CertificateChecks.KernelLC.Census.b3L 12
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.B3H CertificateChecks.KernelLC.Census.b3H 12
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.B5L CertificateChecks.KernelLC.Census.b5L 12
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.B5H CertificateChecks.KernelLC.Census.b5H 12
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.BQ CertificateChecks.KernelLC.Census.bqRows 16
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.BJ CertificateChecks.KernelLC.Census.bjRows 16
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.OF CertificateChecks.KernelLC.Census.ofRows 16
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.CN CertificateChecks.KernelLC.Census.cnRows 16
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.SJ CertificateChecks.KernelLC.Census.sjRows 16
#kmisc_packarrs CertificateChecks.KernelLC.CensusD.ST CertificateChecks.KernelLC.Census.stRows 16

namespace CertificateChecks.KernelLC.CensusD

open CFSG.KC.Enum CFSG.KC.XorSpan CFSG.KC.SpanPin CFSG.KC.CensusForm

@[expose] noncomputable def Kf (q : Nat) : Nat :=
  fld(KT (Nat.shiftRight q (nat_lit 3)), Nat.mul (nat_lit 120) (Nat.land q (nat_lit 7)),
    nat_lit 1329227995784915872903807060280344575)

@[expose] noncomputable def Wf (q : Nat) : Nat :=
  fld(WT (Nat.shiftRight q (nat_lit 3)), Nat.mul (nat_lit 64) (Nat.land q (nat_lit 7)),
    nat_lit 18446744073709551615)

@[expose] noncomputable def SRf (q : Nat) : Nat :=
  fld(SRT (Nat.shiftRight q (nat_lit 3)), Nat.mul (nat_lit 32) (Nat.land q (nat_lit 7)),
    nat_lit 4294967295)

@[expose] noncomputable def At (l : Nat) : Nat := nIf(Nat.beq l (nat_lit 0), G1L 0, G2L 0)

@[expose] noncomputable def Bt (l : Nat) : Nat := nIf(Nat.beq l (nat_lit 0), G1H 0, G2H 0)

@[expose] noncomputable def Xf (kq : Nat) : Bool :=
  bIf(Nat.beq kq (N0K 0), true,
    bIf(mapsK (nat_lit 6) (nat_lit 12) (nat_lit 4095) (nat_lit 72) (img (B3L 0) (B3H 0)) kq kq,
      bIf(mapsK (nat_lit 6) (nat_lit 12) (nat_lit 4095) (nat_lit 72) (img (B5L 0) (B5H 0)) kq kq,
        false, true), true))

@[expose] noncomputable def slC (s : Nat) : Bool :=
  strictB (SJ s) fun j => strictB (ST s) fun t =>
    sliceK (nat_lit 6) (nat_lit 12) (nat_lit 4095) (nat_lit 72) (nat_lit 6) (nat_lit 63) (nat_lit 2)
      At Bt Kf Wf Xf (OF j) (CN j) (Nat.mul (nat_lit 1260) t) (nat_lit 1260)

@[expose] noncomputable def srC (s : Nat) : Bool :=
  sortK (nat_lit 48960) Kf SRf (Nat.mul (nat_lit 4896) s) (nat_lit 4896)

end CertificateChecks.KernelLC.CensusD

end
