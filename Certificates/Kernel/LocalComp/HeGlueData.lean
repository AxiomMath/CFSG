module

public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeGlueTests
meta import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeGlueTests

namespace CertificateChecks.KernelLC.HeGlue

open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.HeTri CFSG.ComponentClassification.AS81.Hexa
open CFSG.ComponentClassification.AS81.HePres.Native

meta def repEM : Array (Array Nat) := heRepE.toArray
meta def repEIM : Array (Array Nat) := repEM.map (invCand 64)
meta def repFM : Array (Array Nat) := heRepF.toArray
meta def repFIM : Array (Array Nat) := repFM.map (invCand 64)
meta def conjFM : Array (Array Nat) := heConjF.toArray
meta def piEM : Array (Array Nat) := hePiEArrs
meta def piEIM : Array (Array Nat) := piEM.map (invCand 64)
meta def piFM : Array (Array Nat) := hePiFArrs
meta def piFIM : Array (Array Nat) := piFM.map (invCand 64)
meta def g23IM : Array (Array Nat) := heP23Gens.toArray.map (invCand 64)
meta def xyM : Array (Array Nat) :=
  #[invCand 64 hexaT0, invCand 64 (conjA 64 hexaT0 (hePiFArrs.getD 7 #[]))]
meta def conjFIM : Array (Array Nat) := conjFM.map (invCand 64)
meta def piC0M : Array (Array Nat) := hePiCArrs false
meta def piC0IM : Array (Array Nat) := piC0M.map (invCand 32)
meta def piC1M : Array (Array Nat) := hePiCArrs true
meta def piC1IM : Array (Array Nat) := piC1M.map (invCand 32)
meta def g12IM : Array (Array Nat) := heP12CGens.toArray.map (invCand 32)
meta def g13IM : Array (Array Nat) := heP13CGens.toArray.map (invCand 32)
meta def tcM : Array (Array Nat) := #[heTCArr]

meta def p12M : Array (Array Nat) := heP12L.toArray

meta def p23M : Array (Array Nat) := heP23L.toArray

meta def indexOf (L : Array (Array Nat)) : Std.HashMap (Array Nat) Nat := Id.run do
  let mut m : Std.HashMap (Array Nat) Nat := {}
  for j in [0:L.size] do
    m := m.insert L[j]! j
  return m

meta def invIdx (n : Nat) (L : Array (Array Nat)) : Array (Array Nat) :=
  let m := indexOf L
  L.map fun x => #[(m.get? (invCand n x)).getD 0]

meta def ipM : Array (Array Nat) := invIdx 64 p12M
meta def i23M : Array (Array Nat) := invIdx 64 p23M

meta def wBM : Array (Array Nat) := Id.run do
  let mut m : Std.HashMap (Array Nat) Nat := {}
  for p in [0:p12M.size] do
    for i in [0:4] do
      m := m.insert (conjA 64 p12M[p]! (repE i 1)) (4 * p + i)
  return p12M.map fun h => #[(m.get? h).getD 0]

meta def failIdx (n : Nat) (gs : List (Array Nat)) (rels : List (List Nat)) : Nat :=
  (rels.findIdx? fun r => !(eqA n (evalW n gs r) (idA n))).getD rels.length

meta def wRCM : Array (Array Nat) × Array (Array Nat) := Id.run do
  let mut wr : Array (Array Nat) := #[]
  let mut wc : Array (Array Nat) := #[]
  for i in [0:4] do
    let r := repE i 1
    let mut m : Std.HashMap (Array Nat) Nat := {}
    for c in [0:p12M.size] do
      for i' in [0:4] do
        if eqA 64 (conjA 64 p12M[c]! (repE i' 1)) r then
          m := m.insert (conjA 64 p12M[c]! (repE i' 0)) (4 * c + i')
    for h in p12M do
      wr := wr.push #[failIdx 64 [h, r] heRelsP]
      wc := wc.push #[(m.get? h).getD 0]
  return (wr, wc)

meta def wRM : Array (Array Nat) := wRCM.1
meta def wCM : Array (Array Nat) := wRCM.2

meta def classIdx (a : Array Nat) : Array Nat := Id.run do
  let m := indexOf p23M
  let mut out : Array Nat := #[(m.get? a).getD 0]
  let mut i := 0
  while i < out.size do
    let x := p23M[out[i]!]!
    for g in heP23Gens do
      let j := (m.get? (conjA 64 g x)).getD 0
      if !out.contains j then
        out := out.push j
    i := i + 1
  return out

meta def fusImgs (k : Nat) : Array Nat × Array Nat × Array Nat × Array Nat :=
  let i := (k + 1) / 4
  let j := (k + 1) % 4
  (evalW 64 (pairE i) (heWit.getD (4 * k) []), evalW 64 (pairE i) (heWit.getD (4 * k + 2) []),
    evalW 64 (pairF j) (heWit.getD (4 * k + 1) []), evalW 64 (pairF j) (heWit.getD (4 * k + 3) []))

meta def wFM : Array (Array Nat) := (Array.range 15).map fun k =>
  let (x1, x2, y1, y2) := fusImgs k
  let ab := if heWitE.getD k true then (x1, x2) else (y1, y2)
  #[(p23M.findIdx? fun q => eqA 64 (conjA 64 q ab.1) ab.2).getD 0]

meta def fusCls : Array (Array Nat) := (Array.range 15).map fun k =>
  let (x1, _, y1, _) := fusImgs k
  classIdx (if heWitE.getD k true then y1 else x1)

meta def wMM : Array (Array Nat) := fusCls.map fun c => #[c.size]
meta def wXM : Array (Array Nat) :=
  (Array.range (15 * 64)).map fun t => #[(fusCls[t / 64]!).getD (t % 64) 0]

meta def kYM : Array (Array Nat) := p23M.map fun hy => #[failIdx 64 (heT8 (idA 64) hy) heRelsY]

meta def kXM : Array (Array Nat) :=
  let yF := hePiFArrs.getD 7 #[]
  let yF' := conjA 64 hexaT0 yF
  p23M.map fun hx => #[failIdx 64 (heT8 hx (idA 64)) heRelsX +
    8 * failIdx 64 (heT8 hx yF) heRels23 + 64 * failIdx 64 (heT8 hx yF') heRels23]

end CertificateChecks.KernelLC.HeGlue

public section

set_option maxRecDepth 400000

#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.RE CertificateChecks.KernelLC.HeGlue.repEM 7
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.REI CertificateChecks.KernelLC.HeGlue.repEIM 7
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.RF CertificateChecks.KernelLC.HeGlue.repFM 7
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.RFI CertificateChecks.KernelLC.HeGlue.repFIM 7
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.CF CertificateChecks.KernelLC.HeGlue.conjFM 7
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.CFI CertificateChecks.KernelLC.HeGlue.conjFIM 7
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.PE CertificateChecks.KernelLC.HeGlue.piEM 7
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.PEI CertificateChecks.KernelLC.HeGlue.piEIM 7
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.PF CertificateChecks.KernelLC.HeGlue.piFM 7
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.PFI CertificateChecks.KernelLC.HeGlue.piFIM 7
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.G23I CertificateChecks.KernelLC.HeGlue.g23IM 7
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.XY CertificateChecks.KernelLC.HeGlue.xyM 7
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.PC0 CertificateChecks.KernelLC.HeGlue.piC0M 6
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.PC0I CertificateChecks.KernelLC.HeGlue.piC0IM 6
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.PC1 CertificateChecks.KernelLC.HeGlue.piC1M 6
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.PC1I CertificateChecks.KernelLC.HeGlue.piC1IM 6
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.G12I CertificateChecks.KernelLC.HeGlue.g12IM 6
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.G13I CertificateChecks.KernelLC.HeGlue.g13IM 6
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.TC CertificateChecks.KernelLC.HeGlue.tcM 6
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.IP CertificateChecks.KernelLC.HeGlue.ipM 16
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.I23 CertificateChecks.KernelLC.HeGlue.i23M 16
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.WB CertificateChecks.KernelLC.HeGlue.wBM 16
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.WR CertificateChecks.KernelLC.HeGlue.wRM 8
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.WC CertificateChecks.KernelLC.HeGlue.wCM 16
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.WF CertificateChecks.KernelLC.HeGlue.wFM 16
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.WM CertificateChecks.KernelLC.HeGlue.wMM 8
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.WX CertificateChecks.KernelLC.HeGlue.wXM 16
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.KY CertificateChecks.KernelLC.HeGlue.kYM 8
#kmisc_packarrs CertificateChecks.KernelLC.HeGlueD.KX CertificateChecks.KernelLC.HeGlue.kXM 16

end
