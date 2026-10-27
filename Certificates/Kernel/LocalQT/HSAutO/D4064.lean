module

public import Certificates.Kernel.LocalQT.PEnumD
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.LocalQT.HSAutO
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuterCheckInputs
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutData
public import CFSG.Assembly.Defs
public meta import CFSG.Sporadic.SmallOddCore.HSAut

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LQT.HO

open CFSG.PSL3Four.Native CFSG.QuasithinUnique.Id2519.HSAut

meta def orbM (s : Nat) : Array Nat := Id.run do
  let gs := #[e1Tab, e2Tab]
  let mut seen : Array Bool := (Array.replicate 3850 false).set! s true
  let mut orb : Array Nat := #[s]
  let mut i := 0
  for _ in [0:3850] do
    if i < orb.size then
      let x := orb[i]!
      for g in gs do
        let y := g[x]!
        if !seen[y]! then
          seen := seen.set! y true
          orb := orb.push y
      i := i + 1
  return orb.qsort (· < ·)

meta def opM : Array Nat := orbM 152

meta def posO (x : Nat) : Nat := (opM.findIdx? (· == x)).getD 35

meta def gM : Array (Array Nat) :=
  #[e1Tab, e2Tab].map fun g => opM.map fun x => posO g[x]!

meta def giM : Array (Array Nat) := gM.map (invTab 35)

meta def idM : Array Nat := idTab 35

meta def tM : Array Tab := (enumBFS 35 gM 20160).tabs

meta def clsM : Array Nat × Array Nat × Array Nat × Array Nat := Id.run do
  let m := tM.size
  let idx := indexOf tM
  let mut lab : Array Nat := Array.replicate m 14
  let mut wit : Array Nat := Array.replicate m 0
  let mut reps : Array Nat := Array.replicate 14 0
  let mut used : Array Bool := Array.replicate 14 false
  for k in [0:m] do
    if lab[k]! == 14 then
      lab := lab.set! k 15
      let mut orb : Array Nat := #[k]
      let mut ws : Array Nat := #[0]
      let mut q := 0
      for _ in [0:m] do
        if q < orb.size then
          let x := orb[q]!
          let w := ws[q]!
          for j in [0:2] do
            let p := posOf idx tM (conjTab 35 gM[j]! giM[j]! tM[x]!)
            if lab[p]! == 14 then
              lab := lab.set! p 15
              orb := orb.push p
              ws := ws.push (posOf idx tM (comp 35 gM[j]! tM[w]!))
          q := q + 1
      let mut l := 14
      for i in [0:14] do
        if l == 14 && !used[i]! && classSizes[i]! == orb.size then
          l := i
      if l < 14 then
        used := used.set! l true
        reps := reps.set! l k
      for t in [0:orb.size] do
        lab := lab.set! orb[t]! l
        wit := wit.set! orb[t]! ws[t]!
  let cp := ((List.range m).toArray.map fun k => (List.range 2).toArray.map fun j =>
    posOf idx tM (conjTab 35 gM[j]! giM[j]! tM[k]!)).flatten
  return (lab, wit, reps, cp)

meta def labM : Array Nat := clsM.1

meta def witM : Array Nat := clsM.2.1

meta def repM : Array Nat := clsM.2.2.1

meta def cpM : Array Nat := clsM.2.2.2

meta def vcM : Array Nat :=
  ((List.range 315).toArray.map fun s => (List.range 14).toArray.map fun l =>
    ((List.range 64).filter fun d => labM[64 * s + d]! == l).length).flatten

meta def qmM : Array (Array Nat) :=
  let o := orbM 18
  #[(List.range 3850).toArray.map fun x => if o.contains x then 1 else 0]

end CFSG.KD.LQT.HO

#kpenum_d CFSG.KD.LQT.HO.A 35 6 false CFSG.KD.LQT.HO.gM CFSG.KD.LQT.HO.giM CFSG.KD.LQT.HO.idM 20160
#krows32 CFSG.KD.LQT.HO.LAB CFSG.KD.LQT.HO.labM
#krows32 CFSG.KD.LQT.HO.WIT CFSG.KD.LQT.HO.witM
#krows32 CFSG.KD.LQT.HO.REP CFSG.KD.LQT.HO.repM
#krows32 CFSG.KD.LQT.HO.CP CFSG.KD.LQT.HO.cpM
#krows32 CFSG.KD.LQT.HO.VC CFSG.KD.LQT.HO.vcM
#krows32 CFSG.KD.LQT.HO.OP CFSG.KD.LQT.HO.opM
#kmisc_packarrs CFSG.KD.LQT.HO.QM CFSG.KD.LQT.HO.qmM 1

end
