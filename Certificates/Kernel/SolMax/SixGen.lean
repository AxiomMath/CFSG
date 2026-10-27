module

public import Certificates.Data.Kernel.SolMaxSixGenK
public import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
public import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
public meta import Certificates.Data.Kernel.SolMaxSixGenK
public meta import CFSG.Certificates.Kernel.Common.Eval
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Common.Eval

public section

namespace CertificateChecks.KernelSolMax.SixGen

open CFSG.PSL3Four.Native CFSG.ComponentClassification.SolMax.SixGen CFSG.KC.Eval

meta def pairWords (gs : Array Tab) : Array (Nat × Nat × List Nat) := Id.run do
  let mut seen : Std.HashMap (Nat × Nat) Unit := (∅ : Std.HashMap (Nat × Nat) Unit).insert (0, 1) ()
  let mut q : Array (Nat × Nat × List Nat) := #[(0, 1, [])]
  let mut h := 0
  while h < q.size do
    let (x, y, w) := q[h]!
    h := h + 1
    for j in [0:gs.size] do
      let g := gs[j]!
      let p := (g[x]!, g[y]!)
      if !seen.contains p then
        seen := seen.insert p ()
        q := q.push (p.1, p.2, j :: w)
  return q

meta def moved (t : Tab) : Nat := ((List.range t.size).filter fun i => t[i]! != i).length

meta def threeWord (gs : Array Tab) (cap : Nat) : Option (List Nat) := Id.run do
  let mut seen : Std.HashMap Tab Unit := (∅ : Std.HashMap Tab Unit).insert (idTab 9) ()
  let mut q : Array (Tab × List Nat) := #[(idTab 9, [])]
  let mut h := 0
  while h < q.size && h < cap do
    let (g, w) := q[h]!
    h := h + 1
    let mut p := g
    for k in [1:30] do
      if moved p == 3 then
        return some ((List.replicate k w).flatten)
      p := comp 9 p g
    for j in [0:gs.size] do
      let x := comp 9 gs[j]! g
      if !seen.contains x then
        seen := seen.insert x ()
        q := q.push (x, j :: w)
  return none

meta def wordVal (w : List Nat) : Val := .list (w.toArray.map .nat)

meta def search : Step := fun _ => do
  let mut T : Array Val := #[]
  let mut S : Array Val := #[]
  let mut C : Array Val := #[]
  for e in entries do
    let gs : Array Tab := (e.2.map fun l => tabOf (permOf l)).toArray
    let P := pairWords gs
    let mut tq : Array Val := #[]
    let mut sq : Array Val := #[]
    for q in [0:9] do
      match P.find? (fun r => r.1 == q) with
      | some r => tq := tq.push (wordVal r.2.2)
      | none => throw s!"no word to {q}"
      if q == 0 then
        sq := sq.push (wordVal [])
      else
        match P.find? (fun r => r.1 == 0 && r.2.1 == q) with
        | some r => sq := sq.push (wordVal r.2.2)
        | none => throw s!"no stabilizer word to {q}"
    T := T.push (.list tq)
    S := S.push (.list sq)
    match threeWord gs 50000 with
    | some w => C := C.push (wordVal w)
    | none => throw "no three-cycle"
  return #[(`T, .list T), (`S, .list S), (`C, .list C)]

meta def cgM : Array (Array Nat) := cgTabs

meta def idM : Array Nat := idTab 9

end CertificateChecks.KernelSolMax.SixGen

#kc_eval CertificateChecks.KernelSolMax SGW CertificateChecks.KernelSolMax.SixGen.search

#kpenum CertificateChecks.KernelSolMax.CE 9 4 false CertificateChecks.KernelSolMax.SixGen.cgM
  CertificateChecks.KernelSolMax.SixGen.cgM CertificateChecks.KernelSolMax.SixGen.idM 288

namespace CertificateChecks.KernelSolMax.SixGen

open CFSG.ComponentClassification.SolMax.SixGen CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
  CFSG.KS.PEnum

theorem k_wit : sixGenWitK SGW.T SGW.S SGW.C = true := by
  decide +kernel

theorem k_witNeg : sixGenWitK SGW.S SGW.T SGW.C = false := by
  decide +kernel

theorem k_hd : bAnd(gensK cgTabs 9 4 CE.k CE.G, bAnd(Nat.beq CE.cnt 288,
    penumHdK (pidn 9 4) CE.cnt 288 CE.T CE.PL)) = true := by
  quickRfl

theorem k_sl : penumSlK 9 4 (mask 4) (9 * 4) false CE.G CE.GI CE.k CE.cnt CE.T CE.PL
    CE.POS CE.SRT CE.SRI 0 288 = true := by
  quickRfl

theorem k_cov : (cgCommK && coverK (penumRec 9 4 CE.cnt CE.T CE.PL)) = true := by
  decide +kernel

end CertificateChecks.KernelSolMax.SixGen

end
