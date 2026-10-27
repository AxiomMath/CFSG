module

public import Certificates.Kernel.LocalQT.TabA2.D4043
public import Certificates.Data.Kernel.LocalQT.TabL34

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LQT.TL

open CFSG.PSL3Four.Native CFSG.KD.LQT.TA

meta def rgM : Array (Array Nat) := gTabs

meta def cPos : Array Nat := cM

meta def closure (gs : Array Tab) : Array Tab := (bfs (leftStep 42 gs) gs.size (idTab 42) 200).tabs

meta def cgM : Array Nat := Id.run do
  let mut gs : Array Nat := #[]
  let mut cl : Array Tab := #[idTab 42]
  for k in cPos do
    let x := eM.tabs[k]!
    if !cl.contains x then
      gs := gs.push k
      cl := closure (gs.map fun i => eM.tabs[i]!)
  return gs

meta def twIdx : Std.HashMap Tab Nat := Id.run do
  let mut m : Std.HashMap Tab Nat := {}
  for k in [0:eM.tabs.size] do
    let s := eM.tabs[k]!
    let t := comp 42 (comp 42 (invTab 42 s) r₂T) s
    if !m.contains t then
      m := m.insert t k
  return m

meta def twM : Array Nat :=
  let m := twIdx
  eM.tabs.map fun u =>
    if commR u && comp 42 u u == idTab 42 && !(u == idTab 42) then
      m.getD (comp 42 r₂T u) 0
    else 0

meta def kCM : Array (Array Nat) := #[#[cgM.size]]

end CFSG.KD.LQT.TL

#kpenum_d CFSG.KD.LQT.TL.R 42 6 false CFSG.KD.LQT.TL.rgM CFSG.KD.LQT.TL.rgM CFSG.KD.LQT.TA.idM
  241920
#krows32 CFSG.KD.LQT.TL.CGP CFSG.KD.LQT.TL.cgM
#krows32 CFSG.KD.LQT.TL.TWP CFSG.KD.LQT.TL.twM
#kmisc_packarrs CFSG.KD.LQT.TL.KC CFSG.KD.LQT.TL.kCM 32

namespace CFSG.KD.LQT.TL

open CFSG.KS.PEnum

@[expose] noncomputable def CG (i : Nat) : Nat := r32 CGP i

@[expose] noncomputable def TW (i : Nat) : Nat := r32 TWP i

@[expose] noncomputable def kC : Nat := KC (nat_lit 0)

end CFSG.KD.LQT.TL

end
