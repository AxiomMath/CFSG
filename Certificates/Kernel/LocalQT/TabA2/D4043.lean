module

public import Certificates.Kernel.LocalQT.PEnumD
public import Certificates.Kernel.Misc.Perm.HexCmd
public import Certificates.Data.Kernel.LocalQT.TabA2
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabA2CheckInputs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.LQT.TA

open CFSG.PSL3Four.Native CFSG.QuasithinUnique.Id2519.Tab.A2

meta def gM : Array (Array Nat) := gensS

meta def idM : Array Nat := idTab 42

meta def uM : Array (Array Nat) := uTabs

meta def xM : Array (Array Nat) := #[a0T, zT, r₂T]

meta def eM : Enum := enumBFS 42 gensS 20160

meta def posM (x : Tab) : Nat := posOf (indexOf eM.tabs) eM.tabs x

meta def commR (x : Tab) : Bool := comp 42 x r₂T == comp 42 r₂T x

meta def transM : Array Nat := Id.run do
  let mut r := Array.replicate 16 0
  for k in [0:eM.tabs.size] do
    let x := eM.tabs[k]!
    if x[0]! == 0 then
      let c := conjTab 42 x (invTab 42 x) a0T
      for j in [0:16] do
        if r[j]! == 0 && uTabs[j]! == c then
          r := r.set! j k
  return r

meta def wM : Array Nat := uTabs.map posM ++ transM ++ #[posM a0T, posM zT]

meta def cM : Array Nat :=
  (List.range eM.tabs.size).toArray.filter fun k => commR eM.tabs[k]!

meta def vM : Array Nat := eM.tabs.map fun x =>
  if commR x && comp 42 x x == idTab 42 then
    (cM.find? fun y =>
      let t := eM.tabs[y]!
      uTabs.contains (conjTab 42 t (invTab 42 t) x)).getD 0
  else 0

end CFSG.KD.LQT.TA

#kpenum_d CFSG.KD.LQT.TA.S 42 6 false CFSG.KD.LQT.TA.gM CFSG.KD.LQT.TA.gM CFSG.KD.LQT.TA.idM 20160
#kmisc_packarrs CFSG.KD.LQT.TA.U CFSG.KD.LQT.TA.uM 6
#kmisc_packarrs CFSG.KD.LQT.TA.X CFSG.KD.LQT.TA.xM 6
#krows32 CFSG.KD.LQT.TA.WP CFSG.KD.LQT.TA.wM
#krows32 CFSG.KD.LQT.TA.VP CFSG.KD.LQT.TA.vM

namespace CFSG.KD.LQT.TA

open CFSG.KS.PEnum

@[expose] noncomputable def W (i : Nat) : Nat := r32 WP i

@[expose] noncomputable def V (i : Nat) : Nat := r32 VP i

@[expose] noncomputable def WT (j : Nat) : Nat := r32 WP (Nat.add (nat_lit 16) j)

end CFSG.KD.LQT.TA

end
