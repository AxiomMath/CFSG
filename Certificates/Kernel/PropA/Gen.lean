module

public meta import Certificates.Kernel.PropA.Words
public meta import Certificates.Data.PropAModelData
public meta import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CertificateChecks.KernelPropA.Gen

open CFSG.PSL3Four.Native CertificateChecks.KernelPropA

meta def nat28 (t : Array UInt32) : Array Nat := t.map (·.toNat)

meta def gensK (b : Bool) : Array (Array Nat) :=
  #[nat28 CFSG.EvenSporadicStandard.M12Std.PropA.Data.tabA,
    nat28 CFSG.EvenSporadicStandard.M12Std.PropA.Data.tabB,
    nat28 (if b then CFSG.EvenSporadicStandard.M12Std.PropA.Data.tabG2
      else CFSG.EvenSporadicStandard.M12Std.PropA.Data.tabG1),
    nat28 CFSG.EvenSporadicStandard.M12Std.PropA.Data.tabT]

meta def wt (gs : Array (Array Nat)) (w : List Int) : Array Nat :=
  w.foldr (fun (l : Int) (acc : Array Nat) =>
    comp 28 (if 0 < l then gs[(l - 1).toNat]! else invTab 28 gs[(-l - 1).toNat]!) acc) (idTab 28)

meta def wts (b : Bool) (ws : List (List Int)) : Array (Array Nat) :=
  (ws.map (wt (gensK b))).toArray

meta def invs (a : Array (Array Nat)) : Array (Array Nat) := a.map (invTab 28)

meta def idT : Array Nat := idTab 28

meta def gK1 : Array (Array Nat) := gensK false
meta def giK1 : Array (Array Nat) := invs gK1
meta def gK2 : Array (Array Nat) := gensK true
meta def giK2 : Array (Array Nat) := invs gK2
meta def gD : Array (Array Nat) := wts false pa450010wD
meta def giD : Array (Array Nat) := invs gD

meta def gJ : Array (Array Nat) := wts false pa450010wJ
meta def giJ : Array (Array Nat) := invs gJ
meta def gCDX : Array (Array Nat) := wts false pa450010wCDX
meta def giCDX : Array (Array Nat) := invs gCDX
meta def gCDU : Array (Array Nat) := wts false pa450010wCDU
meta def giCDU : Array (Array Nat) := invs gCDU
meta def gCDA : Array (Array Nat) := wts false pa450010wCDA
meta def giCDA : Array (Array Nat) := invs gCDA
meta def gCDG : Array (Array Nat) := wts false pa450010wCDG
meta def giCDG : Array (Array Nat) := invs gCDG
meta def gSD : Array (Array Nat) := wts false pa450010wSD
meta def giSD : Array (Array Nat) := invs gSD
meta def gCKX1 : Array (Array Nat) := wts false pa450010wCKX
meta def giCKX1 : Array (Array Nat) := invs gCKX1
meta def gCKX2 : Array (Array Nat) := wts true pa450010wCKX
meta def giCKX2 : Array (Array Nat) := invs gCKX2
meta def gS1 : Array (Array Nat) := wts false pa450010wS1
meta def giS1 : Array (Array Nat) := invs gS1
meta def gS2 : Array (Array Nat) := wts true pa450010wS2
meta def giS2 : Array (Array Nat) := invs gS2
meta def gR : Array (Array Nat) := wts false pa450010wR
meta def giR : Array (Array Nat) := invs gR

meta def rx : Array Nat := wt (gensK false) pa450010wx
meta def ru : Array Nat := wt (gensK false) pa450010wu
meta def rA : Array Nat := wt (gensK false) [1]
meta def rep1 (i : Nat) : Array Nat := wt (gensK false) (pa450010wReps.getD i [])
meta def rep2 (i : Nat) : Array Nat := wt (gensK true) (pa450010wReps.getD i [])
meta def r10 : Array Nat := rep1 0
meta def r11 : Array Nat := rep1 1
meta def r12 : Array Nat := rep1 2
meta def r13 : Array Nat := rep1 3
meta def r14 : Array Nat := rep1 4
meta def r15 : Array Nat := rep1 5
meta def r20 : Array Nat := rep2 0
meta def r21 : Array Nat := rep2 1
meta def r22 : Array Nat := rep2 2
meta def r23 : Array Nat := rep2 3
meta def r24 : Array Nat := rep2 4
meta def r25 : Array Nat := rep2 5

meta def enumT (conj : Bool) (gs gi : Array (Array Nat)) (root : Array Nat) (cap : Nat) :
    Array (Array Nat) :=
  let step : Nat → Tab → Tab := fun j t =>
    if conj then conjTab 28 gs[j]! gi[j]! t else comp 28 gs[j]! t
  (bfs step gs.size root cap).tabs

meta def tS1 : Array (Array Nat) := enumT false gS1 giS1 idT 256
meta def tS2 : Array (Array Nat) := enumT false gS2 giS2 idT 256
meta def tSD : Array (Array Nat) := enumT false gSD giSD idT 64
meta def cK1 (i : Nat) : Array (Array Nat) := enumT true gK1 giK1 (rep1 i) 792
meta def cK2 (i : Nat) : Array (Array Nat) := enumT true gK2 giK2 (rep2 i) 792
meta def c10 : Array (Array Nat) := cK1 0
meta def c11 : Array (Array Nat) := cK1 1
meta def c12 : Array (Array Nat) := cK1 2
meta def c13 : Array (Array Nat) := cK1 3
meta def c14 : Array (Array Nat) := cK1 4
meta def c15 : Array (Array Nat) := cK1 5
meta def c20 : Array (Array Nat) := cK2 0
meta def c21 : Array (Array Nat) := cK2 1
meta def c22 : Array (Array Nat) := cK2 2
meta def c23 : Array (Array Nat) := cK2 3
meta def c24 : Array (Array Nat) := cK2 4
meta def c25 : Array (Array Nat) := cK2 5
meta def cDX : Array (Array Nat) := enumT true gD giD rx 396
meta def cDA : Array (Array Nat) := enumT true gD giD rA 495

end CertificateChecks.KernelPropA.Gen

end
