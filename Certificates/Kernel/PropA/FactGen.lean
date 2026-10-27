module

public meta import Certificates.Kernel.PropA.Gen
public meta import Certificates.Kernel.PropA.FactWords
public import Certificates.Kernel.PropA.Gen

public section

namespace CertificateChecks.KernelPropA.Gen

open CFSG.PSL3Four.Native CertificateChecks.KernelPropA

meta def conjQ (a ai b : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let mut out := #[]
  for i in [0:a.size] do
    for j in [0:b.size] do
      out := out.push (conjTab 28 a[i]! ai[i]! b[j]!)
  return out

meta def commQ (a ai : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let mut out := #[]
  for i in [0:a.size] do
    for j in [0:a.size] do
      out := out.push (comp 28 (comp 28 (comp 28 a[i]! a[j]!) ai[i]!) ai[j]!)
  return out

meta def commT (p q : Array Nat) : Bool := comp 28 p q == comp 28 q p

meta def tJ : Array (Array Nat) := enumT false gJ giJ idT 60
meta def tCDX : Array (Array Nat) := enumT false gCDX giCDX idT 240

meta def commPair (t : Array (Array Nat)) (j : Array Nat) : Array Nat × Array Nat := Id.run do
  for u in t do
    for v in t do
      if comp 28 u v == comp 28 (comp 28 j v) u then return (u, v)
  return (idT, idT)

meta def qAB1a : Array (Array Nat) := #[(commPair tCDX gJ[0]!).1]
meta def qAB1b : Array (Array Nat) := #[(commPair tCDX gJ[0]!).2]
meta def qAB2a : Array (Array Nat) := #[(commPair tCDX gJ[1]!).1]
meta def qAB2b : Array (Array Nat) := #[(commPair tCDX gJ[1]!).2]
meta def qJP1a : Array (Array Nat) := #[(commPair tJ gJ[0]!).1]
meta def qJP1b : Array (Array Nat) := #[(commPair tJ gJ[0]!).2]
meta def qJP2a : Array (Array Nat) := #[(commPair tJ gJ[1]!).1]
meta def qJP2b : Array (Array Nat) := #[(commPair tJ gJ[1]!).2]
meta def tR : Array (Array Nat) := enumT false gR giR idT 60
meta def qRP1a : Array (Array Nat) := #[(commPair tR gR[0]!).1]
meta def qRP1b : Array (Array Nat) := #[(commPair tR gR[0]!).2]
meta def qRP2a : Array (Array Nat) := #[(commPair tR gR[1]!).1]
meta def qRP2b : Array (Array Nat) := #[(commPair tR gR[1]!).2]
meta def qEJ : Array (Array Nat) := conjQ gCDX giCDX gJ
meta def qEE : Array (Array Nat) := commQ gCDX giCDX
meta def qKJ1 : Array (Array Nat) := conjQ gCKX1 giCKX1 gJ
meta def qKJ2 : Array (Array Nat) := conjQ gCKX2 giCKX2 gJ

meta def gY1 : Array (Array Nat) := wts false pa450010wY
meta def giY1 : Array (Array Nat) := invs gY1
meta def gY2 : Array (Array Nat) := wts true pa450010wY
meta def giY2 : Array (Array Nat) := invs gY2
meta def tCK1 : Array (Array Nat) := enumT false gCKX1 giCKX1 idT 960
meta def tCK2 : Array (Array Nat) := enumT false gCKX2 giCKX2 idT 960
meta def tY1 : Array (Array Nat) := enumT false gY1 giY1 idT 8
meta def tY2 : Array (Array Nat) := enumT false gY2 giY2 idT 8

meta def g3 (tc ty : Array (Array Nat)) : Array Nat × Array Nat := Id.run do
  for c in tc do
    for y in ty do
      if comp 28 c y == comp 28 (comp 28 rx y) c then return (c, y)
  return (idT, idT)

meta def qG3c1 : Array (Array Nat) := #[(g3 tCK1 tY1).1]
meta def qG3y1 : Array (Array Nat) := #[(g3 tCK1 tY1).2]
meta def qG3c2 : Array (Array Nat) := #[(g3 tCK2 tY2).1]
meta def qG3y2 : Array (Array Nat) := #[(g3 tCK2 tY2).2]

meta def g1 (cl : Array (Array Nat)) : Array (Array Nat) := Id.run do
  for s in cl do
    if commT s rx && !(commT s gJ[0]! && commT s gJ[1]!) then return #[s]
  return #[idT]

meta def qG1_10 : Array (Array Nat) := g1 c10
meta def qG1_11 : Array (Array Nat) := g1 c11
meta def qG1_12 : Array (Array Nat) := g1 c12
meta def qG1_13 : Array (Array Nat) := g1 c13
meta def qG1_14 : Array (Array Nat) := g1 c14
meta def qG1_15 : Array (Array Nat) := g1 c15
meta def qG1_20 : Array (Array Nat) := g1 c20
meta def qG1_21 : Array (Array Nat) := g1 c21
meta def qG1_22 : Array (Array Nat) := g1 c22
meta def qG1_23 : Array (Array Nat) := g1 c23

meta def rz : Array Nat := wt gJ pa450010wG5z
meta def kG5 : Array Nat := wt (gensK false) pa450010wG5k
meta def gG5 : Array (Array Nat) := #[kG5, invTab 28 kG5]
meta def gS5 : Array (Array Nat) :=
  #[gJ[0]!, gJ[1]!, conjTab 28 kG5 (invTab 28 kG5) gJ[0]!, conjTab 28 kG5 (invTab 28 kG5) gJ[1]!]
meta def giS5 : Array (Array Nat) := invs gS5
meta def tZJ : Array (Array Nat) := enumT true gJ giJ rz 15

end CertificateChecks.KernelPropA.Gen

end
