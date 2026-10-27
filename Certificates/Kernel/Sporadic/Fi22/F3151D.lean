
module

public import Certificates.Kernel.Sporadic.Fi22.T2068
public import Certificates.Kernel.Sporadic.Fi22.F1OuterT
public import Certificates.Kernel.Sporadic.Fi22.F1OuterS
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.Misc.Perm.HexCmd
public meta import CFSG.Monster.B.Fischer.Fi22CoverCheckInputs
public meta import CFSG.Monster.B.Fischer.Fi22OuterData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi22F2M

open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer

meta def tpPos : Array (Array Nat) :=
  #[(Array.range 3510).map fun p => fi22OuterTPointsNat.idxOf p]

meta def invIdx : Array Nat := Id.run do
  let L := fi22TLevels
  let bs : Array Nat := #[0, 1, 2, 3, 6, 4]
  let mut out : Array Nat := #[]
  for I in [0:131072] do
    let a := I / 128
    let b := I / 4 % 32
    let c := I % 4
    let im := bs.map (tr3 L a b c)
    let moved := (List.range 6).any fun t => im[t]! != bs[t]!
    let sq := (List.range 6).all fun t => tr3 L a b c im[t]! == bs[t]!
    if moved && sq then
      out := out.push I
  return out

meta def posArr : Array Nat := Id.run do
  let inv := invIdx
  let mut pp : Array Nat := Array.replicate 131072 inv.size
  for k in [0:inv.size] do
    pp := pp.set! inv[k]! k
  return pp

meta def posRows : Array (Array Nat) :=
  let pp := posArr
  (Array.range 256).map fun q => pp.extract (512 * q) (512 * q + 512)

meta def treeArrs : Array (Array Nat) := Id.run do
  let L := fi22TLevels
  let base : Array Nat := #[0, 1, 2, 3, 6, 4]
  let inv := invIdx
  let pp := posArr
  let N := inv.size
  let gens := (fi22OuterStrong3510 4).extract 0 9
  let gInv := gens.map (invCand 3510)
  let us := fi22OuterStrong3510 7
  let mut de : Array Nat := Array.replicate N 0
  let mut pr : Array Nat := Array.replicate N 0
  let mut gn : Array Nat := Array.replicate N 0
  let mut vis : Array Bool := Array.replicate N false
  let mut rt : Array Nat := #[]
  let mut q : Array Nat := #[]
  for j in [0:us.size] do
    let I := idx3 L (coords3 3510 L base us[j]!)
    rt := rt.push I
    let k := pp[I]!
    if k < N && !vis[k]! then
      vis := vis.set! k true
      pr := pr.set! k j
      q := q.push k
  let mut h := 0
  for _ in [0:N] do
    if h < q.size then
      let k := q[h]!
      h := h + 1
      let I := inv[k]!
      let xa := prod3 3510 L (I / 128) (I / 4 % 32) (I % 4)
      for s in [0:9] do
        let J := idx3 L (coords3 3510 L base (compA 3510 gens[s]! (compA 3510 xa gInv[s]!)))
        let k' := pp[J]!
        if k' < N && !vis[k']! then
          vis := vis.set! k' true
          de := de.set! k' (de[k]! + 1)
          pr := pr.set! k' k
          gn := gn.set! k' s
          q := q.push k'
  return #[inv, pr, gn, de, rt]

end CertificateChecks.KernelSpor.Fi22F2M

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22F2Q CertificateChecks.KernelSpor.Fi22F2M.tpPos 9

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22F2R CertificateChecks.KernelSpor.Fi22F2M.treeArrs 17

#kmisc_packarrs CertificateChecks.KernelSpor.Fi22F2P CertificateChecks.KernelSpor.Fi22F2M.posRows 12

namespace CertificateChecks.KernelSpor.Fi22F2

open CFSG.KC.Enum CFSG.KS CertificateChecks.KernelSpor
open CertificateChecks.KernelSpor.Fi22LabX (tr O6)

@[expose] noncomputable def g3 (a b c y : Nat) : Nat := tr 0 a (tr 1024 b (tr 1056 c y))

@[expose] noncomputable def gI (I y : Nat) : Nat :=
  g3 (Nat.div I 128) (Nat.mod (Nat.div I 4) 32) (Nat.mod I 4) y

@[expose] noncomputable def bT (t : Nat) : Nat := ([0, 1, 2, 3, 6, 4] : List Nat).getD t 0

@[expose] noncomputable def invB (a b c : Nat) : Bool :=
  bAnd(Bool.not (allN 6 fun t => Nat.beq (g3 a b c (bT t)) (bT t)),
    allN 6 fun t => Nat.beq (g3 a b c (g3 a b c (bT t))) (bT t))

@[expose] noncomputable def U (j : Nat) : Nat := Fi22OutT.L (Nat.add 39 j)

@[expose] noncomputable def H (j : Nat) : Nat := Fi22OutT.L (Nat.add 93 j)

@[expose] noncomputable def R (k : Nat) : Nat := pg 12 (mask 12) (Fi22OTP.F 0) k

@[expose] noncomputable def Qf (p : Nat) : Nat := pg 9 (mask 9) (Fi22F2Q 0) p

@[expose] noncomputable def tpK : Bool :=
  bAnd(allN 256 (fun k => bAnd(Nat.blt (R k) 3510, Nat.beq (Qf (R k)) k)),
    bAnd(allN 3510 (fun p => bIf(Nat.blt (Qf p) 256, Nat.beq (R (Qf p)) p, true)),
      allN 9 (fun s => allN 3510 (fun p => strictB (pg 12 (mask 12) (Fi22X.TS s) p) fun q =>
        bIf(Nat.blt (Qf p) 256, Nat.blt (Qf q) 256, Bool.not (Nat.blt (Qf q) 256))))))

@[expose] noncomputable def movB (a b c : Nat) : Bool :=
  Bool.not (allN 256 fun k => Nat.beq (g3 a b c (R k)) (R k))

@[expose] noncomputable def PPf (I : Nat) : Nat :=
  pg 12 (mask 12) (Fi22F2P (Nat.div I 512)) (Nat.mod I 512)

@[expose] noncomputable def RF (f k : Nat) : Nat := pg 17 (mask 17) (Fi22F2R f) k

@[expose] noncomputable def SV (k : Nat) : Nat := RF 0 k
@[expose] noncomputable def PR (k : Nat) : Nat := RF 1 k
@[expose] noncomputable def GN (k : Nat) : Nat := RF 2 k
@[expose] noncomputable def DE (k : Nat) : Nat := RF 3 k
@[expose] noncomputable def RT (j : Nat) : Nat := RF 4 j

@[expose] noncomputable def scanRow (I : Nat) : Bool :=
  strictB (Nat.div I 128) fun a => strictB (Nat.mod (Nat.div I 4) 32) fun b =>
    strictB (Nat.mod I 4) fun c =>
      bAnd(strictB (PPf I) fun k =>
          bIf(invB a b c, bAnd(Nat.blt k 3263, Nat.beq (SV k) I), Nat.beq k 3263),
        bIf(Nat.beq I 0, true, movB a b c))

@[expose] noncomputable def scanSl (q : Nat) : Bool :=
  allN 512 fun d => scanRow (Nat.add (Nat.mul q 512) d)

@[expose] noncomputable def conjB (s I J : Nat) : Bool :=
  allN 6 fun t => Nat.beq (gI I (bT t))
    (pg 12 (mask 12) (Fi22X.TS s) (gI J (pg 12 (mask 12) (Fi22TC.SI s) (bT t))))

@[expose] noncomputable def svRow (k : Nat) : Bool :=
  strictB (SV k) fun I => bAnd(Nat.blt I 131072, Nat.beq (PPf I) k)

@[expose] noncomputable def treeRow (k : Nat) : Bool :=
  strictB (SV k) fun I => strictB (PR k) fun p =>
    bIf(Nat.beq (DE k) 0, bAnd(Nat.blt p 54, Nat.beq (RT p) I),
      bAnd(Nat.blt p 3263, bAnd(Nat.blt (DE p) (DE k),
        strictB (GN k) fun s => bAnd(Nat.blt s 9, conjB s I (SV p)))))

@[expose] noncomputable def treeSl (q : Nat) : Bool :=
  allN 512 fun d => strictB (Nat.add (Nat.mul q 512) d) fun k =>
    bIf(Nat.blt k 3263, bAnd(svRow k, treeRow k), true)

@[expose] noncomputable def rootRow (j : Nat) : Bool :=
  strictB (RT j) fun I => bAnd(Nat.blt I 131072, bAnd(Nat.blt (PPf I) 3263,
    allN 3510 fun p => Nat.beq (pg 12 (mask 12) (U j) p) (gI I p)))

@[expose] noncomputable def rootSl (q : Nat) : Bool :=
  allN 6 fun d => rootRow (Nat.add (Nat.mul q 6) d)

@[expose] noncomputable def hRow (j : Nat) : Bool :=
  bAnd(Fi22X.cn (H j), bAnd(Fi22X.siftP (H j), bAnd(Fi22X.cn (U j),
    strictB (Fi22X.c (H j) (U j)) fun P =>
      bIf(Nat.beq P (Fi22X.c (O6 0) (H j)), true,
        bIf(Nat.beq P (Fi22X.c (O6 1) (H j)), true,
          Nat.beq P (Fi22X.c (O6 2) (H j)))))))

@[expose] noncomputable def hSl (q : Nat) : Bool := allN 6 fun d => hRow (Nat.add (Nat.mul q 6) d)

end CertificateChecks.KernelSpor.Fi22F2

end
