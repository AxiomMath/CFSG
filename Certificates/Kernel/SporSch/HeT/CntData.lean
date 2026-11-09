module

public import Certificates.Kernel.SporSch.HeT.Out2116
public import Certificates.Data.Kernel.SporSch.HeSrch
public import CFSG.Sporadic.HeldB.InnerClassCheckInputs
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import Certificates.Kernel.Sporadic.RowsWCmd
public meta import CFSG.Sporadic.HeldB.InnerClassCheckInputs
public meta import CFSG.Sporadic.HeldB.OuterArithCheck
public meta import CFSG.Sporadic.HeldB.HeBlocks
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Data.Kernel.Spor.Row

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeCn

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.HeldB
open CFSG.Certificates.Native

meta def lv : Array Level := heLevels

meta def ev (nf : Array Nat) (x : Nat) : Nat := evR (nfWord lv nf) x

meta def ys : Array (Array Nat) := #[heGen 0, heT1cArr, hePowA heAutRArr 5]

meta def cOf (y : Array Nat) : Array Nat := Id.run do
  let L0 := lv[0]!
  let L1 := lv[1]!
  let L2 := lv[2]!
  for k0 in [0:L0.pts.size] do
    let nf0 := #[k0, 0, 0, 0, 0]
    let p := ev nf0 0
    if y[p]! == p then
      for k1 in [0:L1.pts.size] do
        for k2 in [0:L2.pts.size] do
          let nf := #[k0, k1, k2, 0, 0]
          if y[ev nf 1]! == ev nf 2 then
            return nf
  return #[0, 0, 0, 0, 0]

meta def packNF (nf : Array Nat) : Nat :=
  (List.range nf.size).foldl (fun acc i => acc ||| (nf[i]! <<< (16 * i))) 0

meta def xOf (y : Array Nat) : Array Nat :=
  let nf := cOf y
  let c := (Array.range 8330).map (ev nf)
  let ci := invCand 8330 c
  (Array.range 8330).map fun x => ci.getD (y.getD (c.getD x 0) 0) 0

meta def srchCnt (X Y : Array Nat) (lo len : Nat) : Nat := Id.run do
  let L0 := lv[0]!
  let L1 := lv[1]!
  let L2 := lv[2]!
  let L3 := lv[3]!
  let L4 := lv[4]!
  let mut s := 0
  for k0 in [lo:lo + len] do
    let t0 := L0.tr[k0]!
    let t0i := L0.trInv[k0]!
    let p0 := t0[0]!
    if Y[p0]! == p0 then
      for k1 in [0:L1.pts.size] do
        let t1 := L1.tr[k1]!
        let t1i := L1.trInv[k1]!
        let q1 := t1[1]!
        let q := t0[q1]!
        let yq := Y[q]!
        let v0 := t0i[yq]!
        let v := t1i[v0]!
        let k2 := L2.pos[v]!
        if k2 < L2.pts.size then
          for k3 in [0:L3.pts.size] do
            for k4 in [0:L4.pts.size] do
              let nf := #[k0, k1, k2, k3, k4]
              if [0, 1, 2, 3, 4].all (fun b =>
                  let l := ev nf X[b]!
                  let r := ev nf b
                  l == Y[r]!) then
                s := s + 1
  return s

meta def solsAt (X Y : Array Nat) (k0 lim : Nat) : Array (Array Nat) := Id.run do
  let L1 := lv[1]!
  let L2 := lv[2]!
  let L3 := lv[3]!
  let L4 := lv[4]!
  let t0 := lv[0]!.tr[k0]!
  let t0i := lv[0]!.trInv[k0]!
  let p0 := t0[0]!
  let mut out : Array (Array Nat) := #[]
  if Y[p0]! == p0 then
    for k1 in [0:L1.pts.size] do
      let t1 := L1.tr[k1]!
      let t1i := L1.trInv[k1]!
      let q := t0[t1[1]!]!
      let v := t1i[t0i[Y[q]!]!]!
      let k2 := L2.pos[v]!
      if k2 < L2.pts.size then
        let t2 := L2.tr[k2]!
        for k3 in [0:L3.pts.size] do
          let t3 := L3.tr[k3]!
          for k4 in [0:L4.pts.size] do
            let t4 := L4.tr[k4]!
            let g := fun (b : Nat) => t0[t1[t2[t3[t4[b]!]!]!]!]!
            if out.size < lim && [0, 1, 2, 3, 4].all (fun b => g X[b]! == Y[g b]!) then
              out := out.push #[k0, k1, k2, k3, k4]
  return out

meta def k1Cnt (Y : Array Nat) (k0 : Nat) : Nat := Id.run do
  let L1 := lv[1]!
  let L2 := lv[2]!
  let t0 := lv[0]!.tr[k0]!
  let t0i := lv[0]!.trInv[k0]!
  let mut c := 0
  for k1 in [0:L1.pts.size] do
    let t1 := L1.tr[k1]!
    let t1i := L1.trInv[k1]!
    let q := t0[t1[1]!]!
    if L2.pos[t1i[t0i[Y[q]!]!]!]! < L2.pts.size then
      c := c + 1
  return c

meta def nfArrM (nf : Array Nat) : Array Nat :=
  let ts := (List.range 5).map fun i => lv[i]!.tr[nf[i]!]!
  (Array.range 8330).map fun b => ts.foldr (fun t a => t[a]!) b

meta def siftM (h : Array Nat) : Array Nat := Id.run do
  let mut g := h
  let mut nf : Array Nat := #[]
  for i in [0:5] do
    let L := lv[i]!
    let k := L.pos[g[i]!]!
    nf := nf.push k
    let ti := L.trInv[k]!
    g := g.map fun a => ti[a]!
  return nf

meta def p0M (k : Nat) : Nat := (lv[0]!.tr[k]!)[0]!

meta def orbRZ (X Y : Array Nat) : Array Nat × Array Nat := Id.run do
  let fixK := (Array.range 8330).filter fun k => Y[p0M k]! == p0M k
  let first := fixK.map fun k => (k, solsAt X Y k 1)
  let nz := first.filter fun e => e.2.size > 0
  let mut R := Array.range 8330
  let mut Z := Array.replicate 8330 0
  if nz.size == 0 then return (R, Z)
  let fib := solsAt X Y nz[0]!.1 1000000
  let gsi := invCand 8330 (nfArrM fib[0]!)
  let comp := fun (a b : Array Nat) => (Array.range 8330).map fun i => a[b[i]!]!
  let gens := (nz.map fun e => comp (nfArrM e.2[0]!) gsi) ++ (fib.map fun f => comp (nfArrM f) gsi)
  let mut seen : Array Bool := Array.replicate 8330 false
  for k in fixK do
    let p := p0M k
    if !seen[p]! then
      seen := seen.set! p true
      let mut q : Array (Nat × Array Nat) := #[(p, Array.range 8330)]
      let mut i := 0
      while i < q.size do
        let (a, h) := q[i]!
        i := i + 1
        for g in gens do
          let b := g[a]!
          if !seen[b]! then
            seen := seen.set! b true
            q := q.push (b, comp g h)
      let mut best := 0
      let mut bestC := 1000000
      for j in [0:q.size] do
        let c := k1Cnt Y (lv[0]!.pos[q[j]!.1]!)
        if c < bestC then
          best := j
          bestC := c
      let r := lv[0]!.pos[q[best]!.1]!
      let hri := invCand 8330 q[best]!.2
      for j in [0:q.size] do
        if j != best then
          let kb := lv[0]!.pos[q[j]!.1]!
          R := R.set! kb r
          Z := Z.set! kb (packNF (siftM (comp q[j]!.2 hri)))
  return (R, Z)

meta def twCnt (U : Array Nat) (lo len : Nat) : Nat := Id.run do
  let L2 := lv[2]!
  let L3 := lv[3]!
  let L4 := lv[4]!
  let mut s := 0
  for k1 in [lo:lo + len] do
    for k2 in [0:L2.pts.size] do
      for k3 in [0:L3.pts.size] do
        for k4 in [0:L4.pts.size] do
          let nf := #[0, k1, k2, k3, k4]
          if [0, 1, 2, 3, 4].all (fun b =>
              let a := ev nf b
              let c := ev nf U[a]!
              U[c]! == b) then
            s := s + 1
  return s

meta def heCnRows : Array (Array Nat) :=
  ((include_str "CntData.txt").splitOn "\n").toArray.map fun l =>
    ((l.splitOn " ").filterMap String.toNat?).toArray

meta def xaM : Array Nat := heCnRows[0]!
meta def xtM : Array Nat := heCnRows[1]!
meta def xuM : Array Nat := heCnRows[2]!
meta def vaM : Array Nat := heCnRows[3]!
meta def vtM : Array Nat := heCnRows[4]!
meta def vuM : Array Nat := heCnRows[5]!
meta def raM : Array Nat := heCnRows[6]!
meta def zaM : Array Nat := heCnRows[7]!
meta def rtM : Array Nat := heCnRows[8]!
meta def ztM : Array Nat := heCnRows[9]!
meta def ruM : Array Nat := heCnRows[10]!
meta def zuM : Array Nat := heCnRows[11]!
meta def rs0M : Array Nat := heCnRows[12]!
meta def zs0M : Array Nat := heCnRows[13]!
meta def vs0M : Array Nat := heCnRows[14]!
meta def rs1M : Array Nat := heCnRows[15]!
meta def zs1M : Array Nat := heCnRows[16]!
meta def vs1M : Array Nat := heCnRows[17]!

meta def permsM : Array (Array Nat) :=
  #[heT1Arr, heT1cArr, ys[2]!, xaM, invCand 8330 xaM, xtM, invCand 8330 xtM, xuM, invCand 8330 xuM]

meta def natsM : List Nat := heCnRows[18]!.toList

meta def orbS (U : Array Nat) : Array Nat × Array Nat × Array Nat := Id.run do
  let n1 := lv[1]!.pts.size
  let p1 := fun (k : Nat) => (lv[1]!.tr[k]!)[1]!
  let mut idx : Array Nat := Array.replicate 8330 n1
  for k in [0:n1] do
    idx := idx.set! (U[p1 k]!) k
  let gens := lv[2]!.tr ++ lv[3]!.tr ++ lv[4]!.tr
  let comp := fun (a b : Array Nat) => (Array.range 8330).map fun i => a[b[i]!]!
  let mut seen : Array Bool := Array.replicate n1 false
  let mut R := Array.range n1
  let mut Z := Array.replicate n1 0
  for k in [0:n1] do
    if !seen[k]! then
      seen := seen.set! k true
      let mut q : Array (Nat × Array Nat) := #[(k, Array.range 8330)]
      let mut i := 0
      while i < q.size do
        let (a, h) := q[i]!
        i := i + 1
        for g in gens do
          let b := idx[g[U[p1 a]!]!]!
          if b < n1 && !seen[b]! then
            seen := seen.set! b true
            q := q.push (b, comp g h)
      for j in [1:q.size] do
        R := R.set! q[j]!.1 k
        Z := Z.set! q[j]!.1 (packNF (siftM q[j]!.2))
  return (R, Z, (Array.range n1).map fun k => twCnt U k 1)

meta def vOf (i : Nat) : Array Nat :=
  let x := xOf ys[i]!
  let y := ys[i]!
  (Array.range 8330).map fun k0 => srchCnt x y k0 1

meta def yaM : Array Nat := ys[0]!
meta def ytM : Array Nat := ys[1]!
meta def yuM : Array Nat := ys[2]!

end CertificateChecks.KernelSporSch.HeCn

#kss_perms CertificateChecks.KernelSporSch.HeCnP 14 CertificateChecks.KernelSporSch.HeCn.permsM

#krowsw CertificateChecks.KernelSporSch.HeCnRXA 14 CertificateChecks.KernelSporSch.HeCn.xaM
#krowsw CertificateChecks.KernelSporSch.HeCnRXT 14 CertificateChecks.KernelSporSch.HeCn.xtM
#krowsw CertificateChecks.KernelSporSch.HeCnRXU 14 CertificateChecks.KernelSporSch.HeCn.xuM
#krowsw CertificateChecks.KernelSporSch.HeCnRYA 14 CertificateChecks.KernelSporSch.HeCn.yaM
#krowsw CertificateChecks.KernelSporSch.HeCnRYT 14 CertificateChecks.KernelSporSch.HeCn.ytM
#krowsw CertificateChecks.KernelSporSch.HeCnRYU 14 CertificateChecks.KernelSporSch.HeCn.yuM
#krowsw CertificateChecks.KernelSporSch.HeCnVA 12 CertificateChecks.KernelSporSch.HeCn.vaM
#krowsw CertificateChecks.KernelSporSch.HeCnVT 12 CertificateChecks.KernelSporSch.HeCn.vtM
#krowsw CertificateChecks.KernelSporSch.HeCnVU 12 CertificateChecks.KernelSporSch.HeCn.vuM
#krowsw CertificateChecks.KernelSporSch.HeCnRA 14 CertificateChecks.KernelSporSch.HeCn.raM
#krowsw CertificateChecks.KernelSporSch.HeCnZA 80 CertificateChecks.KernelSporSch.HeCn.zaM
#krowsw CertificateChecks.KernelSporSch.HeCnRT 14 CertificateChecks.KernelSporSch.HeCn.rtM
#krowsw CertificateChecks.KernelSporSch.HeCnZT 80 CertificateChecks.KernelSporSch.HeCn.ztM
#krowsw CertificateChecks.KernelSporSch.HeCnRU 14 CertificateChecks.KernelSporSch.HeCn.ruM
#krowsw CertificateChecks.KernelSporSch.HeCnZU 80 CertificateChecks.KernelSporSch.HeCn.zuM
#krowsw CertificateChecks.KernelSporSch.HeCnRS0 14 CertificateChecks.KernelSporSch.HeCn.rs0M
#krowsw CertificateChecks.KernelSporSch.HeCnZS0 80 CertificateChecks.KernelSporSch.HeCn.zs0M
#krowsw CertificateChecks.KernelSporSch.HeCnVS0 12 CertificateChecks.KernelSporSch.HeCn.vs0M
#krowsw CertificateChecks.KernelSporSch.HeCnRS1 14 CertificateChecks.KernelSporSch.HeCn.rs1M
#krowsw CertificateChecks.KernelSporSch.HeCnZS1 80 CertificateChecks.KernelSporSch.HeCn.zs1M
#krowsw CertificateChecks.KernelSporSch.HeCnVS1 12 CertificateChecks.KernelSporSch.HeCn.vs1M

#knatlist CertificateChecks.KernelSporSch.HeCn.nats CertificateChecks.KernelSporSch.HeCn.natsM

namespace CertificateChecks.KernelSporSch.HeCn

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch CertificateChecks.KernelSporSch
open CertificateChecks.KernelSpor CFSG.Sporadic.HeldB

@[expose] noncomputable def T1 : Nat := HeCnP 0
@[expose] noncomputable def T1C : Nat := HeCnP 1
@[expose] noncomputable def U5 : Nat := HeCnP 2
@[expose] noncomputable def XA : Nat := HeCnP 3
@[expose] noncomputable def XAI : Nat := HeCnP 4
@[expose] noncomputable def XT : Nat := HeCnP 5
@[expose] noncomputable def XTI : Nat := HeCnP 6
@[expose] noncomputable def XU : Nat := HeCnP 7
@[expose] noncomputable def XUI : Nat := HeCnP 8

@[expose] noncomputable def FA : Nat := nats.getD 0 0
@[expose] noncomputable def FT : Nat := nats.getD 1 0
@[expose] noncomputable def FU : Nat := nats.getD 2 0

@[expose] noncomputable def VA (k : Nat) : Nat := CFSG.KS.Row.rg 12 (mask 12) HeCnVA 0 k
@[expose] noncomputable def VT (k : Nat) : Nat := CFSG.KS.Row.rg 12 (mask 12) HeCnVT 0 k
@[expose] noncomputable def VU (k : Nat) : Nat := CFSG.KS.Row.rg 12 (mask 12) HeCnVU 0 k


@[expose] noncomputable def pm (P x : Nat) : Nat := pg 14 (mask 14) P x

@[expose] noncomputable def pmR (T : Nat → Nat) (x : Nat) : Nat := CFSG.KS.Row.rg 14 (mask 14) T 0 x

@[expose] noncomputable def rbAll (T : Nat → Nat) (P : Nat) : Bool :=
  allN 8330 (fun x => Nat.beq (pmR T x) (pm P x))

@[expose] noncomputable def cjB (X Y : Nat → Nat) (F s : Nat) : Bool :=
  allN 170 (fun j => strictB (Nat.add (Nat.mul s 170) j) (fun x =>
    Nat.beq (HeTc.nfp F (pmR X x)) (pmR Y (HeTc.nfp F x))))

@[expose] noncomputable def p1K (k : Nat) : Nat := rpt 14 (mask 14) (HeC.LR 1) k

@[expose] noncomputable def orSt (U V R Z : Nat → Nat) (k : Nat) : Bool :=
  strictB (R k) (fun r => Bool.rec (motive := fun _ => Bool)
    (strictB (Z k) (fun F => bAnd(Nat.blt r 4480, bAnd(Nat.beq (R r) r,
      bAnd(Nat.beq (V k) (V r), bAnd(Nat.blt (p1K r) 8330, bAnd(Nat.blt (p1K k) 8330,
        bAnd(nfValidK 5 HeC.LR F, bAnd(Nat.beq (HeTc.nfp F 0) 0, bAnd(Nat.beq (HeTc.nfp F 1) 1,
          Nat.beq (HeTc.nfp F (U (p1K r))) (U (p1K k))))))))))))
    (Nat.beq (cnt234 HeC.LR (twK 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT heBase U) 0 k) (V k))
    (Nat.beq r k))

@[expose] noncomputable def orSB (U V R Z : Nat → Nat) (s : Nat) : Bool :=
  allN 128 (fun j => orSt U V R Z (Nat.add (Nat.mul s 128) j))

@[expose] noncomputable def cjA (s : Nat) : Bool := cjB HeCnRXA HeCnRYA FA s
@[expose] noncomputable def cjT (s : Nat) : Bool := cjB HeCnRXT HeCnRYT FT s
@[expose] noncomputable def cjU (s : Nat) : Bool := cjB HeCnRXU HeCnRYU FU s
@[expose] noncomputable def p0K (k : Nat) : Nat := trPtT 14 HeTb.NR HeTb.NR HeTb.LT HeTb.PT (nat_lit 0) k 0

@[expose] noncomputable def pcSkip (P : Bool) (X Y V : Nat → Nat) (k : Nat) : Bool :=
  bAnd(P, bAnd(Nat.beq (V k) 0, bAnd(Nat.beq (pmR Y (p0K k)) (p0K k),
    bIf(Nat.beq (srchPC 14 9 HeTb.NR HeTb.NR HeTb.LT HeTb.PT HeTb.QT HeC.LR (pmR Y) k)
      (srchPC 14 9 HeTb.NR HeTb.NR HeTb.LT HeTb.PT HeTb.QT HeC.LR (pmR X) 0), false, true))))

@[expose] noncomputable def orAt (P : Bool) (X Y V R Z : Nat → Nat) (E k : Nat) : Bool :=
  strictB (R k) (fun r => Bool.rec (motive := fun _ => Bool)
    (strictB (Z k) (fun F => bAnd(Nat.blt r 8330, bAnd(Nat.beq (R r) r,
      bAnd(Nat.beq (V k) (V r), bAnd(Nat.blt (p0K r) 8330, bAnd(nfValidK 5 HeC.LR F,
        bAnd(Nat.beq (HeTc.nfp F (p0K r)) (p0K k),
          eqOnL heBase (fun b => HeTc.nfp F (pmR Y b)) (fun b => pmR Y (HeTc.nfp F b))))))))))
    (Bool.rec (motive := fun _ => Bool)
      (bIf(pcSkip P X Y V k, true,
        Nat.beq (srchAAt 14 9 HeTb.NR HeTb.NR HeTb.LT HeTb.PT HeTb.QT HeC.LR heBase 0 (pmR X) (pmR Y)
          k) (V k)))
      (Nat.beq (V k) 0) (Nat.beq k E))
    (Nat.beq r k))

@[expose] noncomputable def orB (P : Bool) (X Y V R Z : Nat → Nat) (E s : Nat) : Bool :=
  allN 170 (fun j => orAt P X Y V R Z E (Nat.add (Nat.mul s 170) j))

@[expose] noncomputable def RA (k : Nat) : Nat := CFSG.KS.Row.rg 14 (mask 14) HeCnRA 0 k
@[expose] noncomputable def ZA (k : Nat) : Nat := CFSG.KS.Row.rg 80 (mask 80) HeCnZA 0 k
@[expose] noncomputable def RT (k : Nat) : Nat := CFSG.KS.Row.rg 14 (mask 14) HeCnRT 0 k
@[expose] noncomputable def ZT (k : Nat) : Nat := CFSG.KS.Row.rg 80 (mask 80) HeCnZT 0 k
@[expose] noncomputable def RU (k : Nat) : Nat := CFSG.KS.Row.rg 14 (mask 14) HeCnRU 0 k
@[expose] noncomputable def ZU (k : Nat) : Nat := CFSG.KS.Row.rg 80 (mask 80) HeCnZU 0 k
@[expose] noncomputable def orA (s : Nat) : Bool := orB false HeCnRXA HeCnRYA VA RA ZA 598 s
@[expose] noncomputable def orT (s : Nat) : Bool := orB false HeCnRXT HeCnRYT VT RT ZT 8330 s
@[expose] noncomputable def orU (s : Nat) : Bool := orB true HeCnRXU HeCnRYU VU RU ZU 8330 s

@[expose] noncomputable def RS0 (k : Nat) : Nat := CFSG.KS.Row.rg 14 (mask 14) HeCnRS0 0 k
@[expose] noncomputable def ZS0 (k : Nat) : Nat := CFSG.KS.Row.rg 80 (mask 80) HeCnZS0 0 k
@[expose] noncomputable def VS0 (k : Nat) : Nat := CFSG.KS.Row.rg 12 (mask 12) HeCnVS0 0 k
@[expose] noncomputable def RS1 (k : Nat) : Nat := CFSG.KS.Row.rg 14 (mask 14) HeCnRS1 0 k
@[expose] noncomputable def ZS1 (k : Nat) : Nat := CFSG.KS.Row.rg 80 (mask 80) HeCnZS1 0 k
@[expose] noncomputable def VS1 (k : Nat) : Nat := CFSG.KS.Row.rg 12 (mask 12) HeCnVS1 0 k

@[expose] noncomputable def s0 (s : Nat) : Bool := orSB (fun b => b) VS0 RS0 ZS0 s
@[expose] noncomputable def s1 (s : Nat) : Bool := orSB (pmR HeCnRYU) VS1 RS1 ZS1 s

end CertificateChecks.KernelSporSch.HeCn

end
