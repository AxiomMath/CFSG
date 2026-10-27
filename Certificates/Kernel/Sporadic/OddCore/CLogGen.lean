module

public import Init

public section

namespace CertificateChecks.KernelSpor.CLogGen

structure Log where
  fd : Array Nat
  fw : Array Nat
  fs : Array Nat
  sd : Array Nat
  dt : Array Nat
  nc : Nat
  fin : Nat

structure St where
  tab : Array Nat
  tst : Array Nat
  par : Array Nat
  pf : Array Nat
  nxt : Nat
  fd : Array Nat
  fw : Array Nat
  fs : Array Nat
  sd : Array Nat
  dt : Array Nat
  dedq : Array (Nat × Nat)
  cq : Array (Nat × Nat × Nat)

variable (L : Nat) (rels : Array (Array Nat))

meta def word (r k o : Nat) : Array Nat :=
  let w := rels[r]!
  let w := if o == 0 then w else w.reverse.map (· ^^^ 1)
  let k := k % w.size
  w.extract k w.size ++ w.extract 0 k

meta def fact (s : St) (kind a x b W : Nat) (steps : Array Nat) : St × Nat :=
  let row := kind ||| (a <<< 2) ||| (x <<< 16) ||| (b <<< 20)
  let s' : St := { s with
    fd := s.fd.push row
    fw := s.fw.push W
    fs := s.fs.push s.sd.size
    sd := s.sd ++ steps }
  (s', s.fd.size)

meta partial def root (s : St) (c : Nat) (acc : Array Nat := #[]) : Nat × Array Nat :=
  if s.par[c]! == c then (c, acc) else root s s.par[c]! (acc.push (s.pf[c]! * 2))

meta def flip (st : Array Nat) : Array Nat := st.reverse.map (· ^^^ 1)

meta def setent (s : St) (c x e st : Nat) : St :=
  { s with
    tab := (s.tab.set! (c * L + x) e).set! (e * L + (x ^^^ 1)) c
    tst := (s.tst.set! (c * L + x) st).set! (e * L + (x ^^^ 1)) (st ^^^ 1)
    dedq := s.dedq.push (c, x) }

meta def entryOrCoinc (s : St) (c x e f : Nat) : St :=
  let g := s.tab[c * L + x]!
  if g != 0 then
    if g != e then
      let (s, q) := fact s 3 g x e 2 #[s.tst[c * L + x]! ^^^ 1, f * 2]
      { s with cq := s.cq.push (g, e, q) }
    else s
  else
    let g := s.tab[e * L + (x ^^^ 1)]!
    if g != 0 then
      if g != c then
        let (s, q) := fact s 3 g (x ^^^ 1) c 2 #[s.tst[e * L + (x ^^^ 1)]! ^^^ 1, f * 2 + 1]
        { s with cq := s.cq.push (g, c, q) }
      else s
    else setent L s c x e (f * 2)

meta partial def coinc (s : St) : St :=
  match s.cq.back? with
  | none => s
  | some (a, b, q) =>
    let s := { s with cq := s.cq.pop }
    let (ra, pa) := root s a
    let (rb, pb) := root s b
    if ra == rb then coinc s else
    let (l, d, steps) := if ra < rb then (ra, rb, flip pb ++ #[q * 2 + 1] ++ pa)
      else (rb, ra, flip pa ++ #[q * 2] ++ pb)
    let (s, e2) := fact s 3 d 0 l 3 steps
    let s := { s with par := s.par.set! d l, pf := s.pf.set! d e2 }
    let s := (List.range L).foldl (fun s x =>
      let e := s.tab[d * L + x]!
      if e == 0 then s else
      let st := s.tst[d * L + x]!
      let s := { s with tab := s.tab.set! (d * L + x) 0 }
      let s := if s.tab[e * L + (x ^^^ 1)]! == d then
        { s with tab := s.tab.set! (e * L + (x ^^^ 1)) 0 } else s
      let (re, pe) := root s e
      let (s, f) := fact s 2 l x re 3 (#[e2 * 2 + 1, st] ++ pe)
      entryOrCoinc L s l x re f) s
    coinc s

meta partial def walkF (s : St) (w : Array Nat) (pos i : Nat) (st : Array Nat) :
    Nat × Array Nat × Nat :=
  if i < w.size && s.tab[pos * L + w[i]!]! != 0 then
    let e := s.tab[pos * L + w[i]!]!
    let (r, p) := root s e
    walkF s w r (i + 1) (st.push (s.tst[pos * L + w[i]!]!) ++ p)
  else (pos, st, i)

meta partial def walkB (s : St) (w : Array Nat) (i b j : Nat) (B : Array Nat) :
    Nat × Array Nat × Nat :=
  if j > i && s.tab[b * L + (w[j - 1]! ^^^ 1)]! != 0 then
    let e := s.tab[b * L + (w[j - 1]! ^^^ 1)]!
    let (re, pe) := root s e
    walkB s w i re (j - 1) (flip pe ++ #[s.tst[b * L + (w[j - 1]! ^^^ 1)]! ^^^ 1] ++ B)
  else (b, B, j)

meta def scan (s : St) (c r k0 o : Nat) (define : Bool) : St × Bool :=
  let w := word rels r k0 o
  let n := w.size
  let (f, F, i) := walkF L s w c 0 #[]
  if i == n then
    if f != c then
      let (s, q) := fact s 3 c 0 f (o ||| (k0 <<< 2) ||| (r <<< 8)) F
      (coinc L { s with cq := s.cq.push (c, f, q) }, true)
    else (s, true)
  else
  let (b, B, j) := walkB L s w i c n #[]
  let k := (k0 + i) % n
  let W := o ||| (k <<< 2) ||| (r <<< 8)
  if j == i then
    if f != b then
      let (s, q) := fact s 3 b 0 f W (B ++ F)
      (coinc L { s with cq := s.cq.push (b, f, q) }, true)
    else (s, true)
  else if j == i + 1 then
    let (s, q) := fact s 2 f w[i]! b W (B ++ F)
    (coinc L (entryOrCoinc L s f w[i]! b q), true)
  else if define then
    let m := s.nxt
    let (s, q) := fact s 0 f w[i]! m 3 #[]
    let s := { s with nxt := m + 1, par := s.par.set! m m, dt := s.dt.set! m q }
    (setent L s f w[i]! m (q * 2), false)
  else (s, false)

meta def rots : Array (Array (Nat × Nat × Nat)) := Id.run do
  let mut out : Array (Array (Nat × Nat × Nat)) := Array.replicate L #[]
  let mut seen : Array (Array Nat) := #[]
  for r in [0:rels.size] do
    for o in [0:2] do
      for k in [0:rels[r]!.size] do
        let w := word rels r k o
        if !seen.contains w then
          seen := seen.push w
          out := out.modify w[0]! (·.push (r, k, o))
  return out

meta partial def process (R : Array (Array (Nat × Nat × Nat))) (s : St) : St :=
  match s.dedq.back? with
  | none => s
  | some (c, x) =>
    let s := { s with dedq := s.dedq.pop }
    if s.tab[c * L + x]! == 0 || s.par[c]! != c then process R s else
    let s := R[x]!.foldl (fun s (r, k, o) =>
      if s.par[c]! != c then s else (scan L rels s c r k o false).1) s
    process R s

meta partial def fill (R : Array (Array (Nat × Nat × Nat))) (s : St) (c r : Nat) : St :=
  if s.par[c]! != c then s else
  let (s, done) := scan L rels s c r 0 0 true
  let s := process L rels R s
  if done then s else fill R s c r

meta partial def hlt (R : Array (Array (Nat × Nat × Nat))) (s : St) (c : Nat) : St :=
  if c < s.nxt then
    let s := if s.par[c]! == c then
      (List.range rels.size).foldl (fun s r => fill L rels R s c r) s else s
    hlt R s (c + 1)
  else s

meta def run (subs : List Nat) (z cap : Nat) : Log :=
  let R := rots L rels
  let s0 : St := {
    tab := Array.replicate (cap * L) 0
    tst := Array.replicate (cap * L) 0
    par := Array.range cap
    pf := Array.replicate cap 0
    nxt := 2
    fd := #[]
    fw := #[]
    fs := #[]
    sd := #[]
    dt := Array.replicate cap 0
    dedq := #[]
    cq := #[] }
  let s := subs.foldl (fun s y =>
    let (s, f) := fact s 1 1 y 1 3 #[]
    process L rels R (coinc L (entryOrCoinc L s 1 y 1 f))) s0
  let s := hlt L rels R s 1
  let e := s.tab[L + z]!
  let (_, pe) := root s e
  let (s, fin) := fact s 2 1 z 1 3 (#[s.tst[L + z]!] ++ pe)
  { fd := s.fd
    fw := s.fw
    fs := s.fs.push s.sd.size
    sd := s.sd
    dt := s.dt.extract 0 s.nxt
    nc := s.nxt
    fin := fin }

end CertificateChecks.KernelSpor.CLogGen

end
