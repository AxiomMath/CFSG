module

public meta import Certificates.Kernel.Sporadic.OddCore.CLogGen
public import Certificates.Kernel.Sporadic.OddCore.CLogGen

public section

namespace CertificateChecks.KernelSpor.CLogGen

meta def runZ (L : Nat) (rels : Array (Array Nat)) (subs zs : List Nat) (cap : Nat) :
    Log × Array Nat :=
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
  let (s, fins) := zs.foldl (fun (s, fins) z =>
    let e := s.tab[L + z]!
    let (_, pe) := root s e
    let (s, fin) := fact s 2 1 z 1 3 (#[s.tst[L + z]!] ++ pe)
    (s, fins.push fin)) (s, #[])
  ({ fd := s.fd
     fw := s.fw
     fs := s.fs.push s.sd.size
     sd := s.sd
     dt := s.dt.extract 0 s.nxt
     nc := s.nxt
     fin := fins[0]! }, fins)

end CertificateChecks.KernelSpor.CLogGen

end
