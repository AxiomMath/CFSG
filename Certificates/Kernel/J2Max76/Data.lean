module

import CFSG.Certificates.Kernel.Common.JsonGzEval
import CFSG.Certificates.Kernel.Common.Repo
public import CFSG.Monster.B.TwoA.Census.NatCert
public import Std.Data.HashMap

set_option maxRecDepth 400000

#kc_repo #kc_json_gz_eval CertificateChecks.KernelJ2Max76
  "Certificates/Kernel/J2Max76/data/j2max76.json.gz" 72411 12997460557605489323
  (rootLit : Nat) (gensL : List (List Nat)) (nTabsL : Array (Array Nat))
  (orbPts : Array Nat) (orbEdges : Array (Array Nat)) (orbPar : Array Nat) (orbLab : Array Nat)
  (o0Pts : Array Nat) (o0Edges : Array (Array Nat)) (o0Par : Array Nat) (o0Lab : Array Nat)
  (o1Pts : Array Nat) (o1Edges : Array (Array Nat)) (o1Par : Array Nat) (o1Lab : Array Nat)
  (o15Pts : Array Nat) (o15Edges : Array (Array Nat)) (o15Par : Array Nat) (o15Lab : Array Nat)
  (o18Pts : Array Nat) (o18Edges : Array (Array Nat)) (o18Par : Array Nat) (o18Lab : Array Nat)
  (w1 : List Nat) (rp1 : Array Nat)
  (c1Pts : Array Nat) (c1Edges : Array (Array Nat)) (c1Par : Array Nat) (c1Lab : Array Nat)
  (w15 : List Nat) (rp15 : Array Nat)
  (c15Pts : Array Nat) (c15Edges : Array (Array Nat)) (c15Par : Array Nat) (c15Lab : Array Nat)
  (w18 : List Nat) (rp18 : Array Nat)
  (c18Pts : Array Nat) (c18Edges : Array (Array Nat)) (c18Par : Array Nat) (c18Lab : Array Nat)

public section

namespace CertificateChecks.KernelJ2Max76

open CFSG.Monster.B.TwoA.Census

@[expose] def orbLit : NatCert := ⟨orbPts, orbEdges, orbPar, orbLab⟩

@[expose] def o0 : NatCert := ⟨o0Pts, o0Edges, o0Par, o0Lab⟩

@[expose] def o1 : NatCert := ⟨o1Pts, o1Edges, o1Par, o1Lab⟩

@[expose] def o15 : NatCert := ⟨o15Pts, o15Edges, o15Par, o15Lab⟩

@[expose] def o18 : NatCert := ⟨o18Pts, o18Edges, o18Par, o18Lab⟩

@[expose] def orbsLit : List (ℕ × NatCert) := [(0, o0), (1, o1), (15, o15), (18, o18)]

@[expose] def c1 : NatCert := ⟨c1Pts, c1Edges, c1Par, c1Lab⟩

@[expose] def c15 : NatCert := ⟨c15Pts, c15Edges, c15Par, c15Lab⟩

@[expose] def c18 : NatCert := ⟨c18Pts, c18Edges, c18Par, c18Lab⟩

end CertificateChecks.KernelJ2Max76
