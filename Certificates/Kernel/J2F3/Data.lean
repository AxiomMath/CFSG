module

public import Certificates.Kernel.Sporadic.OddCore.J2Cn
public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Data.Kernel.SporSch.BasePtWit
public import Certificates.Data.Odd87F3J2
public meta import Certificates.Kernel.Sporadic.OddCore.J2Cn
public meta import Certificates.Data.Odd87F3J2

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2F3

open CertificateChecks.KernelSpor.J2Cn Certificates.Odd87F3.J2

meta def cmpM (a b : Array Nat) : Array Nat := Array.ofFn (n := 315) fun i => a[b[i]!]!

meta def invM (a : Array Nat) : Array Nat := Id.run do
  let mut r := Array.replicate 315 0
  for i in [0:315] do
    r := r.set! a[i]! i
  return r

meta def evM (gs : List Nat) (wd : List Int) : Array Nat :=
  wd.foldr (fun z acc =>
    cmpM (if 0 < z then cM (gs.getD (z.toNat - 1) 0) else ciM (gs.getD ((-z).toNat - 1) 0)) acc)
    (Array.ofFn (n := 315) fun i => i.val)

meta def g1M : List Nat := [10, 11, 12]
meta def g2M : List Nat := [18, 19, 20, 21, 22]
meta def g3M : List Nat := [32, 33, 34, 35]

meta def a1M : Array Nat := evM g1M (oddWordsR1_3.getD 0 [])
meta def b1M : Array Nat := evM g1M (oddWordsR1_3.getD 1 [])
meta def a2M : Array Nat := evM g2M (oddWordsR2_5.getD 0 [])
meta def b2M : Array Nat := evM g2M (oddWordsR2_5.getD 1 [])
meta def c2M : Array Nat := evM g2M (oddWordsR2_5.getD 2 [])
meta def d2M : Array Nat := evM g2M (oddWordsR2_5.getD 3 [])
meta def e2M : Array Nat := evM g2M (oddWordsR2_7.getD 0 [])
meta def a3M : Array Nat := evM g3M (oddWordsR3_3.getD 0 [])
meta def b3M : Array Nat := evM g3M (oddWordsR3_3.getD 1 [])
meta def c3M : Array Nat := evM g3M (oddWordsR3_3.getD 2 [])
meta def d3M : Array Nat := evM g3M (oddWordsR3_5.getD 0 [])
meta def e3M : Array Nat := evM g3M (oddWordsR3_5.getD 1 [])
meta def a1IM : Array Nat := invM a1M
meta def b1IM : Array Nat := invM b1M
meta def a2IM : Array Nat := invM a2M
meta def b2IM : Array Nat := invM b2M
meta def c2IM : Array Nat := invM c2M
meta def d2IM : Array Nat := invM d2M
meta def e2IM : Array Nat := invM e2M
meta def a3IM : Array Nat := invM a3M
meta def b3IM : Array Nat := invM b3M
meta def c3IM : Array Nat := invM c3M
meta def d3IM : Array Nat := invM d3M
meta def e3IM : Array Nat := invM e3M

end CertificateChecks.KernelJ2F3

#ks_perm CertificateChecks.KernelJ2F3.A1 9 CertificateChecks.KernelJ2F3.a1M
#ks_perm CertificateChecks.KernelJ2F3.B1 9 CertificateChecks.KernelJ2F3.b1M
#ks_perm CertificateChecks.KernelJ2F3.A2 9 CertificateChecks.KernelJ2F3.a2M
#ks_perm CertificateChecks.KernelJ2F3.B2 9 CertificateChecks.KernelJ2F3.b2M
#ks_perm CertificateChecks.KernelJ2F3.C2 9 CertificateChecks.KernelJ2F3.c2M
#ks_perm CertificateChecks.KernelJ2F3.D2 9 CertificateChecks.KernelJ2F3.d2M
#ks_perm CertificateChecks.KernelJ2F3.E2 9 CertificateChecks.KernelJ2F3.e2M
#ks_perm CertificateChecks.KernelJ2F3.A3 9 CertificateChecks.KernelJ2F3.a3M
#ks_perm CertificateChecks.KernelJ2F3.B3 9 CertificateChecks.KernelJ2F3.b3M
#ks_perm CertificateChecks.KernelJ2F3.C3 9 CertificateChecks.KernelJ2F3.c3M
#ks_perm CertificateChecks.KernelJ2F3.D3 9 CertificateChecks.KernelJ2F3.d3M
#ks_perm CertificateChecks.KernelJ2F3.E3 9 CertificateChecks.KernelJ2F3.e3M
#ks_perm CertificateChecks.KernelJ2F3.A1I 9 CertificateChecks.KernelJ2F3.a1IM
#ks_perm CertificateChecks.KernelJ2F3.B1I 9 CertificateChecks.KernelJ2F3.b1IM
#ks_perm CertificateChecks.KernelJ2F3.A2I 9 CertificateChecks.KernelJ2F3.a2IM
#ks_perm CertificateChecks.KernelJ2F3.B2I 9 CertificateChecks.KernelJ2F3.b2IM
#ks_perm CertificateChecks.KernelJ2F3.C2I 9 CertificateChecks.KernelJ2F3.c2IM
#ks_perm CertificateChecks.KernelJ2F3.D2I 9 CertificateChecks.KernelJ2F3.d2IM
#ks_perm CertificateChecks.KernelJ2F3.E2I 9 CertificateChecks.KernelJ2F3.e2IM
#ks_perm CertificateChecks.KernelJ2F3.A3I 9 CertificateChecks.KernelJ2F3.a3IM
#ks_perm CertificateChecks.KernelJ2F3.B3I 9 CertificateChecks.KernelJ2F3.b3IM
#ks_perm CertificateChecks.KernelJ2F3.C3I 9 CertificateChecks.KernelJ2F3.c3IM
#ks_perm CertificateChecks.KernelJ2F3.D3I 9 CertificateChecks.KernelJ2F3.d3IM
#ks_perm CertificateChecks.KernelJ2F3.E3I 9 CertificateChecks.KernelJ2F3.e3IM

namespace CertificateChecks.KernelJ2F3

@[expose] noncomputable def bs : List Nat := [1, 0, 2]

@[expose] noncomputable def og1 : List (List Nat) := [[A1, B1], [], [A1, B1]]

@[expose] noncomputable def og2 : List (List Nat) := [[A2], [A2, B2, C2, D2], [E2]]

@[expose] noncomputable def og3 : List (List Nat) := [[A3, B3, C3], [D3, E3], []]

@[expose] noncomputable def og1I : List (List Nat) := [[A1I, B1I], [], [A1I, B1I]]

@[expose] noncomputable def og2I : List (List Nat) := [[A2I], [A2I, B2I, C2I, D2I], [E2I]]

@[expose] noncomputable def og3I : List (List Nat) := [[A3I, B3I, C3I], [D3I, E3I], []]

@[expose] noncomputable def rows1 : List (Nat × Nat × List (Nat × Nat)) :=
  [(3, 27, [(A1, A1I), (B1, B1I)]), (5, 25, []), (7, 7, [(A1, A1I), (B1, B1I)])]

@[expose] noncomputable def rows2 : List (Nat × Nat × List (Nat × Nat)) :=
  [(3, 27, [(A2, A2I)]), (5, 25, [(A2, A2I), (B2, B2I), (C2, C2I), (D2, D2I)]),
    (7, 7, [(E2, E2I)])]

@[expose] noncomputable def rows3 : List (Nat × Nat × List (Nat × Nat)) :=
  [(3, 27, [(A3, A3I), (B3, B3I), (C3, C3I)]), (5, 25, [(D3, D3I), (E3, E3I)]), (7, 7, [])]

end CertificateChecks.KernelJ2F3

end
