module

public import Certificates.Data.Kernel.F3152.Forms
public import Certificates.Data.Kernel.Spor.Row
public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Kernel.Sporadic.RowsWCmd
public meta import CFSG.Monster.B.Fischer.Fi22FormsData
public meta import CFSG.Monster.B.Fischer.Fi22SepData
public meta import CFSG.Monster.B.Fischer.PinnedChainData
public meta import Certificates.Data.CFSGNative.Fi22Pinned.Forms
public meta import Certificates.Data.CFSGNative.Fi22.Certificate

public section

namespace CertificateChecks.KernelSpor.F3152

open CFSG.F3.Native CFSG.Monster.B.Fischer CFSG.Monster.B.Fischer.Native

meta def laneP (X : Array V) : Nat := (List.range 77).foldl (fun a i => a + X[i]!.p * 2 ^ (77 * i)) 0

meta def laneM (X : Array V) : Nat := (List.range 77).foldl (fun a i => a + X[i]!.m * 2 ^ (77 * i)) 0

meta def lanes : Array Nat := Id.run do
  let mut a : Array Nat := #[]
  let mats : Array (Array V) := (Array.range 3510).map (fun r => polarRows fi22FormsBytes (752 * r)) ++
    #[polarRows fi22InvFormBytes 0, fi22Bi, transpose 77 (CFSG.Sporadic.Fi22.Native.matA ()),
      transpose 77 (CFSG.Sporadic.Fi22.Native.matB ())]
  for X in mats do
    a := (a.push (laneP X)).push (laneM X)
  return a

meta def gens : Array Nat :=
  #[0, 1].map fun k => (List.range 3510).foldl (fun a i => a + (fi22ChainGen k)[i]! * 2 ^ (12 * i)) 0

end CertificateChecks.KernelSpor.F3152

#krowsw CertificateChecks.KernelSpor.F3152.ST 5929 CertificateChecks.KernelSpor.F3152.lanes
#krowsw CertificateChecks.KernelSpor.F3152.GT 42120 CertificateChecks.KernelSpor.F3152.gens

namespace CertificateChecks.KernelSpor.F3152

open CFSG.F3.Native CFSG.KS CFSG.KS.Row

@[expose] noncomputable def SL (i : Nat) : V :=
  ⟨rg (nat_lit 5929) (mask (nat_lit 5929)) ST (nat_lit 0) (Nat.mul (nat_lit 2) i),
    rg (nat_lit 5929) (mask (nat_lit 5929)) ST (nat_lit 0) (Nat.succ (Nat.mul (nat_lit 2) i))⟩

@[expose] noncomputable def GL (k : Nat) : Nat := rg (nat_lit 42120) (mask (nat_lit 42120)) GT (nat_lit 0) k

end CertificateChecks.KernelSpor.F3152

end
