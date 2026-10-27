module

public import CFSG.Certificates.Kernel.Spor.RawFam
public import CFSG.Monster.B.Mathieu.CertDataK
public meta import Certificates.Data.Kernel.Mathieu.Raw
public meta import Certificates.Kernel.Sporadic.RawGenFam
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.RawGenFam
public import Mathlib.GroupTheory.Schreier

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMathieu

open CFSG.KD.Mathieu CFSG.Monster.B.Mathieu

@[expose] noncomputable def pD24 : List (List (List ℤ)) := m24PD.map (·.map decWord)

@[expose] noncomputable def nD24 (i : Nat) : List (List (List ℤ)) :=
  (m24RecordK.sylows.getD i default).normalGeneration.map (·.chain.derivations)

@[expose] noncomputable def nD24s0 : List (List (List ℤ)) := nD24 0
@[expose] noncomputable def nD24s1 : List (List (List ℤ)) := nD24 1
@[expose] noncomputable def nD24s2 : List (List (List ℤ)) := nD24 2
@[expose] noncomputable def nD24s3 : List (List (List ℤ)) := nD24 3
@[expose] noncomputable def nD24s4 : List (List (List ℤ)) := nD24 4
@[expose] noncomputable def nD24s5 : List (List (List ℤ)) := nD24 5

meta def nS24s0 : List (List (List Nat)) := m24NS.getD 0 []
meta def nB24s0 : List (List Nat) := m24NB.getD 0 []
meta def nK24s0 : List Nat := m24NK.getD 0 []
meta def nS24s1 : List (List (List Nat)) := m24NS.getD 1 []
meta def nB24s1 : List (List Nat) := m24NB.getD 1 []
meta def nK24s1 : List Nat := m24NK.getD 1 []
meta def nS24s2 : List (List (List Nat)) := m24NS.getD 2 []
meta def nB24s2 : List (List Nat) := m24NB.getD 2 []
meta def nK24s2 : List Nat := m24NK.getD 2 []
meta def nS24s3 : List (List (List Nat)) := m24NS.getD 3 []
meta def nB24s3 : List (List Nat) := m24NB.getD 3 []
meta def nK24s3 : List Nat := m24NK.getD 3 []
meta def nS24s4 : List (List (List Nat)) := m24NS.getD 4 []
meta def nB24s4 : List (List Nat) := m24NB.getD 4 []
meta def nK24s4 : List Nat := m24NK.getD 4 []
meta def nS24s5 : List (List (List Nat)) := m24NS.getD 5 []
meta def nB24s5 : List (List Nat) := m24NB.getD 5 []
meta def nK24s5 : List Nat := m24NK.getD 5 []

end CertificateChecks.KernelMathieu

open CFSG.KD.Mathieu CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.P24 24 5 24 m24PS m24PB m24PK pD24

open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N24s0 24 5 24 nS24s0 nB24s0 nK24s0 nD24s0
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N24s1 24 5 24 nS24s1 nB24s1 nK24s1 nD24s1
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N24s2 24 5 24 nS24s2 nB24s2 nK24s2 nD24s2
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N24s3 24 5 24 nS24s3 nB24s3 nK24s3 nD24s3
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N24s4 24 5 24 nS24s4 nB24s4 nK24s4 nD24s4
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N24s5 24 5 24 nS24s5 nB24s5 nK24s5 nD24s5

end
