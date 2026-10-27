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

@[expose] noncomputable def pD22 : List (List (List ℤ)) := m22PD.map (·.map decWord)

@[expose] noncomputable def nD22 (i : Nat) : List (List (List ℤ)) :=
  (m22RecordK.sylows.getD i default).normalGeneration.map (·.chain.derivations)

@[expose] noncomputable def nD22s0 : List (List (List ℤ)) := nD22 0
@[expose] noncomputable def nD22s1 : List (List (List ℤ)) := nD22 1
@[expose] noncomputable def nD22s2 : List (List (List ℤ)) := nD22 2
@[expose] noncomputable def nD22s3 : List (List (List ℤ)) := nD22 3
@[expose] noncomputable def nD22s4 : List (List (List ℤ)) := nD22 4

meta def nS22s0 : List (List (List Nat)) := m22NS.getD 0 []
meta def nB22s0 : List (List Nat) := m22NB.getD 0 []
meta def nK22s0 : List Nat := m22NK.getD 0 []
meta def nS22s1 : List (List (List Nat)) := m22NS.getD 1 []
meta def nB22s1 : List (List Nat) := m22NB.getD 1 []
meta def nK22s1 : List Nat := m22NK.getD 1 []
meta def nS22s2 : List (List (List Nat)) := m22NS.getD 2 []
meta def nB22s2 : List (List Nat) := m22NB.getD 2 []
meta def nK22s2 : List Nat := m22NK.getD 2 []
meta def nS22s3 : List (List (List Nat)) := m22NS.getD 3 []
meta def nB22s3 : List (List Nat) := m22NB.getD 3 []
meta def nK22s3 : List Nat := m22NK.getD 3 []
meta def nS22s4 : List (List (List Nat)) := m22NS.getD 4 []
meta def nB22s4 : List (List Nat) := m22NB.getD 4 []
meta def nK22s4 : List Nat := m22NK.getD 4 []

end CertificateChecks.KernelMathieu

open CFSG.KD.Mathieu CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.P22 22 5 22 m22PS m22PB m22PK pD22

open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N22s0 22 5 22 nS22s0 nB22s0 nK22s0 nD22s0
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N22s1 22 5 22 nS22s1 nB22s1 nK22s1 nD22s1
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N22s2 22 5 22 nS22s2 nB22s2 nK22s2 nD22s2
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N22s3 22 5 22 nS22s3 nB22s3 nK22s3 nD22s3
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N22s4 22 5 22 nS22s4 nB22s4 nK22s4 nD22s4

end
