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

@[expose] noncomputable def pD11 : List (List (List ℤ)) := m11PD.map (·.map decWord)

@[expose] noncomputable def nD11 (i : Nat) : List (List (List ℤ)) :=
  (m11RecordK.sylows.getD i default).normalGeneration.map (·.chain.derivations)

@[expose] noncomputable def nD11s0 : List (List (List ℤ)) := nD11 0
@[expose] noncomputable def nD11s1 : List (List (List ℤ)) := nD11 1
@[expose] noncomputable def nD11s2 : List (List (List ℤ)) := nD11 2
@[expose] noncomputable def nD11s3 : List (List (List ℤ)) := nD11 3

meta def nS11s0 : List (List (List Nat)) := m11NS.getD 0 []
meta def nB11s0 : List (List Nat) := m11NB.getD 0 []
meta def nK11s0 : List Nat := m11NK.getD 0 []
meta def nS11s1 : List (List (List Nat)) := m11NS.getD 1 []
meta def nB11s1 : List (List Nat) := m11NB.getD 1 []
meta def nK11s1 : List Nat := m11NK.getD 1 []
meta def nS11s2 : List (List (List Nat)) := m11NS.getD 2 []
meta def nB11s2 : List (List Nat) := m11NB.getD 2 []
meta def nK11s2 : List Nat := m11NK.getD 2 []
meta def nS11s3 : List (List (List Nat)) := m11NS.getD 3 []
meta def nB11s3 : List (List Nat) := m11NB.getD 3 []
meta def nK11s3 : List Nat := m11NK.getD 3 []

end CertificateChecks.KernelMathieu

open CFSG.KD.Mathieu CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.P11 11 4 11 m11PS m11PB m11PK pD11

open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N11s0 11 4 11 nS11s0 nB11s0 nK11s0 nD11s0
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N11s1 11 4 11 nS11s1 nB11s1 nK11s1 nD11s1
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N11s2 11 4 11 nS11s2 nB11s2 nK11s2 nD11s2
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N11s3 11 4 11 nS11s3 nB11s3 nK11s3 nD11s3

end
