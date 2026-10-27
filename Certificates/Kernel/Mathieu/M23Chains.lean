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

@[expose] noncomputable def pD23 : List (List (List ℤ)) := m23PD.map (·.map decWord)

@[expose] noncomputable def nD23 (i : Nat) : List (List (List ℤ)) :=
  (m23RecordK.sylows.getD i default).normalGeneration.map (·.chain.derivations)

@[expose] noncomputable def nD23s0 : List (List (List ℤ)) := nD23 0
@[expose] noncomputable def nD23s1 : List (List (List ℤ)) := nD23 1
@[expose] noncomputable def nD23s2 : List (List (List ℤ)) := nD23 2
@[expose] noncomputable def nD23s3 : List (List (List ℤ)) := nD23 3
@[expose] noncomputable def nD23s4 : List (List (List ℤ)) := nD23 4
@[expose] noncomputable def nD23s5 : List (List (List ℤ)) := nD23 5

meta def nS23s0 : List (List (List Nat)) := m23NS.getD 0 []
meta def nB23s0 : List (List Nat) := m23NB.getD 0 []
meta def nK23s0 : List Nat := m23NK.getD 0 []
meta def nS23s1 : List (List (List Nat)) := m23NS.getD 1 []
meta def nB23s1 : List (List Nat) := m23NB.getD 1 []
meta def nK23s1 : List Nat := m23NK.getD 1 []
meta def nS23s2 : List (List (List Nat)) := m23NS.getD 2 []
meta def nB23s2 : List (List Nat) := m23NB.getD 2 []
meta def nK23s2 : List Nat := m23NK.getD 2 []
meta def nS23s3 : List (List (List Nat)) := m23NS.getD 3 []
meta def nB23s3 : List (List Nat) := m23NB.getD 3 []
meta def nK23s3 : List Nat := m23NK.getD 3 []
meta def nS23s4 : List (List (List Nat)) := m23NS.getD 4 []
meta def nB23s4 : List (List Nat) := m23NB.getD 4 []
meta def nK23s4 : List Nat := m23NK.getD 4 []
meta def nS23s5 : List (List (List Nat)) := m23NS.getD 5 []
meta def nB23s5 : List (List Nat) := m23NB.getD 5 []
meta def nK23s5 : List Nat := m23NK.getD 5 []

end CertificateChecks.KernelMathieu

open CFSG.KD.Mathieu CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.P23 23 5 23 m23PS m23PB m23PK pD23

open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N23s0 23 5 23 nS23s0 nB23s0 nK23s0 nD23s0
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N23s1 23 5 23 nS23s1 nB23s1 nK23s1 nD23s1
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N23s2 23 5 23 nS23s2 nB23s2 nK23s2 nD23s2
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N23s3 23 5 23 nS23s3 nB23s3 nK23s3 nD23s3
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N23s4 23 5 23 nS23s4 nB23s4 nK23s4 nD23s4
open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.N23s5 23 5 23 nS23s5 nB23s5 nK23s5 nD23s5

end
