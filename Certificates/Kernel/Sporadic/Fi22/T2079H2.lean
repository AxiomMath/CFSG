module

public import Certificates.Kernel.Sporadic.ConjTreeGen
public import Certificates.Kernel.Sporadic.Fi22.H2066c2
public import Certificates.Kernel.Sporadic.Fi22.R2079P42
public import Certificates.Kernel.Sporadic.Fi22.D2079
public meta import Certificates.Kernel.Sporadic.Fi22.H2066D
public meta import CFSG.Sporadic.FischerOddCore.FischerOuterFi22CheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Spor.Loops
import CFSG.Certificates.Kernel.Spor.PackFld
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelSpor.Fo22R

meta def g2M : Array (Array Nat) := CertificateChecks.KernelSpor.Fi22H.S2.extract 0 3

end CertificateChecks.KernelSpor.Fo22R

#ks_conjtree CertificateChecks.KernelSpor.Fo22T2 3510 12 3 27 CertificateChecks.KernelSpor.Fo22R.g2M
  CFSG.Sporadic.FischerOddCore.fo22S02 CFSG.Sporadic.FischerOddCore.fo22Tree2
  CertificateChecks.KernelSpor.Fi22H2.S CertificateChecks.KernelSpor.Fi22H2.SI
  CertificateChecks.KernelSpor.Fo22T.Tree2.F 7 CertificateChecks.KernelSpor.Fo22P2.S 5

namespace CertificateChecks.KernelSpor.Fo22T2

open CFSG.KC.Enum CFSG.KS

noncomputable def commRow (j : Nat) : Bool := allN 27 (fun k =>
  Nat.beq (pcomp 3510 12 (mask 12) (T j) (T k)) (pcomp 3510 12 (mask 12) (T k) (T j)))

noncomputable def commSl (s : Nat) : Bool := allN 3 (fun d => commRow (Nat.add (s * 3) d))

theorem c0 : commSl 0 = true := by quickRfl
theorem c1 : commSl 1 = true := by quickRfl
theorem c2 : commSl 2 = true := by quickRfl
theorem c3 : commSl 3 = true := by quickRfl
theorem c4 : commSl 4 = true := by quickRfl
theorem c5 : commSl 5 = true := by quickRfl
theorem c6 : commSl 6 = true := by quickRfl
theorem c7 : commSl 7 = true := by quickRfl
theorem c8 : commSl 8 = true := by quickRfl

theorem comm2 : allN 27 (fun j => allN 27 (fun k =>
    Nat.beq (pcomp 3510 12 (mask 12) (T j) (T k)) (pcomp 3510 12 (mask 12) (T k) (T j)))) = true := by
  have hs : ∀ s < 9, commSl s = true := fun s h9 => by
    interval_cases s
    exacts [c0, c1, c2, c3, c4, c5, c6, c7, c8]
  refine PackFld.allN_of_forall fun j hj => ?_
  have h : commRow (Nat.add (j / 3 * 3) (j % 3)) = true :=
    allN_spec (hs (j / 3) (by omega)) (j % 3) (Nat.mod_lt _ (by norm_num))
  rw [Nat.add_eq, Nat.div_add_mod'] at h
  exact h

end CertificateChecks.KernelSpor.Fo22T2

end
