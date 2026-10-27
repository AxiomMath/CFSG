module

public import Certificates.Data.Kernel.Spor.ONTauK
public import Certificates.Kernel.Sporadic.ON2.Data
public import CFSG.Sporadic.Recognition.ONMultiplierInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONC

open CFSG.KS.ONC

@[expose] def tauPairs : List (List Nat × List Nat) :=
  [([3, 3, 0], [0, 3, 3]), ([3, 3, 1], [1, 0, 1, 3, 3]), ([3, 3, 2], [2, 3, 3])]

@[expose] noncomputable def FA (j : Nat) : Nat := List.getD ONW.LA j (nat_lit 0)

@[expose] noncomputable def FB (j : Nat) : Nat := List.getD ONW.LB j (nat_lit 0)

set_option Elab.async false

theorem tau_ok :
    relsK FA FB CFSG.Sporadic.Recognition.ONMultiplier.onGenWords.toList tauPairs = true := by
  quickRfl

end CertificateChecks.KernelSpor.ONC

end
