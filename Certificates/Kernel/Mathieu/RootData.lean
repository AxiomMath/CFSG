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

meta def rootS11 : List (List (List Nat)) := [m11S]
meta def rootB11 : List (List Nat) := [m11B]
meta def rootS12 : List (List (List Nat)) := [m12S]
meta def rootB12 : List (List Nat) := [m12B]
meta def rootS22 : List (List (List Nat)) := [m22S]
meta def rootB22 : List (List Nat) := [m22B]
meta def rootS23 : List (List (List Nat)) := [m23S]
meta def rootB23 : List (List Nat) := [m23B]
meta def rootS24 : List (List (List Nat)) := [m24S]
meta def rootB24 : List (List Nat) := [m24B]
meta def rootK : List Nat := [2]

@[expose] noncomputable def rootD11 : List (List (List ℤ)) := [m11RecordK.chain.derivations]
@[expose] noncomputable def rootD12 : List (List (List ℤ)) := [m12RecordK.chain.derivations]
@[expose] noncomputable def rootD22 : List (List (List ℤ)) := [m22RecordK.chain.derivations]
@[expose] noncomputable def rootD23 : List (List (List ℤ)) := [m23RecordK.chain.derivations]
@[expose] noncomputable def rootD24 : List (List (List ℤ)) := [m24RecordK.chain.derivations]

end CertificateChecks.KernelMathieu

open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.Root11 11 4 11 rootS11 rootB11 rootK rootD11

open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.Root12 12 4 12 rootS12 rootB12 rootK rootD12

open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.Root22 22 5 22 rootS22 rootB22 rootK rootD22

open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.Root23 23 5 23 rootS23 rootB23 rootK rootD23

open CertificateChecks.KernelMathieu in
#ks_rawchain_fam CertificateChecks.KernelMathieu.Root24 24 5 24 rootS24 rootB24 rootK rootD24

end
