module

public import CFSG.Certificates.Kernel.Mols4Sound
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneSquaresInputs
import CFSG.Certificates.Kernel.Common.Harness
public import Mathlib

public section

namespace CertificateChecks.KernelLC

open CFSG.KC.Mols4 CFSG.KLie.CT CFSG.ComponentClassification.WittDesign

@[expose] noncomputable def PL : Nat := nat_lit 669236436005411928080145373044091295208890640391302853860

@[expose] noncomputable def LL : Nat :=
  nat_lit 116537985661465278778626903548241849386918932628970121183322136741339740317234973495119408469536117079

theorem kPerms : permsOK PL = true := by quickRfl
theorem kList : listOK PL LL = true := by quickRfl
theorem kMols : molsK PL LL 13639 4600 9407 = true := by quickRfl

theorem tA : IsTriple PL 13639 rA := ⟨by decide, by decide⟩
theorem tB : IsTriple PL 4600 rB := ⟨by decide, by decide⟩
theorem tC : IsTriple PL 9407 rC := ⟨by decide, by decide⟩

open CFSG CFSG.ComponentClassification CFSG.ComponentClassification.WittDesign Equiv in
theorem cert2037 : MolsLevel2 := sound kPerms kList tA tB tC kMols

end CertificateChecks.KernelLC

end
