module

public import Certificates.Data.Kernel.BfsReach
public import Certificates.Data.CatFactsL4U4P1U43Defs
import all Init.Data.Range.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSchreierFam.C22241

open CFSG.KC.BfsPairs CFSG.LieType.Multipliers.U43 CFSG.ComponentClassification.HarrisLit.P1.U43
  Matrix

@[expose] noncomputable def stepU (l p : Nat) : Nat :=
  (UInt32.ofNat (if l = 0 then tabA else tabB)[p]!).toNat

@[expose] noncomputable def onlyFix (b c₁ c₂ : Nat) : Bool :=
  (List.range 820).all fun j => j == b || ptIndex (mv4 (matN9 c₁) (decode j)) != j ||
    ptIndex (mv4 (matN9 c₂) (decode j)) != j

theorem reach : (bfsReach 820 2 stepU [0, 4]).toList.all id = true := by decide +kernel

theorem only0 : onlyFix 0 404334890521881 1352341616652227 = true := by decide +kernel

theorem only4 : onlyFix 4 1309751274598484 1681408017212684 = true := by decide +kernel

theorem fixes : ptIndex (mv4 (matN9 404334890521881) (decode 0)) = 0 ∧
    ptIndex (mv4 (matN9 1352341616652227) (decode 0)) = 0 ∧
    ptIndex (mv4 (matN9 1309751274598484) (decode 4)) = 4 ∧
    ptIndex (mv4 (matN9 1681408017212684) (decode 4)) = 4 := by decide +kernel

theorem unitary1 : ((matN9 404334890521881).map (· ^ 3))ᵀ * matN9 404334890521881 = 1 := by
  decide +kernel

theorem unitary2 : ((matN9 1352341616652227).map (· ^ 3))ᵀ * matN9 1352341616652227 = 1 := by
  decide +kernel

theorem unitary3 : ((matN9 1309751274598484).map (· ^ 3))ᵀ * matN9 1309751274598484 = 1 := by
  decide +kernel

theorem unitary4 : ((matN9 1681408017212684).map (· ^ 3))ᵀ * matN9 1681408017212684 = 1 := by
  decide +kernel

theorem det1 : (matN9 404334890521881).det = 1 := by decide +kernel

theorem det2 : (matN9 1352341616652227).det = 1 := by decide +kernel

theorem det3 : (matN9 1309751274598484).det = 1 := by decide +kernel

theorem det4 : (matN9 1681408017212684).det = 1 := by decide +kernel

end CertificateChecks.KernelSchreierFam.C22241
