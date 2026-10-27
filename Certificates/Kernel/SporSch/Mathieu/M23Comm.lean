module

public import Certificates.Data.CommProdM23
public meta import Certificates.Data.CommProdM23
public import Certificates.Kernel.SporSch.Mathieu.M23Facts
public import CFSG.Certificates.Kernel.SporSch.CommWordSound
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutCheckBase

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.M23Comm

open CFSG CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu CFSG.OddStandard
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CFSG.KS.SporSch.CommWord
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.M23OC Certificates.CommProd

theorem kPerm : allN 4 (fun j => permOK 23 5 (mask 5) (23 * 5) (M23C1.S j) (M23C1.SI j)) =
    true := by quickRfl

theorem kId : idK 23 5 (mask 5) = true := by quickRfl

theorem kWords : allN 4 (fun i => bAnd(lettersK 4 (cpWord (m23CentPerfWit.getD i [])),
    Nat.beq (wordK 23 5 (mask 5) (pidn 23 5) M23C1.S M23C1.SI (cpWord (m23CentPerfWit.getD i [])))
      (M23C1.S i))) = true := by quickRfl

theorem and_of_bAnd {a b : Bool} (h : bAnd(a, b) = true) : a = true ∧ b = true := by
  cases a <;> simp_all

theorem img_one : imageList (1 : Equiv.Perm (Fin 23)) = (unpack 23 5 (pidn 23 5)).toList := by
  rw [idK_sound kId]
  apply List.ext_getElem <;> simp [imageList, CFSG.Monster.B.Co2.Native.idA]

theorem len_cg : m23Cg1.length = 4 := by
  simp [m23Cg1, m23CentWords1]

theorem commProd : commProdOK m23Cg1 m23CentPerfWit = true := by
  have hg : ∀ j < m23Cg1.length, imageList (m23Cg1.getD j 1) = (unpack 23 5 (M23C1.S j)).toList :=
    chainC1.2.2.2.1
  refine commProdOK_of_img szOK' hg (fun j hj => allN_spec kPerm j (len_cg ▸ hj)) img_one
    (by rw [len_cg]; rfl) (by decide) fun i hi => ?_
  rw [len_cg] at hi ⊢
  obtain ⟨h1, h2⟩ := and_of_bAnd (allN_spec kWords i hi)
  exact ⟨h1, Nat.eq_of_beq_eq_true h2⟩

end CertificateChecks.KernelSporSch.M23Comm

end
