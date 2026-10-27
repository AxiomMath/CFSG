module

public import CFSG.ClassicalInvolution.SmallCases.NobqLists
import Certificates.Kernel.SmallSpor.M23Checks
import Certificates.Kernel.SmallSpor.M23RChecks
import Certificates.Kernel.SporSch.Mathieu.M23Facts
import CFSG.Certificates.Kernel.ListBridge.RootSound
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.M23Inputs
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23

namespace CertificateChecks.KernelSmallSpor.M23R

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Sporadic.Mathieu
open CFSG.Sporadic.Schreier.Native CFSG.Monster.B.Mathieu CFSG.ClassicalInvolution
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.Prim CFSG.KC.ListBridge
open CFSG.ClassicalInvolution.ListBridge CFSG.ClassicalInvolution.Nobq CFSG.KS.SporSch.MOC
open CertificateChecks.KernelSmallSpor.M23

theorem kGens_eq : m23KGens1 = m23CentWords1.map (evalCodes [m23PermA, m23PermB]) := by
  simp only [m23KGens1, tabWords, tab_eq]

theorem lenK : m23KGens1.length = EK.ng := by
  rw [Nat.eq_of_beq_eq_true nums.1, kGens_eq, List.length_map]
  rfl

theorem prepK : ∀ j < EK.ng, PRep 23 5 (EK.G j) (m23KGens1.getD j 1) := by
  intro j hj
  rw [Nat.eq_of_beq_eq_true (allN_spec bindK j (by rwa [← Nat.eq_of_beq_eq_true nums.1]))]
  rw [kGens_eq]
  have hj' : j < (m23CentWords1.map (evalCodes [m23PermA, m23PermB])).length := by
    rw [← kGens_eq, lenK]
    exact hj
  exact prep_of_imageList (KernelSporSch.M23OC.chainC1.2.2.2.1 j hj')

theorem mem_K (g : Equiv.Perm (Fin 23)) :
    g ∈ enumerationTab m23CentQ1 ↔ g ∈ Subgroup.closure {s | s ∈ m23KGens1} := by
  rw [mem_enumerationTab_iff m23CentQ1 KernelSporSch.M23OC.cent1.1, m23CentQ1,
    certificate_originalSubgroup, kGens_eq]

public theorem check9306 : cqCheck m23Rep1 (enumerationTab m23CentQ1) = true := by
  have hR : PRep 23 5 (KernelSporSch.M23CK.getD 0 clsD0).R m23Rep1 :=
    prep_of_imageList KernelSporSch.M23OC.imgRep0
  have hs := rootsK_sound EK.ok lenK prepK hR roots
  simp only [cqCheck, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true]
  intro c hcL
  by_cases hcr : c * c = m23Rep1
  · right
    obtain ⟨g, hg, h⟩ := hs c ((mem_K c).1 hcL) hcr
    exact ⟨g, (mem_K g).2 hg, h⟩
  · exact Or.inl hcr

end CertificateChecks.KernelSmallSpor.M23R
