
module

public import Certificates.Kernel.He7223.Pts
public import Certificates.Kernel.SchreierFam.He725F
public import CFSG.Certificates.Kernel.Misc.WordPtsGroup
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

set_option maxRecDepth 400000

#kss_strof CertificateChecks.KernelHe7223.ES CFSG.Quasithin.KGC31.He.eW

namespace CertificateChecks.KernelHe7223

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.WordPts CFSG.Quasithin.KGC31
  CFSG.Quasithin.KGC31.He CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
  CFSG.Sporadic.Schreier CertificateChecks.KernelLC.HeFix
  CertificateChecks.KernelSchreierFam.He725

theorem gens3_length : gens3.length = 3 := rfl

theorem letRep_LU :
    LetRep 8330 14 LU LUI gens3 := by
  intro j hj
  rw [gens3_length] at hj
  have hrep : Rep 8330 (unpack 8330 14 (LU j)) (gens3.getD j 1) := by
    rw [← gA_bind.2 j hj]
    have := rep_gA j (by rw [gens3_length]; exact hj)
    rwa [List.getD_eq_getElem _ _ (by rw [gens3_length]; exact hj)] at this ⊢
  have hp : permOK 8330 14 (mask 14) (8330 * 14) (LU j) (LUI j) = true := allN_spec kPLU j hj
  obtain ⟨h1, h2⟩ := rep_permOfArr (Orb.isInvA_unpack hp)
  have e := h1.unique hrep
  rw [e] at h2
  exact ⟨Orb.prep_of_rep hrep, Orb.prep_of_rep h2⟩

theorem eW_eq : eW = EB := by
  rw [ES.eq, decodeWs_ofList (by decide) (ascii_of_all (by decide +kernel))]
  decide +kernel

theorem qW_eq : qW = QB := by
  rw [QS.eq, decodeWs_ofList (by decide) (ascii_of_all (by decide +kernel))]
  decide +kernel

theorem bsL_lt : ∀ b ∈ bsL, b < 8330 := by decide

theorem bsL_eq : bsL = bs := rfl

theorem EB_letters : ∀ wd ∈ EB, lettersOK 2 wd = true := by decide +kernel

theorem QB_letters : ∀ wd ∈ QB, lettersOK 2 wd = true := by decide +kernel

theorem letters3 {B : List (List ℤ)} (h : ∀ wd ∈ B, lettersOK 2 wd = true) :
    ∀ wd ∈ B, lettersOK gens3.length wd = true := fun wd hw =>
  lettersOK_mono (by rw [gens3_length]; norm_num) (h wd hw)

theorem mem_heP_of
    {B : List (List ℤ)} (h : ∀ wd ∈ B, lettersOK 2 wd = true) :
    ∀ wd ∈ B, evalSignedWord gens3 wd ∈ heP := fun wd hw => elt_mem_heP (h wd hw)

theorem ebasis_E :
    EBasis (fun i : Fin 6 => elt (eW.getD i [])) := by
  rw [eW_eq]
  exact ebasis_of_ebK (bsL_eq ▸ baseFaithful_heP) letRep_LU bsL_lt (letters3 EB_letters)
    (mem_heP_of EB_letters) ch7223eb

theorem ebasis_Q :
    EBasis (fun i : Fin 4 => elt (qW.getD i [])) := by
  rw [qW_eq]
  exact ebasis_of_ebK (bsL_eq ▸ baseFaithful_heP) letRep_LU bsL_lt (letters3 QB_letters)
    (mem_heP_of QB_letters) ch7223qb

end CertificateChecks.KernelHe7223

end
