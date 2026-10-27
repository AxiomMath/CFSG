module

public import Certificates.Kernel.LocalComp.L34Field.Chk
public import Certificates.Kernel.LocalComp.L34Para.Final
public import CFSG.Certificates.Kernel.L34FieldSound

public section

namespace CertificateChecks.KernelLC.L34Field

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34Field CFSG.KC.L34W
open CertificateChecks.KernelLC.L34X CertificateChecks.KernelLC.L34Cert
open CertificateChecks.KernelLC.L34Para CFSG.PSL3Four.Native
open CFSG.ComponentClassification.GrSLit.L34Facts

theorem gensG : GensG L34R.G := fun _ hj => ⟨g_eq hj, cnG hj⟩

theorem hY : ∀ k < 105, wordTab (wReps.getD k []) = unpack 42 6 (L34PR.Y k) ∧ Cn (L34PR.Y k) := by
  intro k hk
  have hkl : k < wReps.length := hk
  refine ⟨?_, canonY hk⟩
  rw [← (gY.2 k hk).1, wordTabs_getElem! wReps hkl, List.getD_eq_getElem _ _ hkl]

theorem hYI : ∀ k < 105, invTab 42 (unpack 42 6 (L34PR.Y k)) = unpack 42 6 (L34PR.YI k) ∧
    Cn (L34PR.YI k) := by
  intro k hk
  obtain ⟨c, e⟩ := andB_iff.1 (allN' kYI k hk)
  exact ⟨invTab_eq_of_pcomp (canonY hk) c (Nat.eq_of_beq_eq_true e), c⟩

theorem syl2Wit_true : syl2WitOK = true :=
  syl2WitOK_of gensG r2_eq (cnRP (by decide)) rT.1 rT.2.2.1 rT.2.2.2 rB.1 hY hYI kSyl22209

theorem fieldFree_true : fieldFreeOK = true :=
  fieldFreeOK_of gensG r2_eq (cnRP (by decide)) kField22209

theorem fieldOK_true : fieldOK = true := by
  unfold fieldOK
  rw [syl2Wit_true, fieldFree_true]
  rfl

end CertificateChecks.KernelLC.L34Field

end
