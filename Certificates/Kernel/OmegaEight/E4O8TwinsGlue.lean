module

public import Certificates.Kernel.OmegaEight.E4O8TwinsK
public import Certificates.Kernel.OmegaEight.E4O8MembersGlue
public import Certificates.Data.E4O8TwoTwins

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.Monster.B.Co2.Native CFSG.ClassicalInvolution.Q3.TL4

theorem e4_wsW_getD {k : Nat} (hk : k < 6300) : (E4O8.wsW ()).getD k [] = e4WW k := by
  rw [wsW_eq]
  unfold e4WW
  exact getD_map_of_lt _ _ _ (by rw [e4_len]; exact hk)

theorem e4_member {k : Nat} (hk : k < 6300) :
    omegaW ((E4O8.wsW ()).getD k []) = unpack 360 9 (wO (e4WW k)) ∧ cn (wO (e4WW k)) = true ∧
      pm (wO (e4WW k)) = true ∧ cn (pinv (wO (e4WW k))) = true := by
  obtain ⟨hl, hc, hp, -⟩ := e4_row_facts (e4_row_at hk)
  obtain ⟨p, i⟩ := e4Pm_iff.1 hp
  rw [e4_wsW_getD hk]
  exact ⟨omegaW_eq hl, hc, p, i⟩

theorem e4_two_twins : Certificates.E4O8TwoTwins.check () = true := by
  have hk := kE4Twins
  simp only [bAnd_iff] at hk
  obtain ⟨hE, hD⟩ := hk
  obtain ⟨-, cu, -, cv, -, -⟩ := e4_facts
  obtain ⟨e1, c1, p1, i1⟩ := e4_member (k := 1) (by norm_num)
  obtain ⟨e3, c3, p3, i3⟩ := e4_member (k := 3) (by norm_num)
  unfold e4EdgeAt at hE
  simp only [bAnd_iff] at hE
  unfold e4DiffAt at hD
  simp only [bAnd_iff] at hD
  obtain ⟨hp, hn⟩ := hD
  obtain ⟨pd, cd⟩ := e4Pm_iff.1 hp
  unfold Certificates.E4O8TwoTwins.check
  simp only []
  rw [e1, e3, L0A_pk, u0A_pk, v0A_pk, edgeCheckA_pk e4L_cn cu cv c3 i3 p3 hE.1 hE.2.1,
    invCand_pinv p1, compA_pc i1 c3, normsA_pk e4L_cn cu cv (cn_pc i1 c3) cd pd, hE.2.2,
    Bool.true_and]
  exact e4_not_of hn

end CertificateChecks.KernelO8

end
