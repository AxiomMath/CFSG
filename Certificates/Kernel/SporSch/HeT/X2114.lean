module

public import Certificates.Kernel.SporSch.Mathieu.GenOddPt
public import Certificates.Kernel.LocalQT.He4148.Glue
public import CFSG.Sporadic.HeldB.InnerCheckInputs
public meta import CFSG.Sporadic.HeldB.InnerData
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HeX14

open CFSG.KS.SporSch.MOCG CFSG.Sporadic.HeldB

meta def SX0 : Array (Array Nat) := strongOf 240 heInnerSigma0.toArray heInnerChainWords0

meta def baseX0 : Array Nat := #[0, 1, 2]

meta def SX1 : Array (Array Nat) := strongOf 42 heInnerSigma1.toArray heInnerChainWords1

meta def baseX1 : Array Nat := #[0, 1, 7, 10, 3, 2]

end CertificateChecks.KernelSporSch.HeX14

#ks_rawchain CertificateChecks.KernelSporSch.HeX14.X0Q 240 8 16
  CertificateChecks.KernelSporSch.HeX14.SX0 CertificateChecks.KernelSporSch.HeX14.baseX0 9
  CFSG.Sporadic.HeldB.heInnerChainWords0

#ks_rawchain CertificateChecks.KernelSporSch.HeX14.X1Q 42 6 16
  CertificateChecks.KernelSporSch.HeX14.SX1 CertificateChecks.KernelSporSch.HeX14.baseX1 9
  CFSG.Sporadic.HeldB.heInnerChainWords1

namespace CertificateChecks.KernelSporSch.HeX14

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Sporadic.HeldB CertificateChecks.KernelLQT.He4148

theorem bX0 : bindsK 240 8 X0Q.S X0Q.SI heInnerSigma0 0 = true := by quickRfl

theorem bX1 : bindsK 42 6 X1Q.S X1Q.SI heInnerSigma1 0 = true := by quickRfl

theorem oX0 : Nat.beq (ordK X0Q.LR 3) 80640 = true := by quickRfl

theorem oX1 : Nat.beq (ordK X1Q.LR 6) 10752 = true := by quickRfl

theorem len_X0 : heInnerSigma0.length = 9 := rfl

theorem len_X1 : heInnerSigma1.length = 9 := rfl

theorem atX0 {j : Nat} (hj : j < 9) :
    BindAt 240 8 (X0Q.S j) (X0Q.SI j) (heInnerSigma0.getD j #[]) := by
  have h := bindsK_spec bX0 j (by rw [len_X0]; exact hj)
  rwa [Nat.zero_add] at h

theorem atX1 {j : Nat} (hj : j < 9) :
    BindAt 42 6 (X1Q.S j) (X1Q.SI j) (heInnerSigma1.getD j #[]) := by
  have h := bindsK_spec bX1 j (by rw [len_X1]; exact hj)
  rwa [Nat.zero_add] at h

theorem chainX0 : ChainK 240 8 (heInnerSigma0.map (permOrId 240)) heInnerChainWords0
    (#v[0, 1, 2] : Vector (Fin 240) 3) X0Q.S X0Q.SI X0Q.LR X0Q.TR X0Q.TRI 13 X0Q.BP 15 16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, X0Q.head, X0Q.hl,
    by norm_num, X0Q.hs⟩
  have hj' : j < heInnerSigma0.length := by simpa using hj
  rw [getD_map_lt _ #[] _ hj']
  exact imageList_bind (atX0 (len_X0 ▸ hj'))

theorem chainX1 : ChainK 42 6 (heInnerSigma1.map (permOrId 42)) heInnerChainWords1
    (#v[0, 1, 7, 10, 3, 2] : Vector (Fin 42) 6) X1Q.S X1Q.SI X1Q.LR X1Q.TR X1Q.TRI 17 X1Q.BP 3
    16 := by
  refine ⟨by norm_num, by norm_num, by norm_num, fun j hj => ?_, by decide, X1Q.head, X1Q.hl,
    by norm_num, X1Q.hs⟩
  have hj' : j < heInnerSigma1.length := by simpa using hj
  rw [getD_map_lt _ #[] _ hj']
  exact imageList_bind (atX1 (len_X1 ▸ hj'))

theorem x0_check : heX0.check = true ∧ heX0.orderCertificate = 80640 := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainX0
  exact ⟨h1, h2.trans (Nat.eq_of_beq_eq_true oX0)⟩

theorem x1_check : heX1.check = true ∧ heX1.orderCertificate = 10752 := by
  obtain ⟨h1, h2⟩ := chainK_check (by decide) (by decide) chainX1
  exact ⟨h1, h2.trans (Nat.eq_of_beq_eq_true oX1)⟩

theorem sig_perm : (∀ j < 9, permChk 240 (heInnerSigma0.getD j #[]) = true) ∧
    ∀ j < 9, permChk 42 (heInnerSigma1.getD j #[]) = true :=
  ⟨fun _ hj => (bind_facts (atX0 hj)).2.1, fun _ hj => (bind_facts (atX1 hj)).2.1⟩

end CertificateChecks.KernelSporSch.HeX14

end
