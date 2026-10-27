module

public import Certificates.Kernel.LocalQT.He4148.Chains
public import Certificates.Kernel.Sporadic.OddCore.HLF
public import CFSG.Sporadic.SmallOddCore.ClassSimple
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLQT.He4148

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.KC.BfsPin
open CFSG.QuasithinUnique.Id2519.HeInner CFSG.Sporadic.SmallOddCore CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four

theorem bK : bindsK 105 7 KernelSpor.HKE.G KernelSpor.HKI heSigmaP 0 = true := by quickRfl

theorem sDG : allN 5 (fun j => siftK 105 7 (mask 7) (105 * 7) (pidn 105 7) DQ.LR DQ.TRI DQ.BP 3 0
    (KernelSpor.HDE.G j)) = true := by quickRfl

theorem delta_eq : heDeltaP = heOmega0 := rfl

theorem sig_eq {j : Nat} (hj : j < 9) : heSigmaP.getD j #[] = heKGens[j]! := by
  have h := bindsK_spec bK j (by rw [len_X]; exact hj)
  rw [Nat.zero_add] at h
  rw [(bind_facts h).1, KernelSpor.HeL.kgens_get hj]

theorem p105 : incListOK 8330 105 heDeltaP = true ∧
    ∀ j < 9, permChk 105 (heSigmaP.getD j #[]) = true ∧
      agreeOK 105 (heInnerC0 j) heDeltaP (heSigmaP.getD j #[]) = true := by
  rw [delta_eq]
  refine ⟨KernelSpor.HeL.inc_ok, fun j hj => ?_⟩
  rw [sig_eq hj]
  exact ⟨(KernelSpor.HeL.k_first j hj).1, (KernelSpor.HeL.k_first j hj).2.2⟩

theorem dgen_facts {j : Nat} (hj : j < 5) : permChk 105 heDGens[j]! = true ∧
    Rep 105 (unpack 105 7 (KernelSpor.HDE.G j)) (permOrId 105 heDGens[j]!) := by
  obtain ⟨-, -, h1, h2, -, -⟩ := KernelSpor.HeL.dg_facts hj
  obtain ⟨hc, hr, -⟩ := unpack_facts (KernelSpor.HeL.dgens_get hj) h1 h2
  exact ⟨hc, hr⟩

theorem d_sift : ∀ j < 5, heDp.sift (permOrId 105 heDGens[j]!) 0 = true := fun j hj =>
  sift_D (KernelSpor.HeL.dg_facts hj).2.1 (dgen_facts hj).2 (allN_spec sDG j hj)

theorem dgens_size : heDGens.size = 5 := by
  simp [heDGens]

theorem d_tabRep : ∀ j < heDGens.size, TabRep heDGens[j]! (permOrId 105 heDGens[j]!) := by
  intro j hj
  have hj5 : j < 5 := dgens_size ▸ hj
  refine ⟨?_, (permChk_spec (dgen_facts hj5).1).1⟩
  rw [KernelSpor.HeL.dgens_get hj5]
  exact unpack_size' _ _ _

theorem d_cert : ClassCert 105 heDGens heDInvs heDEnum 10 heDClassWords heDClassSizes
    heDOrbits := by
  obtain ⟨-, -, ⟨hD, -, -⟩, ⟨hO, -, horb, hnot, hw, h0⟩, hcov, -⟩ := KernelSpor.HeL.facts2275
  refine ⟨hD, hw, h0, horb, hnot, fun k hk => ?_⟩
  obtain ⟨l, hl, hf⟩ := cover_of_coverAllOK hcov k hk
  exact ⟨l, hO ▸ hl, hf⟩

theorem d_card : heDEnum.tabs.size = 20160 := KernelSpor.HeL.facts2275.2.2.1.2.1

theorem dp_classes : (∀ j < 5, heDp.sift (permOrId 105 heDGens[j]!) 0 = true) ∧
    ClassCert 105 heDGens heDInvs heDEnum 10 heDClassWords heDClassSizes heDOrbits ∧
    (∀ j < heDGens.size, TabRep heDGens[j]! (permOrId 105 heDGens[j]!)) ∧
    heDEnum.tabs.size = 20160 :=
  ⟨d_sift, d_cert, d_tabRep, d_card⟩

end CertificateChecks.KernelLQT.He4148

end
