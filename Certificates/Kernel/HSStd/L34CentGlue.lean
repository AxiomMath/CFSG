module

public import Certificates.Kernel.HSStd.L34CentChecks
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.Certificates.Kernel.L34InvSound
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HL34Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.HFIL34Data
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.BfsPinSetSound
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.BfsReplay

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelHSStd.L34C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Inv
open CertificateChecks.KernelLC CertificateChecks.KernelLC.L34X CertificateChecks.KernelLC.L34Cert
open CFSG.PSL3Four.Native
open CFSG.KLie.CT (andB orB notB anyN)

theorem kCentK : centK 42 6 241920 L34R.T (RP 2) 240 X P = true := by
  have he := kEnds
  simp only [Bool.and_eq_true] at he
  exact centK_of_slices (L := 1344) (K := 180) (CC := CC) rfl (fun s hs => csAll s hs)
    (Nat.eq_of_beq_eq_true he.1) (Nat.eq_of_beq_eq_true he.2) kList

theorem cent3 : centTabs 42 (pts 42 6 241920 L34R.T) r₃T = pts 42 6 240 P :=
  cent_sound r3_eq (cnRP (by decide)) pinR.canon kCentK

theorem canonP : ∀ k < 240, canonK 42 6 (mask 6) (42 * 6) (P k) = true := by
  intro k hk
  have h := CFSG.KS.Raw.Orb.allN_iff.1 kList k hk
  rw [CFSG.KC.BfsPin.strictB_app, CFSG.KC.L34KSnd.andB_iff] at h
  obtain ⟨h1, h2⟩ := h
  obtain ⟨-, h3⟩ := CFSG.KC.L34KSnd.andB_iff.1 h2
  obtain ⟨-, h4⟩ := CFSG.KC.L34KSnd.andB_iff.1 h3
  rw [Nat.eq_of_beq_eq_true h4]
  exact pinR.canon _ (Nat.blt_eq.mp h1)

theorem hl34_true :
    CFSG.EvenSporadicStandard.HSStd.HL34.hl34Check (enumBFS 42 gTabs 241920).tabs
      (orbitBFS 42 gTabs (gTabs.map (invTab 42)) r₂T 1963).tabs
      (orbitBFS 42 gTabs (gTabs.map (invTab 42)) r₄T 1963).tabs = true := by
  rw [hR.1, hO1.1, hO3.1]
  unfold CFSG.EvenSporadicStandard.HSStd.HL34.hl34Check
  simp only []
  rw [cent3, r3_eq]
  have hr := cnRP (j := 2) (by decide)
  have hc2 : ∀ i < 360, canonK 42 6 (mask 6) (42 * 6) (L34O.T 1 i) = true := hOc 1 (by decide)
  have hc4 : ∀ i < 280, canonK 42 6 (mask 6) (42 * 6) (L34O.T 3 i) = true := hOc 3 (by decide)
  have hK := kHL
  unfold hl34K at hK
  rw [CFSG.KC.BfsPin.strictB_app, CFSG.KS.Raw.Orb.allN_iff] at hK
  rw [CFSG.KS.BfsReplay.allBelow_iff]
  intro k hk
  rw [pts_size] at hk
  have hx := canonP k hk
  have h := hK k hk
  rw [CFSG.KC.BfsPin.strictB_app, CFSG.KC.BfsPin.strictB_app] at h
  have hf := anyBelow_filter_pts (n := 42) (w := 6) (m := 240) (CT := P)
    (fun w => !(w == idTab 42) && powTab 42 w 3 == idTab 42)
    (fun y => comp 42 y (unpack 42 6 (P k)) == comp 42 (unpack 42 6 (P k)) y)
    (fun j => strictB (P j) fun y => andB (ord3K 42 6 (pidn 42 6) y)
      (Nat.beq (pcomp 42 6 (mask 6) y (P k)) (pcomp 42 6 (mask 6) (P k) y))) (by
      intro j hj
      have hy := canonP j hj
      rw [beq_id hy, pow3_id hy, comm_beq hx hy, CFSG.KC.BfsPin.strictB_app]
      unfold ord3K
      simp only [andB_eq, notB_eq])
  rw [pts_get' hk, hf, sq_id hx, beq_id hx, beq_r hx hr, CFSG.KC.L34KSnd.comp_unpack' hr hx,
    memTab_pts hc2 hx, memTab_pts hc4 hx, memTab_pts hc2 (CFSG.KC.BfsPin.canonK_pcomp hr hx),
    memTab_pts hc4 (CFSG.KC.BfsPin.canonK_pcomp hr hx)]
  unfold invNeK at h
  simp only [andB_eq, orB_eq, notB_eq, Bool.and_assoc, Bool.or_assoc] at h ⊢
  exact h

theorem hfi34_true :
    CFSG.EvenSporadicStandard.HSStd.HFI.hfi34Check (enumBFS 42 gTabs 241920).tabs
      (orbitBFS 42 gTabs (gTabs.map (invTab 42)) r₃T 1963).tabs = true := by
  rw [hR.1, hO2.1]
  unfold CFSG.EvenSporadicStandard.HSStd.HFI.hfi34Check
  simp only []
  rw [cent3, r3_eq]
  have hr := cnRP (j := 2) (by decide)
  have hc3 : ∀ i < 1008, canonK 42 6 (mask 6) (42 * 6) (L34O.T 2 i) = true := hOc 2 (by decide)
  have hK := kHFI
  unfold hfi34K at hK
  rw [CFSG.KC.BfsPin.strictB_app, CFSG.KS.Raw.Orb.allN_iff] at hK
  rw [CFSG.KS.BfsReplay.allBelow_iff]
  intro k hk
  rw [pts_size] at hk
  have hx := canonP k hk
  have h := hK k hk
  rw [CFSG.KC.BfsPin.strictB_app] at h
  rw [pts_get' hk, sq_id hx, beq_id hx, beq_r hx hr, CFSG.KC.L34KSnd.comp_unpack' hr hx,
    memTab_pts hc3 hx, memTab_pts hc3 (CFSG.KC.BfsPin.canonK_pcomp hr hx)]
  unfold invNeK at h
  simp only [andB_eq, orB_eq, notB_eq, Bool.and_assoc, Bool.or_assoc] at h ⊢
  exact h

end CertificateChecks.KernelHSStd.L34C

end
