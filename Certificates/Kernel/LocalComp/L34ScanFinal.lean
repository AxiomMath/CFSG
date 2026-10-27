module

public import Certificates.Kernel.LocalComp.L34ScanChk
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.Certificates.Kernel.L34ScanSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CertificateChecks.KernelLC.L34Scan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34Scan
open CertificateChecks.KernelLC.L34X CertificateChecks.KernelLC.L34Cert CFSG.PSL3Four.Native
open CFSG.KLie.CT (andB)

theorem canonC : (∀ c < 64, canonK 42 6 (mask 6) (42 * 6) (L34C1.P c) = true) ∧
    (∀ c < 168, canonK 42 6 (mask 6) (42 * 6) (L34C2.P c) = true) ∧
    (∀ c < 60, canonK 42 6 (mask 6) (42 * 6) (L34C3.P c) = true) := by
  obtain ⟨h1, h⟩ := andT kCanonC
  obtain ⟨h2, h3⟩ := andT h
  exact ⟨CFSG.KS.Raw.Orb.allN_iff.1 h1, CFSG.KS.Raw.Orb.allN_iff.1 h2,
    CFSG.KS.Raw.Orb.allN_iff.1 h3⟩

theorem strictB_app2 (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem twoCentral_true : CFSG.ComponentClassification.GrSLit.twoCentralOK
    (enumBFS 42 gTabs 241920).tabs (centTabs 42 (enumBFS 42 gensS 20160).tabs (r₁T ())) =
      true := by
  rw [hR.1, hS.1, cent1]
  refine twoCentralOK_of pinR.canon canonC.1 ?_
  intro i hi
  have h := scanSl_spec (f := twoK 42 6 64 L34C1.P (pidn 42 6)) (L := 1344) (K := 180)
    (by decide) (by decide) (fun s hs => by
      have h1 := two1All s hs
      unfold two1 at h1
      rwa [strictB_app2] at h1) i hi
  exact h

theorem fix_true :
    CFSG.ComponentClassification.CatFactsL4U4.fixCheck (enumBFS 42 gTabs 241920).tabs
        (centTabs 42 (enumBFS 42 gensS 20160).tabs r₂T) r₂T = true ∧
      CFSG.ComponentClassification.CatFactsL4U4.fixCheck (enumBFS 42 gTabs 241920).tabs
        (centTabs 42 (enumBFS 42 gensS 20160).tabs r₃T) r₃T = true := by
  rw [hR.1, hS.1, cent2, cent3, r2_eq, r3_eq]
  refine ⟨fixCheck_of pinR.canon canonC.2.1 (cnRP (by decide)) ?_,
    fixCheck_of pinR.canon canonC.2.2 (cnRP (by decide)) ?_⟩
  · exact scanSl_spec (L := 1344) (K := 180) (by decide) (by decide) fun s hs => by
      have h1 := fix2All s hs
      unfold fix2 at h1
      rwa [strictB_app2, strictB_app2] at h1
  · exact scanSl_spec (L := 1344) (K := 180) (by decide) (by decide) fun s hs => by
      have h1 := fix3All s hs
      unfold fix3 at h1
      rwa [strictB_app2, strictB_app2] at h1

end CertificateChecks.KernelLC.L34Scan

end
