module

public import Certificates.Kernel.LocalComp.L34Graph.Chk
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.Certificates.Kernel.L34GraphSound
import CFSG.Certificates.Kernel.L34ScanSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CertificateChecks.KernelLC.L34Graph

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34Graph CFSG.KC.L34W CFSG.KC.L34Scan
open CertificateChecks.KernelLC CertificateChecks.KernelLC.L34X CertificateChecks.KernelLC.L34Cert
open CFSG.PSL3Four.Native CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.KLie.CT (andB)

theorem gensG22210 : GensG L34R.G := fun _ hj => ⟨g_eq hj, cnG hj⟩

theorem all_pts_toList {N : Nat} {T : Nat → Nat} {f : Tab → Bool}
    (h : ∀ i < N, f (unpack 42 6 (T i)) = true) : (pts 42 6 N T).toList.all f = true := by
  refine List.all_eq_true.2 fun x hx => ?_
  rw [Array.mem_toList_iff, Array.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hi' : i < N := by rwa [size_pts] at hi
  rw [pts_getElem hi']
  exact h i hi'

theorem orb_all {o N : Nat} (ho : o < 4) (hN : N = L34O.N o)
    (h : allN N (fun i => strictB (L34O.T o i)
      (invK (tgK L34R.G 4) (tgK L34R.G 8) [pxK L34R.G 0, pxK L34R.G 1, pxK L34R.G 2])) = true) :
    (pts 42 6 N (L34O.T o)).toList.all (invertOK xAll) = true := by
  refine all_pts_toList fun i hi => ?_
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h i hi
  rw [strictB_app] at h'
  exact invertOK_of gensG22210 (hOc o ho i (by rw [← hN]; exact hi)) h'

theorem graphOK_true : graphOK = true := by
  have hg := kGraph22210
  unfold graphK at hg
  rw [strictB_app, strictB_app, forceL_eq, forceL_eq, forceL_eq] at hg
  obtain ⟨g1, hg⟩ := andB_iff.1 hg
  obtain ⟨g2, g3⟩ := andB_iff.1 hg
  unfold graphOK
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  rw [hO1.1, hO2.1, hO3.1, kBits22210, decompOK_of gensG22210 kDec22210,
    orb_all (o := 1) (N := 360) (by decide) rfl g1, orb_all (o := 2) (N := 1008) (by decide) rfl g2,
    orb_all (o := 3) (N := 280) (by decide) rfl g3]
  rfl

end CertificateChecks.KernelLC.L34Graph

end
