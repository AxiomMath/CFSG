module

public import Certificates.Kernel.ONSeven.RGlueC
public import CFSG.Certificates.Kernel.Spor.ONSevenRChecks

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ONR

open CFSG.KC.ONR CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.ONR CFSG.KS.ONOrb CFSG.KC.B3S3K
  CFSG.KC.BfsPin CFSG.KC.Misc.ArrEnum CFSG.RankThree.Native
open CertificateChecks.KernelSpor.ON8 (onP)

theorem lt7 {s : Nat} (h : s < 7) : s < nat_lit 7 := h

theorem lt8 {s : Nat} (h : s < 8) : s < nat_lit 8 := h

theorem kb_lt {N : Nat} (h : 3 ≤ N) : ∀ p ∈ kbA.toList, p < N := by
  intro p hp
  simp [kbA] at hp
  omega

theorem ccheck_full {r N w k sz NE : Nat} {T G D S GE TE E SE : Nat → Nat} {SK : List Nat}
    (hr5 : r < 5) (hk : (onSevenCArrs r).size = k) (ho : orbK N w k T G D S = true)
    (hres : ∀ s < (cAll r).size, resK N w T (cF r s) (G s) = true)
    (hcomm : ∀ j < (onSevenCArrs r).size, onP (fun y => cF r j (cF r (onSevenCArrs r).size y))
      (fun y => cF r (onSevenCArrs r).size (cF r j y)) = true)
    (hw : szOK N w = true) (hGE : ∀ s < k, GE s = G s) (hp : ∀ s < k, permB N w (G s) = true)
    (hbk : bfsK N w k GE NE TE E SE = true) (hK : keysSK N w kbA.toList NE TE SK = true)
    (hf : NE ≤ 1400) (hsz : NE = sz) :
    onSevenCCheck (onSevenCR r) (onSevenRepArr r) (onSevenCArrs r) (onSevenCTabs r)
      (onSevenCCert r) sz = true := by
  obtain ⟨hR, hres', hB, -⟩ := cRes hr5 hk ho hres
  have O := orbK_spec ho
  unfold onSevenCCert onSevenCTabs
  rw [hR]
  have hRs : (Array.ofFn (n := N) fun i => T i.val).size = N := Array.size_ofFn
  rw [hRs]
  have hGE' : BindA N w ((onSevenCArrs r).map (onSevenTab (Array.ofFn (n := N) fun i => T i.val)))
      k GE := ⟨hB.1, fun j hj => by rw [hB.2 j hj, hGE j hj]⟩
  have hE := enum_of (fuel := 1400) hGE' (fun j hj => by rw [hGE j hj]; exact hp j hj) hbk
    (kb_lt O.three_le) hK hf
  have hkeys : kbA.toList = onSevenKeys := rfl
  rw [hkeys] at hE
  refine ccheck_of hres' (comm_of hr5 hcomm) (by rw [hRs]; exact hE.1) (by rw [hE.2.1, hsz])

theorem fcheck_full {r N w k nf NE NF : Nat} {T G D S GE TE E SE GF TF EF SF X : Nat → Nat}
    {SK SKF : List Nat} (hr3 : r < 3) (hk : (onSevenCArrs r).size = k)
    (hnf : (onSevenFArrs r).size = nf) (ho : orbK N w k T G D S = true)
    (hres : ∀ s < (cAll r).size, resK N w T (cF r s) (G s) = true)
    (hw : szOK N w = true) (hGE : ∀ s < k, GE s = G s)
    (hp : ∀ s < k + 1 + nf, permB N w (G s) = true)
    (hbk : bfsK N w k GE NE TE E SE = true) (hK : keysSK N w kbA.toList NE TE SK = true)
    (hf : NE ≤ 1400)
    (hGF : ∀ l < nf, GF l = G (k + 1 + l))
    (hbf : bfsK N w nf GF NF TF EF SF = true) (hKF : keysSK N w kbA.toList NF TF SKF = true)
    (hNF : NF = 343) (hX : X 1 = G k) (hpx : powsK N w (X 1) X 7 = true)
    (hfk : fK N NE 343 w k nf TE TF G (fun l => G (k + 1 + l)) X = true) :
    onSevenFCheck (onSevenCR r) (onSevenCTabs r) (onSevenCCert r) (onSevenFArrs r)
      (onSevenFTabs r) (onSevenRepTab r) (onSevenFCert r) = true := by
  obtain ⟨hR, -, hB, hx⟩ := cRes (by omega) hk ho hres
  obtain ⟨hresF, hBF⟩ := fRes hr3 hk ho hres
  have O := orbK_spec ho
  rw [hnf] at hBF
  unfold onSevenCCert onSevenCTabs onSevenFCert onSevenFTabs onSevenRepTab
  rw [hR]
  have hRs : (Array.ofFn (n := N) fun i => T i.val).size = N := Array.size_ofFn
  rw [hRs]
  have hGp : ∀ j < k, permB N w (G j) = true := fun j hj => hp j (by omega)
  have hGE' : BindA N w ((onSevenCArrs r).map (onSevenTab (Array.ofFn (n := N) fun i => T i.val)))
      k GE := ⟨hB.1, fun j hj => by rw [hB.2 j hj, hGE j hj]⟩
  have hGEp : ∀ j < k, permB N w (GE j) = true := fun j hj => by rw [hGE j hj]; exact hGp j hj
  have hE := enum_of (fuel := 1400) hGE' hGEp hbk (kb_lt O.three_le) hK hf
  have hFp : ∀ l < nf, permB N w (G (k + 1 + l)) = true := fun l hl => hp _ (by omega)
  have hGF' : BindA N w ((onSevenFArrs r).map (onSevenTab (Array.ofFn (n := N) fun i => T i.val)))
      nf GF := ⟨hBF.1, fun l hl => by rw [hBF.2 l hl, hGF l hl]⟩
  have hGFp : ∀ l < nf, permB N w (GF l) = true := fun l hl => by rw [hGF l hl]; exact hFp l hl
  have hEF := enum_of (fuel := 400) hGF' hGFp hbf (kb_lt O.three_le) hKF (by omega)
  have hkeys : kbA.toList = onSevenKeys := rfl
  rw [hkeys] at hE hEF
  refine fcheck_of hw hRs hresF hEF.1 (by rw [hEF.2.1, hNF])
    (fun i hi => hEF.2.2 i (by omega)) (fun i hi => perm_pts hw hGFp hbf i (by omega))
    hE.2.1 hE.2.2 (perm_pts hw hGEp hbk) hB hGp hBF hFp (by rw [hx, hX]) hpx hfk

end CertificateChecks.KernelSpor.ONR

end
