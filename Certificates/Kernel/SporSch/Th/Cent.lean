
module

public import Certificates.Kernel.SporSch.Th.GenStr
public import Certificates.Kernel.Sporadic.RawGen
public import CFSG.Certificates.Kernel.SporSch.ThTextSound
public import CFSG.Sporadic.ThSchreier.CentralizerDataInputs
public import CFSG.Sporadic.ThSchreier.LocalDataInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_strof CertificateChecks.KernelSporSch.ThFix CFSG.Sporadic.ThSchreier.centFixedIdx
#kss_strof CertificateChecks.KernelSporSch.ThImg CFSG.Sporadic.ThSchreier.centImageIdx
#kss_strof CertificateChecks.KernelSporSch.ThImgR CFSG.Sporadic.ThSchreier.centImageRows
#kss_strof CertificateChecks.KernelSporSch.ThPar CFSG.Sporadic.ThSchreier.centOrbitPar
#kss_strof CertificateChecks.KernelSporSch.ThLab CFSG.Sporadic.ThSchreier.centOrbitLab
#kss_strof CertificateChecks.KernelSporSch.ThEdg CFSG.Sporadic.ThSchreier.centOrbitEdges
#ks_chars CertificateChecks.KernelSporSch.ThRows CFSG.Sporadic.ThSchreier.localRowsTxt

namespace CertificateChecks.KernelSporSch.ThCent

open CFSG.KS.SporSch CFSG.Sporadic.ThSchreier CertificateChecks.KernelSporSch

@[expose] def NV : Nat := 2 ^ 250

theorem sFix : Nat.beq (thScanK false NV NV ThFix.chars) (4 * 10200) = true := by quickRfl
theorem sImg : Nat.beq (thScanK false NV 120754 ThImg.chars) (4 * 120 + 2) = true := by quickRfl
theorem sImgR : Nat.beq (thScanK true (2 ^ 248) NV ThImgR.chars) (4 * 240) = true := by quickRfl
theorem sPar : Nat.beq (thScanK false NV NV ThPar.chars) (4 * 819) = true := by quickRfl
theorem sLab : Nat.beq (thScanK false NV NV ThLab.chars) (4 * 819) = true := by quickRfl
theorem sEdg : Nat.beq (thScanK false NV NV ThEdg.chars) (4 * 1638) = true := by quickRfl
theorem sRows : Nat.beq (thScanK true (2 ^ 248) NV ThRows.chars) (4 * 2457) = true := by quickRfl

theorem scan_of {hex : Bool} {B v N f : Nat} {cs : List Char}
    (h : Nat.beq (thScanK hex B v cs) (4 * N + 2 * f) = true) (hf : f < 2) :
    let L := if hex then hexsOf (String.ofList cs) else natsOf (String.ofList cs)
    L.length = N ∧ (∀ n ∈ L, n < B) ∧ (v ∈ L ↔ f = 1) := by
  have e := Nat.eq_of_beq_eq_true h
  have h0 : thScanK hex B v cs % 2 = 0 := by omega
  obtain ⟨h1, h2, h3⟩ := thScan_sound h0
  refine ⟨by rw [h1]; omega, h2, ?_⟩
  rw [h3, e]
  constructor
  · intro hx
    omega
  · intro hx
    omega

theorem scan0 {hex : Bool} {B v N : Nat} {cs : List Char}
    (h : Nat.beq (thScanK hex B v cs) (4 * N) = true) :
    let L := if hex then hexsOf (String.ofList cs) else natsOf (String.ofList cs)
    L.length = N ∧ (∀ n ∈ L, n < B) :=
  have h' : Nat.beq (thScanK hex B v cs) (4 * N + 2 * 0) = true := h
  ⟨(scan_of h' (by omega)).1, (scan_of h' (by omega)).2.1⟩

theorem facts2309 : centFixedIdx.length = 10200 ∧ centImageIdx.length = 120 ∧
    centImageRows.length = 240 ∧ (∀ n ∈ centImageRows, n < 2 ^ 248) ∧ centOrbitPar.length = 819 ∧
    centOrbitLab.length = 819 ∧ centOrbitEdges.length = 1638 := by
  rw [ThFix.eq, ThImg.eq, ThImgR.eq, ThPar.eq, ThLab.eq, ThEdg.eq]
  exact ⟨(scan0 sFix).1, (scan_of (f := 1) sImg (by omega)).1, (scan0 sImgR).1, (scan0 sImgR).2,
    (scan0 sPar).1, (scan0 sLab).1, (scan0 sEdg).1⟩

theorem facts2312 : localRowNats.length = 2457 ∧ ∀ n ∈ localRowNats, n < 2 ^ 248 := by
  rw [localRowNats, ThRows.eq]
  exact scan0 sRows

theorem facts2317 : 120754 ∈ centImageIdx := by
  rw [ThImg.eq]
  exact (scan_of (f := 1) sImg (by omega)).2.2.2 rfl

end CertificateChecks.KernelSporSch.ThCent

end
