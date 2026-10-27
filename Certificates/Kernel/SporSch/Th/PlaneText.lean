module

public import Certificates.Kernel.SporSch.Th.Cent
public import Certificates.Kernel.SporSch.Th.GenV4
public import CFSG.Sporadic.ThSchreier.PlaneChainDataInputs
public import CFSG.Sporadic.ThSchreier.PlaneSepDataInputs
meta import CFSG.Sporadic.ThSchreier.PlaneSepDataInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_strof CertificateChecks.KernelSporSch.ThCSR CFSG.Sporadic.ThSchreier.chainSmallRows
#kss_strof CertificateChecks.KernelSporSch.ThCP0 CFSG.Sporadic.ThSchreier.chainPerm0
#kss_strof CertificateChecks.KernelSporSch.ThCP1 CFSG.Sporadic.ThSchreier.chainPerm1
#kss_strof CertificateChecks.KernelSporSch.ThSF CFSG.Sporadic.ThSchreier.sepFNats
#kss_strof CertificateChecks.KernelSporSch.ThSW CFSG.Sporadic.ThSchreier.sepWords
#kss_strof CertificateChecks.KernelSporSch.ThSR CFSG.Sporadic.ThSchreier.sepRowNats

namespace CertificateChecks.KernelSporSch.ThPlane

open CFSG.KS.SporSch CFSG.Sporadic.ThSchreier CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.ThCent

meta def swFlat : List Nat := sepWords.flatMap fun w => w.length :: w.map Int.toNat

#kss_natlist CertificateChecks.KernelSporSch.ThPlane.SWN swFlat

theorem sCSR : Nat.beq (thScanK true (2 ^ 248) NV ThCSR.chars) (4 * 108) = true := by quickRfl
theorem sCP0 : Nat.beq (thScanK false NV NV ThCP0.chars) (4 * 54) = true := by quickRfl
theorem sCP1 : Nat.beq (thScanK false NV NV ThCP1.chars) (4 * 54) = true := by quickRfl
theorem sSF : Nat.beq (thScanK true (2 ^ 248) NV ThSF.chars) (4 * 248) = true := by quickRfl
theorem sSR : Nat.beq (thScanK true (2 ^ 248) NV ThSR.chars) (4 * 248) = true := by quickRfl
theorem bSW : Nat.beq (thBindK false SWN ThSW.chars) (2 * 1110) = true := by quickRfl

theorem negCSR : (!Nat.beq (thScanK true (2 ^ 248) NV ThCSR.chars) (4 * 107)) = true := by
  quickRfl
theorem negSW : (!Nat.beq (thBindK false SWN ThSW.chars) (2 * 1109)) = true := by quickRfl

theorem kW : (decodeWords 124 ((List.range 1110).map SWN)).length = 124 ∧
    (∀ w ∈ decodeWords 124 ((List.range 1110).map SWN), ∀ l ∈ w, l = 1 ∨ l = 2) ∧
    (decodeWords 124 ((List.range 1110).map SWN)).getD 0 [] = [] := by
  decide +kernel

theorem sw_eq : natsOf (String.ofList ThSW.chars) = (List.range 1110).map SWN := by
  have e := Nat.eq_of_beq_eq_true bSW
  obtain ⟨h1, h2⟩ := thBind_sound (hex := false) (R := SWN) (cs := ThSW.chars) (by rw [e])
  simp only [Bool.false_eq_true, if_false, e] at h1 h2
  apply List.ext_getElem
  · simp [h1]
  · intro t ht _
    have := h2 t ht
    simpa [List.getD_eq_getElem?_getD, ht] using this

theorem facts2316 : chainSmallRows.length = 108 ∧ (∀ n ∈ chainSmallRows, n < 2 ^ 248) ∧
    chainPerm0.length = 54 ∧ chainPerm1.length = 54 := by
  rw [ThCSR.eq, ThCP0.eq, ThCP1.eq]
  exact ⟨(scan0 sCSR).1, (scan0 sCSR).2, (scan0 sCP0).1, (scan0 sCP1).1⟩

theorem facts2319 : sepFNats.length = 248 ∧ (∀ n ∈ sepFNats, n < 2 ^ 248) ∧
    sepWords.length = 124 ∧ (∀ w ∈ sepWords, ∀ l ∈ w, l = 1 ∨ l = 2) ∧
    sepRowNats.length = 248 ∧ (∀ n ∈ sepRowNats, n < 2 ^ 248) ∧ sepWords.getD 0 [] = [] := by
  rw [ThSF.eq, ThSR.eq, ThSW.eq, sw_eq]
  exact ⟨(scan0 sSF).1, (scan0 sSF).2, kW.1, kW.2.1, (scan0 sSR).1, (scan0 sSR).2, kW.2.2⟩

end CertificateChecks.KernelSporSch.ThPlane

end
