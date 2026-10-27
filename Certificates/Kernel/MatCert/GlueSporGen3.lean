module

public import Certificates.Kernel.MatCert.SporGen3
public import Certificates.Kernel.MatCert.Glue
public import CFSG.Certificates.Kernel.OpsMcertBSound
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMB CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.KC.Ord CFSG.KS.SporSch.LyM
open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint
open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThFive
open CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis

theorem seedCert_of_B {M V₀ V : Type} [Inhabited M] {O₀ : Ops M V₀} {O : Ops Nat V}
    (H : Hom O₀ O) {sA sB : String} {A B : Nat} (eA : O₀.decode sA = H.U A)
    (eB : O₀.decode sB = H.U B) (hA : H.P A) (hB : H.P B) {C : MCert}
    (h : seedRunB O A B C = true) : seedCertCheck O₀ sA sB C = true := by
  obtain ⟨n, prog, fs⟩ := C
  obtain ⟨h2, h⟩ := seedRunB_sound O h
  have hn : 2 ≤ n := h2
  obtain ⟨hm, h0, h1⟩ := seeds_of_N H eA eB hA hB (rA := 0) (rB := 1) (by omega) (by omega) h
  unfold seedCertCheck
  simp only [Bool.and_eq_true]
  exact ⟨⟨hm, h0⟩, h1⟩

theorem sg3ThCheck : seedCertCheck (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2
    thLineCert = true :=
  seedCert_of_B (hom2 248 (by norm_num)) thA thB trivial trivial sg3Th_K

theorem sg3J2Check : seedCertCheck (opsP 5 14) NativeSporadic.J2Seed1 NativeSporadic.J2Seed2
    j2Cert = true := by
  have h := sg3J2_K
  rw [forceB_eq, forceB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hA, hB⟩, h⟩ := h
  refine seedCert_of_B (homP j2Consts (by norm_num)) ?_ ?_ hA hB h
  · rw [J2S1.eq]
    exact payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)
  · rw [J2S2.eq]
    exact payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)

theorem sg3HeCheck : seedCertCheck (opsP 7 50) NativeSporadic.HeSeed1 NativeSporadic.HeSeed2
    heCert = true := by
  have h := sg3He_K
  rw [forceB_eq, forceB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hA, hB⟩, h⟩ := h
  refine seedCert_of_B (homP heConsts (by norm_num)) ?_ ?_ hA hB h
  · rw [HeS1.eq]
    exact payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)
  · rw [HeS2.eq]
    exact payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)

theorem sg3RuCheck : seedCertCheck (ops2 28) NativeSporadic.RuSeed1 NativeSporadic.RuSeed2
    ruCert = true :=
  seedCert_of_B (hom2 28 (by norm_num)) ruA ruB trivial trivial sg3Ru_K

theorem sg3J4Check : seedCertCheck (ops2 112) NativeSporadic.J4Seed1 NativeSporadic.J4Seed2
    j4Cert = true :=
  seedCert_of_B (hom2 112 (by norm_num)) j4A j4B trivial trivial sg3J4_K

end CertificateChecks.KernelMC

end
