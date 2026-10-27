module

public import Certificates.Kernel.MatCert.J4Mcert
public import Certificates.Kernel.MatCert.RuMcert
public import Certificates.Kernel.MatCert.ThThree
public import Certificates.Kernel.MatCert.J4Fix
public import Certificates.Kernel.MatCert.Fp
public import CFSG.Certificates.Kernel.OpsMcertNSound
public import CFSG.Certificates.Kernel.OpsFpKSound
public import CFSG.Certificates.Kernel.OpsF2FrMcert
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMC

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsHom CFSG.KC.Ord CFSG.KS.SporSch.LyM
open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3
open CFSG.RankThree.PartTwo.Sec4.ONanJ4Nine CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
open CFSG.Blueprint

theorem decode2 {cs : List Char} {d M : Nat} (h : CFSG.KC.M1F2.m1Bind cs d M = true) :
    (ops2 d).decode (String.ofList cs) = CFSG.KC.Co1F2.unpackR d M :=
  CFSG.KC.Co1F2.bind_sound h

theorem thA : (ops2 248).decode NativeSporadic.ThSeed1 = CFSG.KC.Co1F2.unpackR 248 KernelLC.ThA.M := by
  have e : NativeSporadic.ThSeed1 = String.ofList KernelLC.ThA.chars :=
    (rfl : NativeSporadic.ThSeed1 = KernelLC.thSeedA).trans KernelLC.ThA.eq
  rw [e]
  exact decode2 KernelLC.ThA.bind

theorem thB : (ops2 248).decode NativeSporadic.ThSeed2 = CFSG.KC.Co1F2.unpackR 248 KernelLC.ThB.M := by
  have e : NativeSporadic.ThSeed2 = String.ofList KernelLC.ThB.chars :=
    (rfl : NativeSporadic.ThSeed2 = KernelLC.thSeedB).trans KernelLC.ThB.eq
  rw [e]
  exact decode2 KernelLC.ThB.bind

theorem j4A : (ops2 112).decode NativeSporadic.J4Seed1 = CFSG.KC.Co1F2.unpackR 112 JA.M := by
  rw [JA.eq]
  exact decode2 JA.bind

theorem j4B : (ops2 112).decode NativeSporadic.J4Seed2 = CFSG.KC.Co1F2.unpackR 112 JB.M := by
  rw [JB.eq]
  exact decode2 JB.bind

theorem ruA : (ops2 28).decode NativeSporadic.RuSeed1 =
    CFSG.KC.Co1F2.unpackR 28 KernelSRHS.RA.M := by
  rw [KernelSRHS.RA.eq]
  exact decode2 KernelSRHS.RA.bind

theorem ruB : (ops2 28).decode NativeSporadic.RuSeed2 =
    CFSG.KC.Co1F2.unpackR 28 KernelSRHS.RB.M := by
  rw [KernelSRHS.RB.eq]
  exact decode2 KernelSRHS.RB.bind

theorem j4Mcert : mcertCheck (ops2fr 112) NativeSporadic.J4Seed1 NativeSporadic.J4Seed2
    CFSG.RankThree.Asc83Table.J4.j4Cert = true := by
  rw [CFSG.KC.OpsF2K.mcertCheck_fr_eq]
  exact mcertCheck_of_N (hom2 112 (by norm_num)) j4A j4B trivial trivial j4_K

theorem ruMcert : mcertCheck (ops2fr 28) NativeSporadic.RuSeed1 NativeSporadic.RuSeed2
    CFSG.RankThree.Asc83Table.Ru.ruCert = true := by
  rw [CFSG.KC.OpsF2K.mcertCheck_fr_eq]
  exact mcertCheck_of_N (hom2 28 (by norm_num)) ruA ruB trivial trivial ru_K

theorem thTz : tzCheck (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 thThreeN
    thThreeProg thTzSpec = true := by
  obtain ⟨hm, h0, h1⟩ := seeds_of_N (hom2 248 (by norm_num)) thA thB trivial trivial
    (fs := thTzSpec.facts) (rA := 0) (rB := 1) (by decide) (by decide)
    thTz_K
  unfold tzCheck
  rw [hm, h0, h1]
  decide +kernel

theorem thCz : czCheck (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 thThreeN
    thThreeProg thCzSpec = true := by
  obtain ⟨hm, h0, h1⟩ := seeds_of_N (hom2 248 (by norm_num)) thA thB trivial trivial
    (fs := thCzSpec.facts) (rA := 0) (rB := 1) (by decide) (by decide)
    thCz_K
  unfold czCheck
  rw [hm, h0, h1]
  decide +kernel

theorem j4Fix : fixCheck (ops2 112) NativeSporadic.J4Seed1 NativeSporadic.J4Seed2 j4Nregs j4Prog
    j4Spec = true := by
  have hA : j4Spec.rA < j4Nregs := by decide +kernel
  have hB : j4Spec.rB < j4Nregs := by decide +kernel
  obtain ⟨hm, h0, h1⟩ := seeds_of_N (hom2 112 (by norm_num)) j4A j4B trivial trivial
    (fs := j4Spec.facts) hA hB j4Fix_K
  unfold fixCheck
  rw [hm, h0, h1, decide_eq_true hA, decide_eq_true hB]
  decide +kernel

theorem j4Sec : SClaim.check (ops2 112) NativeSporadic.J4Seed1 NativeSporadic.J4Seed2
    j4_7_claims = true := by
  unfold SClaim.check
  rw [mcertCheck_of_N (hom2 112 (by norm_num)) j4A j4B trivial trivial j4Sec_K]
  decide +kernel

theorem heMcert : mcertCheck (opsP 7 50) NativeSporadic.HeSeed1 NativeSporadic.HeSeed2
    CFSG.RankThree.Asc83Table.He.heCert = true := by
  have h := he_K
  rw [forceB_eq, forceB_eq] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hA, hB⟩, h⟩ := h
  refine mcertCheck_of_N (homP heConsts (by norm_num)) ?_ ?_ hA hB h
  · rw [HeS1.eq]
    exact payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)
  · rw [HeS2.eq]
    exact payRunP_eqL _ (by norm_num) (by norm_num) (by norm_num)

end CertificateChecks.KernelMC

end
