module

public import Certificates.Kernel.McertP.ON
public import Certificates.Kernel.McertP.Th
public import Certificates.Kernel.MatCert.Glue
public import CFSG.Certificates.Kernel.OpsLayMcertSoundP
import all CFSG.Blueprint.NativeSporadic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMP

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.OpsLayK
open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal CFSG.Blueprint

theorem on_31_mcert : mcertCheck (opsP 3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2
    ⟨on_31_claims.nregs, on_31_claims.prog, on_31_claims.facts⟩ = true :=
  (seedsLCP_sound (C := ⟨on_31_claims.nregs, on_31_claims.prog, on_31_claims.facts⟩)
    (S := fun i => ON.P.SL.getD i []) (k := 24) (kf := 1) (rA := 0) (rB := 1)
    KernelTc.ON.lay_ok rfl rfl KernelTc.ON.decA KernelTc.ON.decB KernelTc.ON.LA_eq
    KernelTc.ON.LB_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (eq_of_eqL ON.pInit) (by decide +kernel) ON.pCh_all (by decide +kernel) ON.pFa_all
    ON.pSeeds).1

theorem on_5_mcert : mcertCheck (opsP 3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2
    ⟨on_5_claims.nregs, on_5_claims.prog, on_5_claims.facts⟩ = true :=
  (seedsLCP_sound (C := ⟨on_5_claims.nregs, on_5_claims.prog, on_5_claims.facts⟩)
    (S := fun i => ON.G.SL.getD i []) (k := 100) (kf := 1) (rA := 0) (rB := 1)
    KernelTc.ON.lay_ok rfl rfl KernelTc.ON.decA KernelTc.ON.decB KernelTc.ON.LA_eq
    KernelTc.ON.LB_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (eq_of_eqL ON.gInit) (by decide +kernel) ON.gCh_all (by decide +kernel) ON.gFa_all
    ON.gSeeds).1

theorem cert40341 :
    PClaim.check (opsP 3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2 on_31_claims = true ∧
      PClaim.check (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 th_31_claims = true ∧
      OClaim.check (ops2 248) NativeSporadic.ThSeed1 NativeSporadic.ThSeed2 th_ord4_claims =
        true := by
  refine ⟨?_, ?_, ?_⟩
  · rw [PClaim.check, on_31_mcert]
    decide +kernel
  · rw [PClaim.check, mcertCheck_of_N (hom2 248 (by norm_num)) KernelMC.thA KernelMC.thB trivial
      trivial th_31_K]
    decide +kernel
  · rw [OClaim.check, mcertCheck_of_N (hom2 248 (by norm_num)) KernelMC.thA KernelMC.thB trivial
      trivial th_ord4_K]
    decide +kernel

theorem cert40343 :
    GClaim.check (opsP 3 154) NativeSporadic.ONSeed1 NativeSporadic.ONSeed2 on_5_claims = true := by
  rw [GClaim.check, ON.g_wf, on_5_mcert]
  rfl

end CertificateChecks.KernelMP

end
