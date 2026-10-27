module

public import Certificates.Kernel.LyDce.BWord
public import Certificates.Kernel.LyDce.F0
public import Certificates.Kernel.LyDce.F1
public import Certificates.Kernel.LyDce.F2
public import Certificates.Kernel.LyDce.F3
public import Certificates.Kernel.LyDce.F4
public import Certificates.Kernel.LyDce.Rules
public import Certificates.Kernel.LyBase.Kind
public import Certificates.Kernel.LyReplay.Facts
public import CFSG.Certificates.Kernel.LyDce.Sound

public section

namespace CertificateChecks.KernelLyDce

open CFSG.KC.LyDce CFSG.KC.LyReplay CertificateChecks.KernelLyBase CertificateChecks.KernelLy
  CFSG.Sporadic.Recognition.LyonsSims CFSG.Sporadic.Recognition.LyonsSims.LyFinal CFSG.CosetTable

abbrev R18 : List (List (Fin 6 × Bool)) := modularR Rcore107 modularD

noncomputable abbrev gen18 (i : Fin 6) : PG 6 R18 := PresentedGroup.of i

theorem facts_all : ∀ i < 68, factAt i = true := by
  intro i hi
  interval_cases i
  exacts [f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, f15, f16, f17, f18,
    f19, f20, f21, f22, f23, f24, f25, f26, f27, f28, f29, f30, f31, f32, f33, f34, f35, f36, f37,
    f38, f39, f40, f41, f42, f43, f44, f45, f46, f47, f48, f49, f50, f51, f52, f53, f54, f55, f56,
    f57, f58, f59, f60, f61, f62, f63, f64, f65, f66, f67]

theorem nt_length : nt.length = 68 := by decide +kernel

theorem lift_rel_eq_one {w : List (Fin 6 × Bool)} (hw : w ∈ R18) :
    FreeGroup.lift gen18 (FreeGroup.mk w) = 1 := by
  rw [lift_of_eq_mk]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hw)

theorem sq_mem : ∀ i : Fin 6, i.val ≠ 1 → [(i, true), (i, true)] ∈ Rcore107 := by
  decide +kernel

theorem eRel_mem : ∀ e ∈ dist2EEvs, eRelOf e ∈ Rcore107 := by decide +kernel

theorem trRel_mem : trRel dist2TrEv ∈ Rcore107 := by decide +kernel

theorem core_mem {w : List (Fin 6 × Bool)} (hw : w ∈ Rcore107) : w ∈ R18 :=
  List.mem_append_left _ (List.mem_append_left _ hw)

theorem gen18_inv : ∀ i : Fin 6, i.val ≠ 1 → gen18 i * gen18 i = 1 := by
  intro i hi
  have h := lift_rel_eq_one (core_mem (sq_mem i hi))
  simpa [lift_mk_cons, lift_mk_nil] using h

section Holds

variable (hc : ∀ a : Fin Ly0.deg, cL a = (Ly0.cG a : Nat))
  (hd : ∀ a : Fin Ly0.deg, dL a = (Ly0.dG a : Nat)) (hbc : RB5Bound)
include hc hd hbc

theorem step_sound (k : Nat) (old new : List (Fin 6 × Bool))
    (h : stepOKD wB (rulesOf KernelLyReplay.kR) (rulesOf KernelLyReplay.eR)
      (rulesOf KernelLyReplay.tR) (rulesOf dR) k old new = true) :
    FreeGroup.lift gen18 (FreeGroup.mk old) = FreeGroup.lift gen18 (FreeGroup.mk new) := by
  have hk : gen18 5 * gen18 5 = 1 := gen18_inv 5 (by decide)
  refine stepOKD_sound (fun w hw => lift_of_eq_one_of_wB hc hd hbc
      (fun r hr => core_mem (rb_mem_core r hr)) hw) gen18_inv ?_ ?_ ?_ ?_ h
  · rw [KernelLyReplay.kR_eq]
    exact dist2KRules_sound hk
  · rw [KernelLyReplay.eR_eq]
    exact dist2ERules_sound gen18_inv hk fun e he => lift_rel_eq_one (core_mem (eRel_mem e he))
  · rw [KernelLyReplay.tR_eq]
    exact dist2TRules_sound gen18_inv hk (lift_rel_eq_one (core_mem trRel_mem))
  · exact dRulesOK_sound gen18_inv dR_ok fun r hr =>
      lift_rel_eq_one (List.mem_append_right _ hr)

theorem fact_holds {i : Nat} (hi : i < 68) :
    (nt.getD i (0, 0)).1 < 5 ∧ (nt.getD i (0, 0)).2 < 5 ∧
      isBWord (wordOf (rep.getD i [])) = true ∧ isBWord (wordOf (vw.getD i [])) = true ∧
      isBWord (wordOf (aw.getD i [])) = true ∧
      FreeGroup.lift gen18 (FreeGroup.mk (wordOf (rootC (nt.getD i (0, 0)).1))) *
          FreeGroup.lift gen18 (FreeGroup.mk (wordOf (rep.getD i []))) * gen18 5 =
        FreeGroup.lift gen18 (FreeGroup.mk (wordOf (aw.getD i []))) *
          FreeGroup.lift gen18 (FreeGroup.mk (wordOf (rootC (nt.getD i (0, 0)).2))) *
          FreeGroup.lift gen18 (FreeGroup.mk (wordOf (vw.getD i []))) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    factOKD_sound (step_sound hc hd hbc) (facts_all i hi)
  exact ⟨h1, h2, h3, h4, h5, lift_startW gen18_inv _ _ _ _ _ h6⟩

end Holds

end CertificateChecks.KernelLyDce

end
