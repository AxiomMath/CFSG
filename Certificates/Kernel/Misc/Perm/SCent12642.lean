module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523.SCentInputs
public import Certificates.Kernel.Misc.Perm.J2EnumS
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Sig5
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.SCent12642

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.RankThree.Native
open CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2.Native CFSG.Monster.B.Mathieu
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523
open CertificateChecks.KernelMisc.J2C3 (cm Z)
open CertificateChecks.KernelMisc.J2Fam (R rZ)
open CertificateChecks.KernelMisc.J2En (SPL hSL memCS)

@[expose] noncomputable def scK (k : ℕ) : Bool :=
  allN 64 fun i => !(Nat.beq (cm (lget (SPL k) i) Z) (cm Z (lget (SPL k) i))) ||
    allN 64 fun j => Nat.beq (cm (lget (SPL k) i) (lget (SPL k) j))
      (cm (lget (SPL k) j) (lget (SPL k) i))

theorem kSC : allN 3 scK = true := by quickRfl

theorem rS {k : ℕ} (hk : k < 3) {x : Array ℕ} (hx : x ∈ (cS k).pts) :
    ∃ i < 64, R x (lget (SPL k) i) := by
  obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 ((memCS k hk x).1 hx)
  have hs := hSL k hk
  have hi' : i < 64 := hs.1 ▸ hi
  refine ⟨i, hi', ?_, hs.2.2 i hi'⟩
  rw [← e, ← getElem!_pos _ i hi]
  exact hs.2.1 i hi'

theorem mem_pts {k : ℕ} (hk : k < 3) {i : ℕ} (hi : i < 64) :
    (cS k).pts[i]! ∈ (cS k).pts := by
  have hsz := (enumS k hk).2
  rw [getElem!_pos _ i (by omega)]
  exact Array.getElem_mem _

theorem sCent_true : sCentOK = true := by
  unfold sCentOK
  refine List.all_eq_true.2 fun k hk => List.all_eq_true.2 fun i hi => ?_
  rw [List.mem_range] at hk hi
  obtain ⟨i', hi', rx⟩ := rS hk (mem_pts hk hi)
  have h : (!(Nat.beq (cm (lget (SPL k) i') Z) (cm Z (lget (SPL k) i'))) ||
      allN 64 fun j => Nat.beq (cm (lget (SPL k) i') (lget (SPL k) j))
        (cm (lget (SPL k) j) (lget (SPL k) i'))) = true :=
    allN_spec (allN_spec kSC k hk) i' hi'
  rw [rx.commA rZ]
  cases hc : Nat.beq (cm (lget (SPL k) i') Z) (cm Z (lget (SPL k) i'))
  · rfl
  · rw [hc, Bool.not_true, Bool.false_or] at h
    rw [Bool.not_true, Bool.false_or]
    refine List.all_eq_true.2 fun j hj => ?_
    rw [List.mem_range] at hj
    obtain ⟨j', hj', ry⟩ := rS hk (mem_pts hk hj)
    rw [rx.commA ry]
    exact allN_spec h j' hj'

end CertificateChecks.KernelMisc.SCent12642

end
