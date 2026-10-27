module

public import Certificates.Kernel.LocalComp.L34Two.Chk0
public import Certificates.Kernel.LocalComp.L34Two.Chk1
public import Certificates.Kernel.LocalComp.L34Two.Chk2
public import Certificates.Kernel.LocalComp.L34Two.Chk3
public import Certificates.Kernel.LocalComp.L34Two.BChk
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.Certificates.Kernel.L34TwoSigKSound
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import Certificates.Certificate2022
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelLC.L34TwoW.sigAll CertificateChecks.KernelLC.L34TwoW.sig 180

namespace CertificateChecks.KernelLC.L34Two

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KC.BfsPin CFSG.KC.L34K
open CFSG.KC.L34KSnd CFSG.KC.L34Scan CFSG.KC.L34Two CFSG.PSL3Four.Native
open CFSG.ComponentClassification.PSL3Four CertificateChecks.KernelLC.L34Cert
open CFSG.KLie.CT (andB)

theorem hgB : GensOK 42 6 2 L34TwoB.G Certificates.L34TwoSig.bGens := gensOK_of kB_gens

theorem hpB : ∀ i < 9, penumPtK 42 6 (mask 6) (42 * 6) false L34TwoB.G L34TwoB.GI 2 9 L34TwoB.T
    L34TwoB.PL L34TwoB.POS L34TwoB.SRT L34TwoB.SRI i = true := fun i hi =>
  penumSl_spec kB_sl i (Nat.zero_le _) (by omega) hi

theorem hEB : enumBFS 42 Certificates.L34TwoSig.bGens 9 = penumRec 42 6 9 L34TwoB.T L34TwoB.PL ∧
    enumOK 42 Certificates.L34TwoSig.bGens (penumRec 42 6 9 L34TwoB.T L34TwoB.PL) = true :=
  penumK_left_sound hsz42 hgB kB_hd hpB

theorem b_mem : ∃ b₁ ∈ S, ∃ b₂ ∈ S, TabRep (unpack 42 6 (L34TwoB.G 0)) b₁ ∧
    TabRep (unpack 42 6 (L34TwoB.G 1)) b₂ := by
  have hE : Enumerates S (pts 42 6 20160 L34S.T).toList := by
    have h := enumerates_S
    rwa [enumS, hS.1] at h
  obtain ⟨h1, h2⟩ := andB_iff.1 kB_S
  have e1 : (pts 42 6 20160 L34S.T)[499]! = unpack 42 6 (L34TwoB.G 0) := by
    rw [pts_get' (by decide), Nat.eq_of_beq_eq_true h1]
  have e2 : (pts 42 6 20160 L34S.T)[18821]! = unpack 42 6 (L34TwoB.G 1) := by
    rw [pts_get' (by decide), Nat.eq_of_beq_eq_true h2]
  obtain ⟨b₁, hb₁, r₁⟩ := hE.sound _ (getElem!_mem (by rw [size_pts]; decide : 499 < _))
  obtain ⟨b₂, hb₂, r₂⟩ := hE.sound _ (getElem!_mem (by rw [size_pts]; decide : 18821 < _))
  rw [e1] at r₁
  rw [e2] at r₂
  exact ⟨b₁, hb₁, b₂, hb₂, r₁, r₂⟩

theorem facts41504 : ∃ B₀ : Subgroup (Equiv.Perm (Fin 42)), B₀ ≤ S ∧ Nat.card B₀ = 9 ∧
    ∀ r ∈ R, r ^ 256 = 1 → (∀ b ∈ B₀, b * r = r * b) ∨
      ∃ w ∈ Subgroup.closure {x | ∃ c ∈ B₀, x = c * r * c⁻¹}, w ^ 256 ≠ 1 := by
  obtain ⟨b₁, hb₁S, b₂, hb₂S, r₁, r₂⟩ := b_mem
  obtain ⟨hgs, hgj⟩ := hgB
  have hgs' : Certificates.L34TwoSig.bGens.size = 2 := hgs
  have hA : ∀ a ∈ ({b₁, b₂} : Set (Equiv.Perm (Fin 42))),
      ∃ j < Certificates.L34TwoSig.bGens.size, TabRep Certificates.L34TwoSig.bGens[j]! a := by
    rintro a (rfl | rfl)
    · exact ⟨0, by rw [hgs']; decide, by rw [(hgj 0 (by decide)).1]; exact r₁⟩
    · exact ⟨1, by rw [hgs']; decide, by rw [(hgj 1 (by decide)).1]; exact r₂⟩
  have hgens : ∀ j < Certificates.L34TwoSig.bGens.size,
      ∃ a ∈ ({b₁, b₂} : Set (Equiv.Perm (Fin 42))), TabRep Certificates.L34TwoSig.bGens[j]! a := by
    intro j hj
    rw [hgs'] at hj
    rw [(hgj j hj).1]
    interval_cases j
    · exact ⟨b₁, Set.mem_insert _ _, r₁⟩
    · exact ⟨b₂, Set.mem_insert_of_mem _ rfl, r₂⟩
  have hB := enumerates_closure hA hgens hEB.2
  have htabs : (penumRec 42 6 9 L34TwoB.T L34TwoB.PL).tabs = pts 42 6 9 L34TwoB.T := rfl
  rw [htabs] at hB
  refine ⟨Subgroup.closure {b₁, b₂}, ?_, ?_, ?_⟩
  · rw [Subgroup.closure_le]
    rintro a (rfl | rfl)
    · exact hb₁S
    · exact hb₂S
  · rw [hB.card, Array.length_toList, size_pts]
  · have hR' : Enumerates R (pts 42 6 241920 L34R.T).toList := by
      have h := enumerates_R
      rwa [enumR, hR.1] at h
    have hC : ConjOK 9 L34TwoB.T L34TwoB.BTI (Subgroup.closure {b₁, b₂}) := by
      refine ⟨by decide, fun j hj => ?_⟩
      obtain ⟨c1, c2⟩ := andB_iff.1 (CFSG.KS.Raw.Orb.allN_iff.1 kB_inv j hj)
      obtain ⟨c, hc, hcr⟩ := hB.sound _ (getElem!_mem (by rw [size_pts]; exact hj))
      rw [pts_get' hj] at hcr
      exact ⟨penumPt_canon (hpB j hj), c1, Nat.eq_of_beq_eq_true c2, c, hc, hcr⟩
    have hsig := sigSl_spec (L := 1344) (K := 180) (N := 241920) (by decide) (by decide)
      L34TwoW.sigAll
    exact twoSig_of hR' pinR.canon hC (hgj 0 (by decide)).2 (hgj 1 (by decide)).2 r₁ r₂ rfl hsig

end CertificateChecks.KernelLC.L34Two

end
