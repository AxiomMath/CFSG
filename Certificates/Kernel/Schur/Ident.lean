module

public import Certificates.Kernel.Schur.Models
public import CFSG.Certificates.Kernel.Schur.ModelM24
public import CFSG.Certificates.Kernel.Bounds.M24Alt.Binding
import Certificates.Kernel.McL.Words
import Certificates.Kernel.M24.Bridge
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation

public section

namespace CertificateChecks.KernelSchur

open CFSG.Certificates CFSG.Certificates.KB CFSG.KC TauCeti

theorem m24_bind : ∀ r < CFSG.KBAlt.M24.rels.length,
    Schur.M24.REL r = ent (CFSG.KBAlt.M24.rels.getD r []) := by
  decide +kernel

theorem m24_small : ∀ w ∈ CFSG.KBAlt.M24.rels, w.length < 1024 ∧ ∀ x ∈ w, x.1 < 127 := by
  decide +kernel

@[expose] def orbN24 (l : ℕ) : ℕ := [24, 23, 22, 21, 20, 16, 3].getD l 0
@[expose] def orbM24 (l : ℕ) : ℕ := [23, 22, 21, 20, 19, 15, 2].getD l 0
@[expose] def orbJ24 (l : ℕ) : ℕ :=
  [Schur.M24.OJ0, Schur.M24.OJ1, Schur.M24.OJ2, Schur.M24.OJ3, Schur.M24.OJ4, Schur.M24.OJ5,
    Schur.M24.OJ6].getD l 0

theorem m24_orb : ∀ l < 7, McL.Model.orbCount (McL.Model.orbitRun Schur.M24.EP Schur.M24.ED
    Schur.M24.BP l (orbM24 l) (orbJ24 l)) = orbN24 l ∧ McL.Model.bpt Schur.M24.BP l < 24 := by
  intro l hl
  interval_cases l
  · exact ⟨Nat.eq_of_beq_eq_true Schur.M24.orb0, Nat.blt_eq.mp Schur.M24.bp0⟩
  · exact ⟨Nat.eq_of_beq_eq_true Schur.M24.orb1, Nat.blt_eq.mp Schur.M24.bp1⟩
  · exact ⟨Nat.eq_of_beq_eq_true Schur.M24.orb2, Nat.blt_eq.mp Schur.M24.bp2⟩
  · exact ⟨Nat.eq_of_beq_eq_true Schur.M24.orb3, Nat.blt_eq.mp Schur.M24.bp3⟩
  · exact ⟨Nat.eq_of_beq_eq_true Schur.M24.orb4, Nat.blt_eq.mp Schur.M24.bp4⟩
  · exact ⟨Nat.eq_of_beq_eq_true Schur.M24.orb5, Nat.blt_eq.mp Schur.M24.bp5⟩
  · exact ⟨Nat.eq_of_beq_eq_true Schur.M24.orb6, Nat.blt_eq.mp Schur.M24.bp6⟩

theorem m24_reads {G : Type*} [Group G] (y : ℕ → G) (hy : ∀ w ∈ CFSG.KBAlt.M24.rels, sword y w = 1)
    (w : List (ℕ × Bool)) (hw : ∀ x ∈ w, x.1 < 2) {n : ℕ} (hwn : w.length = n)
    (h : Nat.beq (McL.evalW Schur.M24.MG 24 (Schur.Pack.pk w) n) (McL.pid 24) = true) :
    sword y w = 1 := by
  have hfin : Finite Sporadic.m24Presentation.Group := KernelBounds.m24.1
  exact model_reads Sporadic.m24Presentation KernelBounds.m24_gens CFSG.KBAlt.M24.rels_eq
    m24_bind m24_small Schur.M24.gens Schur.M24.rels Schur.M24.rels_letters Schur.M24.ents
    (CertificateChecks.KernelMcL.epWrap_sound Schur.M24.ep_wrap) m24_orb
    (N0 := 244823040) (by simp [Finset.prod_range_succ, orbN24]) KernelBounds.m24.2 y hy w hw hwn h

end CertificateChecks.KernelSchur

end
