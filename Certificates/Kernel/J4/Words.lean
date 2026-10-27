module

public import CFSG.Certificates.Kernel.J4RunSound
public import CFSG.Certificates.Kernel.CosetBounds
public import Certificates.Kernel.J4.Data
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko.Four
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.LceSP.Base
public import Certificates.Data.Kernel.LceSTab
public import Mathlib

public section

namespace CertificateChecks.KernelBounds.J4

open CFSG.KJ4 CFSG.KJ4.S CFSG.Certificates CFSG.Certificates.J4R

@[expose] def rels : List (List (Nat × Bool)) :=
  [[(0, true), (0, true)], [(1, true), (1, true), (1, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)], [(0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true), (0, false), (1, false), (0, true), (1, true)], [(0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true), (0, false), (1, false), (0, false), (1, false), (0, true), (1, true), (0, true), (1, true)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false)], [(0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false)], [(2, true), (2, true)], [(2, false), (0, false), (2, true), (0, true)], [(2, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, false), (2, true), (1, true), (0, true), (1, true), (0, true), (1, false), (0, true), (1, false), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true)], [(1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (2, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (2, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, false), (1, true), (0, false), (1, false), (0, false), (1, true), (0, false), (1, false), (2, true), (1, true), (0, true), (1, false), (0, true), (1, true), (0, true), (1, false), (0, true)], [(1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (2, true), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (2, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (2, true), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (1, false), (1, false), (0, false), (1, false), (0, false), (1, false), (0, false), (2, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (0, true), (1, true), (1, true)]]

theorem rels_eq : TauCeti.Sporadic.j4Presentation.relatorLetters = rels := by
  rw [TauCeti.GroupPresentation.relatorLetters_def, TauCeti.GroupPresentation.relators_def,
    TauCeti.Sporadic.j4Presentation_transcribed]
  simp [FreeGroup.invRev, rels]

@[expose] def tcode (p : Nat × Bool) : Nat := if p.1 = 2 then 4 else 2 * p.1 + if p.2 then 0 else 1

@[expose] noncomputable def wList (w n : Nat) : List Nat := (List.range n).map (wLet w)

theorem rt_bind : (List.range 12).map (fun r => wList (wW (KRS.RT r)) (wN (KRS.RT r))) =
    rels.map (List.map tcode) := by
  decide +kernel

theorem rt_nOnly : ∀ r < 7, nOnly (wW (KRS.RT r)) (wN (KRS.RT r)) := by
  have h : ((List.range 7).map fun r => (wList (wW (KRS.RT r)) (wN (KRS.RT r))).all (· < 4)) =
      List.replicate 7 true := by decide +kernel
  intro r hr i hi
  have hr' := congrArg (fun L => L[r]?) h
  simp only [List.getElem?_map, List.getElem?_range hr, List.getElem?_replicate, hr, ite_true,
    Option.map_some, Option.some.injEq] at hr'
  have := List.all_eq_true.mp hr' (wLet (wW (KRS.RT r)) i)
    (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  simpa using this

theorem wval_eq {G : Type*} [Group G] (ℓ : ℕ → G) (w n : ℕ) :
    wval ℓ w n = ((wList w n).map fun c => if c = 255 then 1 else ℓ c).prod := by
  simp only [wval, wList, List.map_map]
  rfl

theorem prod_tcode {G : Type*} [Group G] (x y t : G) (ht : t⁻¹ = t) :
    ∀ l : List (ℕ × Bool), (∀ p ∈ l, p.1 < 3) →
      ((l.map tcode).map fun c => if c = 255 then 1 else lets x y t c).prod =
        KB.sword (fun g => if g = 0 then x else if g = 1 then y else t) l
  | [], _ => rfl
  | p :: l, h => by
    have ih := prod_tcode x y t ht l (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp only [List.map_cons, List.prod_cons, KB.sword] at ih ⊢
    rw [ih]
    congr 1
    obtain ⟨g, b⟩ := p
    have hg : g < 3 := h _ List.mem_cons_self
    rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2) with rfl | rfl | rfl <;> cases b <;>
      simp [tcode, lets, ht]

end CertificateChecks.KernelBounds.J4

end
