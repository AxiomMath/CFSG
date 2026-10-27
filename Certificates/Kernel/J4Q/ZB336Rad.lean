module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Reps2B1
public import Certificates.Kernel.J4Q.ZFrClRad
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4Dec2B1ZB336Native
public import Certificates.Certificate4015

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Sporadic.J4.QT2

theorem zB336Word_eq : b336Word = zB336Word := rfl

theorem zMx_b336Gen (hM : MatFacts) (e : ℕ) : Mx (b336Gen e) = rowsMatrix (zB336T0 e) := by
  unfold b336Gen zB336T0
  rw [map_mul, Mx_eta hM 11 le_rfl, zB336Word_eq, Mx_el5 hM, rowsMatrix_mulRows]
  rfl

theorem xiSpan_eq_range (t : ↥J) :
    xiSpan t = Subgroup.closure (Set.range fun i : Fin 4 => zCj t i) := by
  unfold xiSpan xiGens
  congr 1
  ext x
  constructor
  · intro hx
    have hx' : x ∈ [t, fiveElt * t * fiveElt⁻¹, fiveElt ^ 2 * t * (fiveElt ^ 2)⁻¹,
        fiveElt ^ 3 * t * (fiveElt ^ 3)⁻¹] := hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
    rcases hx' with rfl | rfl | rfl | rfl
    · exact ⟨0, zCj_zero _⟩
    · exact ⟨1, zCj_one _⟩
    · exact ⟨2, zCj_two _⟩
    · exact ⟨3, zCj_three _⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨i, hi⟩ := i
    show _ ∈ [t, fiveElt * t * fiveElt⁻¹, fiveElt ^ 2 * t * (fiveElt ^ 2)⁻¹,
      fiveElt ^ 3 * t * (fiveElt ^ 3)⁻¹]
    interval_cases i
    · show zCj t 0 ∈ _
      rw [zCj_zero]
      simp
    · show zCj t 1 ∈ _
      rw [zCj_one]
      simp
    · show zCj t 2 ∈ _
      rw [zCj_two]
      simp
    · show zCj t 3 ∈ _
      rw [zCj_three]
      simp

theorem classRad_b336
    (hF : J4Basic) (e : ℕ) (gW : List ℤ) (hgW : ∀ l ∈ gW, l ≠ 0) {Ts : List (List ℕ)}
    {base : List ℕ} {C : List (List (List ℕ))} {surv sq D : List (List ℕ)} {E : List ℕ}
    (hchk : chkZFr 4 (zB336T0 e) gW Ts base C surv sq D E = true) : ClassRad (xiSpan (b336Gen e)) :=
  classRad_of_zFr4 hF Certificates.certificate4015 (b336Gen e) (zB336T0 e)
    (zMx_b336Gen hF.mat e) gW hgW (xiSpan_eq_range _) hchk

end CFSG.QuasithinUnique.A5
