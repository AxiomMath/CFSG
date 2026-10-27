module

public import Certificates.Kernel.Sporadic.Fi24Ctl3.Checks
public import Certificates.Kernel.Sporadic.Fi24Pump.Glue
public import Certificates.Kernel.Sporadic.Fi24OrbL.Facts
public import CFSG.Certificates.Kernel.Spor.Fi24Ctl3Sound
public import CFSG.LocalAnalysis.StandardType.GGSporKRestCtrl
public import CFSG.LocalAnalysis.StandardType.GGSporKRestClasses
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Classes

public section

namespace CFSG.KD.Fi24Ctl3

open CFSG.KC.Fi24Kn CFSG.KC.Fi24NetPt CFSG.KC.Fi24Base CFSG.KC.Fi24Ctl3 CFSG.KS.Fi24Ctl3
  CFSG.KS.Fi24NetPt CFSG.KS.Fi24Net CFSG.KD.Fi24Net CFSG.KD.Fi24Pump CFSG.StandardType.SporadicShape
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three


theorem wordElt_eq {u v : List ℕ} (hu : ∀ l ∈ u, l < 26) (hv : ∀ l ∈ v, l < 26)
    (h : eqB (letN NW) u v = true) : wordElt u = wordElt v := by
  have e : letN NW = LN NW := funext fun l => funext fun x => letN_eq NW l x
  rw [e] at h
  refine eq_of_foldr CertificateChecks.KernelFi24OrbL.pairG_LN hu hv fun b hb => ?_
  have := (CFSG.KS.Fi24PumpK.eqB_iff _ _).1 h b hb
  rwa [CFSG.KS.Fi24PumpK.apF_eq_foldr _ hu, CFSG.KS.Fi24PumpK.apF_eq_foldr _ hv] at this

theorem wordElt_zero : wordElt [0] = CFSG.Sporadic.Fi24.a := by
  simp [wordElt, CFSG.Perm.pairG, CFSG.Sporadic.Fi24.gs_zero]

theorem wordElt_two : wordElt [2] = CFSG.Sporadic.Fi24.b := by
  simp [wordElt, CFSG.Perm.pairG, CFSG.Sporadic.Fi24.gs_one]

theorem generating_of_ctlOK {r g x y h : List ℕ} (hc : ctlOK (eqB (letN NW)) r g x y h = true) :
    ∀ z, IsConj (wordElt r) z → SporKRestGenerating 3 z := by
  obtain ⟨hr, hg, hx, hy, hh, h3, hrg, hb, hxy, hxh, ha⟩ := ctlOK_spec hc
  have ap : ∀ {u v : List ℕ}, (∀ l ∈ u, l < 26) → (∀ l ∈ v, l < 26) → ∀ l ∈ u ++ v, l < 26 :=
    fun hu hv => List.forall_mem_append.2 ⟨hu, hv⟩
  have h0 : ∀ l ∈ [0], l < 26 := by decide
  have h2 : ∀ l ∈ [2], l < 26 := by decide
  have hn : ∀ l ∈ ([] : List ℕ), l < 26 := fun _ h => absurd h List.not_mem_nil
  have eR3 := wordElt_eq (ap (ap hr hr) hr) hn h3
  have eRG := wordElt_eq (ap hr hg) (ap hg hx) hrg
  have eXB := wordElt_eq (ap hx h2) (ap h2 hx) hb
  have eXY := wordElt_eq (ap hx hy) (ap hy hx) hxy
  have eXH := wordElt_eq (ap hx hh) (ap hh hy) hxh
  simp only [wordElt_append, wordElt_nil] at eR3 eRG eXB eXY eXH
  rw [wordElt_two] at eXB
  have hX : wordElt x = (wordElt g)⁻¹ * wordElt r * wordElt g := by
    rw [mul_assoc, eRG, ← mul_assoc, inv_mul_cancel, one_mul]
  have hX3 : wordElt x ^ 3 = 1 := by
    have e3 : wordElt x ^ 3 = (wordElt g)⁻¹ * (wordElt r * wordElt r * wordElt r) * wordElt g := by
      rw [pow_three', hX]
      group
    rw [e3, eR3]
    group
  have hya : wordElt y * CFSG.Sporadic.Fi24.a = CFSG.Sporadic.Fi24.a * wordElt y ∨
      wordElt h = CFSG.Sporadic.Fi24.a := by
    rcases ha with ha | ha
    · have e := wordElt_eq (ap hy h0) (ap h0 hy) ha
      simp only [wordElt_append, wordElt_zero] at e
      exact Or.inl e
    · have e := wordElt_eq hh h0 ha
      rw [wordElt_zero] at e
      exact Or.inr e
  have hgen : SporKRestGenerating 3 (wordElt x) :=
    sporKRest_generating_of_ctrl Nat.prime_three CFSG.Sporadic.Fi24.a CFSG.Sporadic.Fi24.b
      CFSG.Sporadic.Fi24.closure_ab hX3 eXB eXY eXH hya
  have hrx : IsConj (wordElt x) (wordElt r) := by
    refine isConj_iff.mpr ⟨wordElt g, ?_⟩
    rw [hX]
    group
  intro z hz
  exact (hgen.of_isConj hrx).of_isConj hz

theorem nthW_R : ∀ i : Fin 5, nthW J.R i = repWords i := by decide +kernel

theorem sporKRestCover_three_J :
    SporKRestCover 3 ↥CFSG.Sporadic.Fi24.J := by
  have hgen : ∀ i : Fin 5, ∀ z, IsConj (fi24Rep3 i) z → SporKRestGenerating 3 z := by
    have hc : ∀ i : Fin 5, ck i = true := by
      intro i
      fin_cases i
      · exact Ck.c0
      · exact Ck.c1
      · exact Ck.c2
      · exact Ck.c3
      · exact Ck.c4
    intro i
    have := generating_of_ctlOK (hc i)
    rwa [nthW_R] at this
  refine sporKRest_cover_of_classes Nat.prime_three (List.ofFn fun i : Fin 5 => fi24Rep3 i) ?_ ?_
  · intro s hs
    obtain ⟨i, hi⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Sylow.fi24ThreeClasses_holds
      s hs
    exact ⟨fi24Rep3 i, List.mem_ofFn.2 ⟨i, rfl⟩, hi.symm⟩
  · intro r hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hr
    exact hgen i

end CFSG.KD.Fi24Ctl3

end
