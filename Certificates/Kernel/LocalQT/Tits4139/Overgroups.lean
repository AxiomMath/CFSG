
module

public import Certificates.Kernel.LocalQT.Tits4139.Facts
public import Certificates.Kernel.LocalQT.Tits4139.OverAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLatticeCoreBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsLatticeCheckInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6TitsOverInputs
public import CFSG.Sporadic.Schreier.TitsPrim
import CFSG.Sporadic.Schreier.TitsPrimCheckInputs
meta import CFSG.Sporadic.Schreier.TitsLocal
meta import CFSG.Sporadic.Schreier.TitsData
meta import CFSG.Sporadic.Schreier.TitsArrays
meta import CFSG.Sporadic.Schreier.TitsBasic
meta import CFSG.Sporadic.Schreier.TitsCertCheck
meta import CFSG.Sporadic.Schreier.TitsLocalCheck
meta import CFSG.Sporadic.Schreier.TitsActionCheck
meta import CFSG.Sporadic.Schreier.TitsOrbit
meta import CFSG.Sporadic.Schreier.TitsStabCheck
meta import CFSG.Certificates.NativeInvariantMerge
meta import Certificates.Data.CFSGNative.Schreier.Check
meta import Certificates.Data.CFSGNative.Schreier.Merge
meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
meta import Certificates.Data.CFSGNative.MonsterB.Co2Data

public noncomputable section

namespace CertificateChecks.KernelLocalQT.Tits4139

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Tits CFSG.QuasithinUnique.Setup.X6.TitsLat

@[expose] def flagLab (x : Fin 8775) : ℕ := titsSFlagForest.1[(x : ℕ)]!

theorem titsSWords_length : titsSWords.length = 3 := rfl

@[expose] def titsSFlagGen (i : ℕ) : Equiv.Perm (Fin 8775) :=
  wordIn 13 titsTFlag (titsSWords.getD i [])

theorem titsSFlagArrs_size : titsSFlagArrs.size = 3 := by
  rw [titsSFlagArrs, List.size_toArray, List.length_map, titsSWords_length]

theorem titsSFlag_rep
    : ∀ i < titsSFlagArrs.size, Rep 8775 titsSFlagArrs[i]! (titsSFlagGen i) := by
  intro i hi
  rw [titsSFlagArrs_size] at hi
  have hi' : i < titsSWords.length := by rw [titsSWords_length]; exact hi
  have e : titsSFlagArrs[i]! = wordArr 8775 titsTFlagArrs titsSWords[i] := by
    rw [titsSFlagArrs, getElem!_pos _ i (by simpa [titsSWords_length] using hi)]
    simp
  rw [e, titsSFlagGen, getD_eq_get hi']
  exact rep_wordArr_tflag (titsLocalWords_letters titsLocalWords_mem.2.1 (List.getElem_mem _))

theorem titsSFlagGen_mem
    {i : ℕ} (hi : i < titsSFlagArrs.size) :
    titsSFlagGen i ∈ titsFlagStab.map titsDFlagAct := by
  rw [titsSFlagArrs_size] at hi
  have hi' : i < titsSWords.length := by rw [titsSWords_length]; exact hi
  have hw : titsSWords[i] ∈ titsSWords := List.getElem_mem hi'
  refine ⟨⟨wordIn 13 titsT titsSWords[i], wordIn_titsT_mem_titsD _⟩, ?_, ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def,
      titsDFlagAct_word]
    exact titsS_gen_fix hw
  · rw [titsDFlagAct_word, titsSFlagGen, getD_eq_get hi']

theorem genGroup_le_image
    : genGroup titsSFlagArrs titsSFlagGen ≤ titsFlagStab.map titsDFlagAct := by
  rw [genGroup, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  exact titsSFlagGen_mem hi

theorem exists_stab_of_mem_genGroup
    {g : Equiv.Perm (Fin 8775)}
    (hg : g ∈ genGroup titsSFlagArrs titsSFlagGen) :
    ∃ s ∈ titsFlagStab, titsDFlagAct s = g := by
  obtain ⟨s, hs, rfl⟩ := genGroup_le_image hg
  exact ⟨s, hs, rfl⟩

theorem flagLab_lt (x : Fin 8775) : flagLab x < 18 :=
  (orbitLabelOK_parts facts.1).1 x x.2

theorem exists_stab_of_lab_eq
    {x y : Fin 8775} (h : flagLab x = flagLab y) :
    ∃ s ∈ titsFlagStab, titsDFlagAct s x = y := by
  obtain ⟨g₁, hg₁, hx⟩ := mem_orbit_rep facts.1 titsSFlag_rep x
  obtain ⟨g₂, hg₂, hy⟩ := mem_orbit_rep facts.1 titsSFlag_rep y
  have hl : titsSFlagForest.1[(x : ℕ)]! = titsSFlagForest.1[(y : ℕ)]! := h
  rw [hl] at hx
  obtain ⟨s, hs, hsg⟩ := exists_stab_of_mem_genGroup (g := g₂ * g₁⁻¹) (mul_mem hg₂ (inv_mem hg₁))
  refine ⟨s, hs, ?_⟩
  rw [hsg, Equiv.Perm.mul_apply, ← hx, perm_inv_apply_self]
  exact hy

theorem lab_zero_iff (x : Fin 8775) : flagLab x = 0 ↔ x = 0 := by
  have h := allLt_spec facts.2.2.1 x.2
  rw [beq_iff_eq, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq] at h
  rw [Fin.ext_iff]
  exact h

theorem lab_one_iff (x : Fin 8775) : flagLab x = 1 ↔ x = 1 ∨ x = 3 := by
  have h := allLt_spec facts.2.2.2.1 x.2
  rw [beq_iff_eq, Bool.eq_iff_iff, beq_iff_eq, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at h
  rw [Fin.ext_iff, Fin.ext_iff (a := x) (b := 3)]
  exact h

theorem lab_two_iff (x : Fin 8775) : flagLab x = 2 ↔ x = 2 ∨ x = 5 ∨ x = 10 ∨ x = 20 := by
  have h := allLt_spec facts.2.2.2.2.1 x.2
  rw [beq_iff_eq, Bool.eq_iff_iff, beq_iff_eq, Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true,
    beq_iff_eq, beq_iff_eq, beq_iff_eq, beq_iff_eq] at h
  rw [Fin.ext_iff, Fin.ext_iff (a := x) (b := 5), Fin.ext_iff (a := x) (b := 10),
    Fin.ext_iff (a := x) (b := 20)]
  simp only [or_assoc] at h ⊢
  exact h

@[expose] def titsDWord (w : List ℤ) : titsD :=
  ⟨wordIn 13 titsT w, wordIn_titsT_mem_titsD w⟩

theorem titsDWord_zero
    {w : List ℤ} (hw : lettersOK 13 w = true) :
    ((titsDFlagAct (titsDWord w) 0 : Fin 8775) : ℕ) = (wordArr 8775 titsTFlagArrs w)[0]! := by
  rw [titsDWord, titsDFlagAct_word, (rep_wordArr_tflag hw).apply (by norm_num : 0 < 8775)]
  rfl

theorem titsDWord_sword_mem
    {i : ℕ} (hi : i < 3) : titsDWord (titsSWords.getD i []) ∈ titsFlagStab := by
  have hi' : i < titsSWords.length := by rw [titsSWords_length]; exact hi
  have h := titsS_gen_fix (List.getElem_mem hi')
  rw [← getD_eq_get (d := []) hi', ← titsDFlagAct_word] at h
  exact h

theorem titsFlagMergeReps_getD {c : ℕ} (h3 : 3 ≤ c) (hc : c < 18) :
    titsFlagMergeReps.getD (c - 3) 0 = titsSFlagReps[c]! := by
  interval_cases c <;> rfl

theorem finPt_rep_val {c : ℕ} (h3 : 3 ≤ c) (hc : c < 18) :
    ((finPt 8775 titsSFlagReps[c]! : Fin 8775) : ℕ) = titsSFlagReps[c]! := by
  apply finPt_val
  interval_cases c <;> decide

theorem rep_not_mem_F5 {c : ℕ} (h3 : 3 ≤ c) (hc : c < 18) :
    ¬ (finPt 8775 titsSFlagReps[c]! = 0 ∨ finPt 8775 titsSFlagReps[c]! = 2 ∨
      finPt 8775 titsSFlagReps[c]! = 5 ∨ finPt 8775 titsSFlagReps[c]! = 10 ∨
      finPt 8775 titsSFlagReps[c]! = 20) := by
  interval_cases c <;> decide

theorem eq_top_of_rep_mem
    {M : Subgroup titsD} (hM : titsFlagStab ≤ M) {c : ℕ} (h3 : 3 ≤ c) (hc : c < 18)
    (hr : finPt 8775 titsSFlagReps[c]! ∈ Delta titsDFlagAct 0 M) : M = ⊤ := by
  obtain ⟨hw1, hw2, hp1, hp2⟩ := facts.2.2.2.2.2 (c - 3) (by omega)
  have hg0 : titsDFlagAct (titsDWord (titsFlagRepWord (c - 3))) 0 = finPt 8775 titsSFlagReps[c]! :=
    Fin.ext (by rw [titsDWord_zero hw1, hp1, titsFlagMergeReps_getD h3 hc, finPt_rep_val h3 hc])
  have hgM : titsDWord (titsFlagRepWord (c - 3)) ∈ M := by
    rw [mem_iff_apply_mem hM, hg0]
    exact hr
  have hgH : titsDWord (titsFlagRepWord (c - 3)) ∉ titsPointStab := by
    intro h
    have h0 : ((titsDWord (titsFlagRepWord (c - 3)) : titsD) : Equiv.Perm (Fin 1755)) 0 = 0 := h
    have hb := titsBeta_dflag (titsDWord (titsFlagRepWord (c - 3))) 0
    rw [titsBeta_zero, h0, beta_eq_zero_iff, hg0] at hb
    exact rep_not_mem_F5 h3 hc hb
  have hK : wordIn 13 titsT (titsFlagZWord (c - 3)) ∈ M.map titsD.subtype := by
    refine wordIn_flatMap_mem _ _ fun d _ => ?_
    unfold titsFlagPiece
    split_ifs with hd hd'
    · exact Subgroup.mem_map.2 ⟨_, hM (titsDWord_sword_mem hd), rfl⟩
    · exact Subgroup.mem_map.2 ⟨_, hgM, rfl⟩
    · rw [wordIn_titsInvWord]
      exact inv_mem (Subgroup.mem_map.2 ⟨_, hgM, rfl⟩)
  obtain ⟨y, hyM, hy⟩ := Subgroup.mem_map.1 hK
  have hzM : titsDWord (titsFlagZWord (c - 3)) ∈ M := by
    have e : y = titsDWord (titsFlagZWord (c - 3)) := Subtype.ext hy
    rw [← e]
    exact hyM
  have hz0 := titsDWord_zero hw2
  rw [← hz0] at hp2
  have hzF : titsDFlagAct (titsDWord (titsFlagZWord (c - 3))) 0 = 2 ∨
      titsDFlagAct (titsDWord (titsFlagZWord (c - 3))) 0 = 5 ∨
      titsDFlagAct (titsDWord (titsFlagZWord (c - 3))) 0 = 10 ∨
      titsDFlagAct (titsDWord (titsFlagZWord (c - 3))) 0 = 20 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp2
    rcases hp2 with h | h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
    · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
  have hzH : titsDWord (titsFlagZWord (c - 3)) ∈ titsPointStab := by
    have hb := titsBeta_dflag (titsDWord (titsFlagZWord (c - 3))) 0
    rw [titsBeta_zero, (beta_eq_zero_iff _).2 (Or.inr hzF)] at hb
    exact hb.symm
  have hzS : titsDWord (titsFlagZWord (c - 3)) ∉ titsFlagStab := by
    intro h
    have h0 : titsDFlagAct (titsDWord (titsFlagZWord (c - 3))) 0 = 0 := h
    rw [h0] at hzF
    revert hzF
    decide
  have hH : IsCoatom titsPointStab := by
    have := CERT_Tits_derived_primitive
    have e : titsPointStab = MulAction.stabilizer titsD (0 : Fin 1755) := by
      ext g
      rfl
    rw [e]
    exact MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive titsD (0 : Fin 1755)
  refine eq_top_of_prime_index hH titsFlagStab_le_point hM ?_ hzM hzH hzS hgM hgH
  rw [index_flag_point]
  norm_num

theorem Delta_lab_lt_three
    {M : Subgroup titsD} (hM : titsFlagStab ≤ M) (hMtop : M ≠ ⊤)
    {x : Fin 8775} (hx : x ∈ Delta titsDFlagAct 0 M) : flagLab x < 3 := by
  by_contra hge
  push Not at hge
  obtain ⟨g, hg, hgx⟩ := mem_orbit_rep facts.1 titsSFlag_rep x
  obtain ⟨s, hs, hsg⟩ := exists_stab_of_mem_genGroup (inv_mem hg)
  have hr : finPt 8775 titsSFlagReps[flagLab x]! ∈ Delta titsDFlagAct 0 M := by
    have h1 := Delta_stable hM hx hs
    rw [hsg] at h1
    have e : g⁻¹ x = finPt 8775 titsSFlagReps[flagLab x]! := by
      have h := perm_inv_apply_self g (finPt 8775 titsSFlagReps[flagLab x]!)
      rw [show g (finPt 8775 titsSFlagReps[flagLab x]!) = x from hgx] at h
      exact h
    rwa [e] at h1
  exact hMtop (eq_top_of_rep_mem hM hge (flagLab_lt x) hr)

theorem overgroups
    (M : Subgroup titsD) (hM : titsFlagStab ≤ M) :
    M = titsFlagStab ∨ M = titsPointStab ∨ M = titsLineStab ∨ M = ⊤ := by
  by_cases hMtop : M = ⊤
  · exact Or.inr (Or.inr (Or.inr hMtop))
  set Δ := Delta titsDFlagAct 0 M with hΔ
  have hlab : ∀ x ∈ Δ, ∀ y, flagLab y = flagLab x → y ∈ Δ := by
    intro x hx y hxy
    obtain ⟨s, hs, hsx⟩ := exists_stab_of_lab_eq hxy.symm
    have := Delta_stable hM hx hs
    rwa [hsx] at this
  have hl1 : flagLab 1 = 1 := (lab_one_iff 1).2 (Or.inl rfl)
  have hl3 : flagLab 3 = 1 := (lab_one_iff 3).2 (Or.inr rfl)
  have hl2 : flagLab 2 = 2 := (lab_two_iff 2).2 (Or.inl rfl)
  have hmem : ∀ x : Fin 8775, x ∈ Δ ↔ x = 0 ∨ ((1 : Fin 8775) ∈ Δ ∧ (x = 1 ∨ x = 3)) ∨
      ((2 : Fin 8775) ∈ Δ ∧ (x = 2 ∨ x = 5 ∨ x = 10 ∨ x = 20)) := by
    intro x
    constructor
    · intro hx
      have h3 := Delta_lab_lt_three hM hMtop hx
      have hcases : flagLab x = 0 ∨ flagLab x = 1 ∨ flagLab x = 2 := by omega
      rcases hcases with h | h | h
      · exact Or.inl ((lab_zero_iff x).1 h)
      · exact Or.inr (Or.inl ⟨hlab x hx 1 (by rw [hl1, h]), (lab_one_iff x).1 h⟩)
      · exact Or.inr (Or.inr ⟨hlab x hx 2 (by rw [hl2, h]), (lab_two_iff x).1 h⟩)
    · rintro (rfl | ⟨h1, rfl | rfl⟩ | ⟨h2, rfl | rfl | rfl | rfl⟩)
      · exact base_mem_Delta _ _ _
      · exact h1
      · exact hlab 1 h1 3 (by rw [hl3, hl1])
      · exact h2
      · exact hlab 2 h2 5 (by rw [hl2]; exact (lab_two_iff 5).2 (by simp))
      · exact hlab 2 h2 10 (by rw [hl2]; exact (lab_two_iff 10).2 (by simp))
      · exact hlab 2 h2 20 (by rw [hl2]; exact (lab_two_iff 20).2 (by simp))
  have hmemM : ∀ g : titsD, g ∈ M ↔ titsDFlagAct g 0 ∈ Δ := fun g => mem_iff_apply_mem hM g
  by_cases h1 : (1 : Fin 8775) ∈ Δ <;> by_cases h2 : (2 : Fin 8775) ∈ Δ
  ·
    exfalso
    have hΔeq : Δ = ((({0, 1, 3, 2, 5, 10, 20} : Finset (Fin 8775))) : Set (Fin 8775)) := by
      ext x
      rw [hmem x]
      simp [h1, h2]
      tauto
    have hdvd := ncard_Delta_dvd (φ := titsDFlagAct) (b := 0) hM
    rw [← hΔ, hΔeq, Set.ncard_coe_finset, titsFlagStab_index] at hdvd
    have hc7 : ({0, 1, 3, 2, 5, 10, 20} : Finset (Fin 8775)).card = 7 := by decide
    rw [hc7] at hdvd
    omega
  ·
    right; right; left
    ext g
    have hk := titsKappa_dflag g 0
    rw [titsKappa_zero] at hk
    have hg : g ∈ titsLineStab ↔ titsDLineAct g 0 = 0 := Iff.rfl
    rw [hg, hmemM g, hmem, ← hk, kappa_eq_zero_iff]
    simp [h1, h2]
  ·
    right; left
    ext g
    have hb := titsBeta_dflag g 0
    rw [titsBeta_zero] at hb
    have hg : g ∈ titsPointStab ↔ (g : Equiv.Perm (Fin 1755)) 0 = 0 := Iff.rfl
    rw [hg, hmemM g, hmem, ← hb, beta_eq_zero_iff]
    simp [h1, h2]
  ·
    left
    ext g
    rw [hmemM g, hmem]
    simp [h1, h2]

end CertificateChecks.KernelLocalQT.Tits4139
