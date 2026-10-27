module

public import Certificates.Kernel.HN1408.TableKChk
public import Certificates.Kernel.HN1408.TableIGlue
public import Certificates.Kernel.HN1408.Spec
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.TK

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.KS.MulH
open CFSG.KC.BfsPin CFSG.KC.Blk CFSG.KD.HN1408
open CFSG.EvenSporadicStandard.HNRecog CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

theorem sN26773 (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem powK_eq {w : List Nat} (hw : lettersOK w = true) :
    ∀ e, powK (WK w) e = WK (List.replicate e w).flatten
  | 0 => rfl
  | e + 1 => by
    have h : powK (WK w) (e + 1) = pc (powK (WK w) e) (WK w) :=
      sN26773 (powK (WK w) e) (fun Y => pc Y (WK w))
    rw [h, powK_eq hw e, List.replicate_succ', List.flatten_append, List.flatten_singleton,
      WK_append (lettersOK_rep hw e) hw]

theorem specK_eq {G : Nat → Nat} {gs : List (List Nat)} (hgs : ∀ w ∈ gs, lettersOK w = true)
    (hG : ∀ i, G i = WK (gs.getD i [])) :
    ∀ sp : List (Nat × Nat), specK G sp = WK (specWord gs sp)
  | [] => rfl
  | p :: sp => by
    have e : specWord gs (p :: sp) =
        (List.replicate p.2 (gs.getD (p.1 - 1) [])).flatten ++ specWord gs sp := by
      simp [specWord]
    have h : specK G (p :: sp) = pc (powK (G (p.1 - 1)) p.2) (specK G sp) :=
      sN26773 (specK G sp) (fun Y => pc (powK (G (Nat.sub p.1 1)) p.2) Y)
    rw [h, specK_eq hgs hG sp, hG, powK_eq (lettersOK_getD hgs _), e,
      WK_append (lettersOK_rep (lettersOK_getD hgs _) _) (lettersOK_specWord hgs sp)]

theorem getD_map_specWord (gs : List (List Nat)) (sps : List (List (Nat × Nat))) (i : Nat) :
    (sps.map (specWord gs)).getD i [] = specWord gs (sps.getD i []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases sps[i]? <;> rfl

theorem lettersOK_map {gs : List (List Nat)} (hgs : ∀ w ∈ gs, lettersOK w = true)
    (sps : List (List (Nat × Nat))) : ∀ w ∈ sps.map (specWord gs), lettersOK w = true := by
  intro w hw
  obtain ⟨sp, -, rfl⟩ := List.mem_map.1 hw
  exact lettersOK_specWord hgs sp

theorem lU : ∀ w ∈ classz.centGens, lettersOK w = true := by decide
theorem lK : ∀ w ∈ kWords, lettersOK w = true := lettersOK_map lU kSpec
theorem lN : ∀ w ∈ nWordsK, lettersOK w = true := lettersOK_map lK nSpecK
theorem lQ : ∀ w ∈ qWordsK, lettersOK w = true := lettersOK_map lN qSpecK
theorem lE : ∀ w ∈ eWordsK, lettersOK w = true := lettersOK_map lN eSpecK
theorem lZ : ∀ w ∈ zcWordsK, lettersOK w = true := by
  intro w hw
  simp only [zcWordsK, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact lettersOK_specWord lN xSpecK
  · exact lettersOK_specWord lN ySpecK

theorem uK_eq (l : Nat) : uK l = WK (classz.centGens.getD l []) := rfl

theorem kK_eq (l : Nat) : kK l = WK (kWords.getD l []) := by
  rw [kK, specK_eq lU uK_eq, kWords, getD_map_specWord]

theorem nK_eq (j : Nat) : nK j = WK (nWordsK.getD j []) := by
  rw [nK, specK_eq lK kK_eq, nWordsK, getD_map_specWord]

theorem nspec_eq (sp : List (Nat × Nat)) : specK nK sp = WK (specWord nWordsK sp) :=
  specK_eq lN nK_eq sp

theorem headI_of {ws : List (List Nat)} {GT : Nat → Nat} {k m cnt : Nat} {G GI GJ T PL : Nat → Nat}
    (hk : ws.length = k) (hGT : ∀ j < k, GT j = WK (ws.getD j []))
    (h : headR GT k m G GI GJ T PL cnt = true) : headI ws k m G GI GJ T PL cnt = true := by
  unfold headR at h
  unfold headI
  obtain ⟨h1, h2⟩ := bA h
  refine (bAnd_iff _ _).2 ⟨by rw [hk]; exact Nat.beq_refl k, (bAnd_iff _ _).2 ⟨?_, h2⟩⟩
  rw [CFSG.KD.HN1408.allN_iff'] at h1 ⊢
  intro j hj
  rw [← hGT j hj]
  exact h1 j hj

theorem recK_parts {k cnt : Nat} {G GI GJ T PL POS SRT SRI HS HSI CL : Nat → Nat}
    (h : recK k cnt G GI GJ T PL POS SRT SRI HS HSI CL = true) :
    (∀ i < cnt, penumPtK 1408 11 (mask 11) (1408 * 11) true G GI k cnt T PL POS SRT SRI i = true) ∧
    (∀ i < cnt, hsortPtK 1408 11 (mask 11) cnt T HS HSI i = true) ∧
    (∀ c < cnt * (k + k),
      findPtK cnt T (prodQK 1408 11 (mask 11) (k + k) T (bothK k GI GJ)) CL c = true) := by
  unfold recK at h
  obtain ⟨hp, h2⟩ := bA h
  obtain ⟨hs, hc⟩ := bA h2
  exact ⟨fun i hi => penumSl_spec hp i (Nat.zero_le _) (by omega) hi,
    fun i hi => slK_spec hs i (Nat.zero_le _) (by omega) hi,
    fun c hc' => slK_spec hc c (Nat.zero_le _)
      (by first | (change c < 0 + cnt * (k + k); omega) | (change c < cnt * (k + k); omega))
      (by first | (change c < 0 + cnt * (k + k); omega) | (change c < cnt * (k + k); omega))⟩

theorem hdQ : headI qWordsK 4 32 TKQ.G TKQ.GI TKQI TKQ.T TKQ.PL TKQ.cnt = true :=
  headI_of (by decide) (fun j _ => by rw [nspec_eq, qWordsK, getD_map_specWord]) ch26773_hQ

theorem hdE : headI eWordsK 3 8 TKE.G TKE.GI TKEI TKE.T TKE.PL TKE.cnt = true :=
  headI_of (by decide) (fun j _ => by rw [nspec_eq, eWordsK, getD_map_specWord]) ch26773_hE

theorem hdZ : headI zcWordsK 2 8 TKZ.G TKZ.GI TKZI TKZ.T TKZ.PL TKZ.cnt = true :=
  headI_of (by decide) (fun j hj => by
    match j, hj with
    | 0, _ => exact nspec_eq xSpecK
    | 1, _ => exact nspec_eq ySpecK) ch26773_hZ

theorem rQ : RecFacts qWordsK 32 TKQ.cnt TKQ.T TKQ.PL := by
  obtain ⟨hp, hs, hc⟩ := recK_parts ch26773_rQ
  exact rec_of lQ hdQ hp hs hc

theorem rE : RecFacts eWordsK 8 TKE.cnt TKE.T TKE.PL := by
  obtain ⟨hp, hs, hc⟩ := recK_parts ch26773_rE
  exact rec_of lE hdE hp hs hc

theorem rZ : RecFacts zcWordsK 8 TKZ.cnt TKZ.T TKZ.PL := by
  obtain ⟨hp, hs, hc⟩ := recK_parts ch26773_rZ
  exact rec_of lZ hdZ hp hs hc

end CFSG.KD.HN1408.TK

end
