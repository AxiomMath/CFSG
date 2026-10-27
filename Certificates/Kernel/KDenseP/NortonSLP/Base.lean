module

public import Certificates.Kernel.KDenseP.TwoPoint.Base
public import Certificates.Kernel.KDenseP.AgreeOf
public import Certificates.Kernel.KDenseP.MonoTabL
public import Certificates.Kernel.NortonSLPKSound
public import CFSG.Certificates.Kernel.KDenseP.NortonSLP.Pairs
public import CFSG.Certificates.Kernel.KDense.Data.Checks
public import CFSG.Certificates.Kernel.KDenseP.ReplaySound

@[expose] public section

namespace CertificateChecks.KernelKDenseP.NortonSLP

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.KC.KDenseP.TwoPoint CFSG.KC.KDenseP.NortonSLP
  CFSG.KC.NortonSLPK CertificateChecks.KernelKDenseP.TwoPoint CFSG.Monster.AxisCount
  CFSG.AGLEmbedding.Norton CFSG.AGLEmbedding.Norton.MON5_7 CFSG.YGroups.Y443 CFSG.YGroups.Y443Native

theorem prodCheck_of {gens : Array (List Native.Gen)} {steps : Array (ProdStep × List Native.Gen)}
    {lo hi : ℕ} (hidx : idxOK gens steps lo hi = true)
    (ha : agreeAll (prodPairs gens steps lo hi) = true) : prodCheck gens steps lo hi = true := by
  have e : prodCheck gens steps lo hi = prodStepsOK gens steps lo hi := by
    unfold prodCheck prodStepsOK
    exact congrArg (List.range' lo (hi - lo)).all (funext (prodStepOKC_eq gens steps))
  rw [e]
  unfold prodStepsOK
  rw [List.all_eq_true]
  intro k hk
  have hik := List.all_eq_true.1 hidx k hk
  have hak : ∀ p, stepPair gens steps k = some p → agree p.1 p.2 = true := fun p hp =>
    List.all_eq_true.1 ha p (List.mem_filterMap.2 ⟨k, hk, hp⟩)
  unfold stepPair at hak
  unfold prodStepOK
  rcases hs : steps[k]!.1 with i | l | l
  · simp only [hs] at hik ⊢
    exact hik
  · simp only [hs] at hik hak ⊢
    rw [hik, hak _ rfl]
    rfl
  · simp only [hs] at hik hak ⊢
    rw [hik, hak _ rfl]
    rfl

theorem prodTargetsCheck_of {gens : Array (List Native.Gen)}
    {steps : Array (ProdStep × List Native.Gen)} {n : ℕ} {idx : List ℕ}
    (ht : tgtOK steps n idx = true) (ha : agreeAll (targetPairs gens steps idx) = true) :
    prodTargetsCheck gens steps n idx = true := by
  unfold tgtOK at ht
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at ht
  unfold prodTargetsCheck
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  refine ⟨ht.1, fun j hj => ⟨ht.2 j hj, ?_⟩⟩
  have hm : (prodWord gens steps idx[j]!, L j) ∈ targetPairs gens steps idx :=
    List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩
  have hj' := List.all_eq_true.1 ha _ hm
  dsimp only at hj'
  rw [agreeC_eq]
  exact hj'

theorem agreeAll_of_plan
    {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ} (hd : dataOKP F MT KT TH OCT DU1 = true)
    (eqs : List (List Native.Gen × List Native.Gen))
    {WD : ℕ → List ℕ} {N : ℕ} (hw : wordsEqB WD (Y443.words (tp3 eqs [])) N = true)
    {WL : ℕ → List Native.Gen} (hWL : ∀ σ, WL σ = decW (WD σ))
    {S : ℕ → St} (hS : ∀ x < 3, S x = CFSG.KD.KDF.I x)
    {CH IXf CHI : ℕ → ℕ} (hCHI : ∀ k, CHI k = CH (IXf k)) {nch nIX : ℕ} {IT : List ℕ}
    (hc : ∀ k < nch, chunkOKN 4 2 5 F MT WL S (CH k) = true)
    (hix : ∀ k < nIX, IXf k < nch) (hplan : planOKP WL CHI nIX IT = true) (hN : 2 * IT.length ≤ N)
    (hwk : wkOK IT (tpWK eqs.length 0) = true) : agreeAll eqs = true :=
  agreeAll_of_wordLin (tp3_valid hd eqs [] hw hWL hS hCHI hc hix hplan hN hwk)
    (tp3_sound hd eqs [] hw hWL hS hCHI hc hix hplan hN hwk).1

theorem ix_lt {IXf : ℕ → ℕ} {nu nr : ℕ} (h : ((List.range nr).all fun k => Nat.blt (IXf k) nu) = true) :
    ∀ k < nr, IXf k < nu := fun k hk => by
  have e := List.all_eq_true.1 h k (List.mem_range.2 hk)
  rwa [Nat.blt_eq] at e

theorem steps_eq_of_parse {t₀ t₁ : String} {S : Array (ProdStep × List Native.Gen)}
    (h : parseEqB (decodeK (t₀.toList ++ '\n' :: t₁.toList)) S = true) :
    decodeProdSteps (t₀ ++ "\n" ++ t₁) = S := by
  have e := decodeProdSteps_ofList (eq_of_parseEqB h)
  rwa [← ofList_nl, String.ofList_toList, String.ofList_toList] at e

theorem slp_loc {F : Fix} {MT : MonoTab} {WL : ℕ → List Native.Gen} :
    ∀ (S S' : ℕ → St) (c : ℕ), S (f20 c (nat_lit 3)) = S' (f20 c (nat_lit 3)) →
      S (f20 c (nat_lit 4)) = S' (f20 c (nat_lit 4)) →
      chunkOKN 4 2 5 F MT WL S c = chunkOKN 4 2 5 F MT WL S' c := by
  intro S S' c h3 h4
  unfold chunkOKN
  rw [h3, h4]

theorem slp_prod {F : Fix} {MT : MonoTab} {WL : ℕ → List Native.Gen} :
    ∀ (S : ℕ → St) (c : ℕ), Nat.beq (f20 c (nat_lit 5)) (nat_lit 1) = false →
      chunkOKN 4 2 5 F MT WL S c = stEqN 4 (runN 4 2 F MT (WL (f20 c (nat_lit 0)))
        (f20 c (nat_lit 1)) (f20 c (nat_lit 2)) (S (f20 c (nat_lit 3)))) (S (f20 c (nat_lit 4))) := by
  intro S c h
  unfold chunkOKN
  rw [h]

open Lean in
macro "kd_slpK% " hd:term:max pre:ident R:ident w?:(num)? eqs:term:max : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  let chk := mkIdentFrom R (R.getId ++ `chk)
  let (s0, w, lt) ← match w? with
    | some w => pure ((n "S0" : Term), w, ← `(fun x hx =>
        (rlS_lt (Nat.lt_of_lt_of_le hx (by decide))).trans (by interval_cases x <;> rfl)))
    | none => pure (← `(CFSG.KD.KDF.I), Syntax.mkNumLit "3", ← `(fun x hx => rlS_lt hx))
  `(agreeAll_of_plan $hd $eqs $(n "weq") (WL := $(n "WL")) (fun _ => rfl)
      (S := rlS $(n "rn") $(n "CH") $(n "PRf") $s0 $w)
      $lt (CH := $(n "CH")) (IXf := $(n "IXf"))
      (CHI := $(n "CHI")) (fun _ => rfl) (nch := kd_count% $pre $(mkIdent `CH))
      (nIX := kd_count% $pre $(mkIdent `IX)) (IT := $(n "IT"))
      (replay_sound (run := $(n "rn")) (chk := $chk $(n "WL"))
        (fun S S' c h3 h4 => slp_loc S S' c h3 h4) (fun S c h => slp_prod S c h)
        (CH := $(n "CH")) (PR := $(n "PRf")) (GK := $(n "GKf")) (G := $(n "Gf"))
        (S0 := $s0) (w := $w) (ng := kd_count% $pre $(mkIdent `u))
        (by kd_allE $pre $(mkIdent `u)) (by quickRfl))
      (ix_lt $(n "ix")) $(n "plan") (by decide +kernel) (by quickRfl))

end CertificateChecks.KernelKDenseP.NortonSLP

end
