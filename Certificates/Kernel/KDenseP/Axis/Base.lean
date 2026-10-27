module

public import CFSG.Certificates.Kernel.KDenseP.Seven
public import CFSG.Certificates.Kernel.KDense.Tactic
public import CFSG.Certificates.Kernel.KDense.Y443.Pairs
public import Certificates.Data.Kernel.KDenseP.Words
public import CFSG.Monster.AxisCount.BabyInv
public import CFSG.Certificates.Kernel.KDenseP.ReplaySound
public meta import Lean
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Monster.AxisCount.BabyCoverSpec
public import CFSG.YGroups.Y443.Native.EdgeNoncommBase

@[expose] public section

namespace CertificateChecks.KernelKDenseP.Axis

open CFSG.KC CFSG.KC.KDense CFSG.KC.KDenseP CFSG.Monster CFSG.Monster.AxisCount
  CFSG.Monster.B.Short CFSG.Monster.Griess

open Lean Elab Term in
elab "kd_count% " pre:ident base:ident : term => do
  let env ← getEnv
  let mut n := 0
  while env.contains (pre.getId ++ Name.mkSimple s!"{base.getId}{n}") do
    n := n + 1
  return mkNatLit n

open Lean Meta Elab Tactic in
elab "kd_allE " pre:ident base:ident : tactic => liftMetaFinishingTactic fun g => do
  let ty ← instantiateMVars (← g.getType)
  let .forallE kn kt (.forallE _ bnd body _) _ := ty
    | throwError "kd_allE: the goal is not of the form ∀ k < n, P k"
  let some n ← (evalNat bnd.appArg!).run
    | throwError "kd_allE: the bound is not a numeral"
  let P := Expr.lam kn kt (body.lowerLooseBVars 1 1) .default
  let mut prf := mkApp (mkConst ``allLt_zero) P
  for k in [0:n] do
    let tk := mkConst (pre.getId ++ Name.mkSimple s!"{base.getId}{k}")
    prf := mkAppN (mkConst ``allLt_succ) #[P, mkRawNatLit k, prf, tk]
  g.assign prf

@[expose] noncomputable def monoFold (F : Fix) (MT : MonoTab) (L : List (List ℕ)) (k : ℕ) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun l _ ih k => andB (monoEntOK F l (MT.ents k)) (ih (Nat.add k 1))) L k

theorem monoFold_nil (F : Fix) (MT : MonoTab) (k : ℕ) : monoFold F MT [] k = true := rfl

theorem monoFold_cons (F : Fix) (MT : MonoTab) (l : List ℕ) (L : List (List ℕ)) (k : ℕ)
    (h1 : monoEntOK F l (MT.ents k) = true) (h2 : monoFold F MT L (k + 1) = true) :
    monoFold F MT (l :: L) k = true :=
  andB_true h1 h2

theorem monoTabOK_of_fold (F : Fix) (MT : MonoTab) (h : monoFold F MT MT.keys 0 = true) :
    monoTabOK F MT = true := h

open Lean Meta Elab Tactic in
elab "kd_monoTab " pre:ident base:ident : tactic => liftMetaFinishingTactic fun g => do
  let ty ← instantiateMVars (← g.getType)
  let some (_, lhs, _) := ty.eq? | throwError "kd_monoTab: the goal is not an equation"
  let_expr monoTabOK F MT := lhs | throwError "kd_monoTab: the goal is not monoTabOK F MT = true"
  let some v := (← getConstInfo MT.constName!).value?
    | throwError "kd_monoTab: {MT} has no value"
  let mut L := v.appFn!.appArg!
  let mut elems : Array Expr := #[]
  let mut fuel := 1000000
  while fuel > 0 do
    fuel := fuel - 1
    L := L.headBeta
    if let .letE _ _ val body _ := L then
      L := body.instantiate1 val
    else if let .mdata _ e := L then
      L := e
    else if L.isAppOfArity ``List.cons 3 then
      elems := elems.push L.appFn!.appArg!
      L := L.appArg!
    else
      break
  unless L.isAppOfArity ``List.nil 1 do throwError "kd_monoTab: the keys are not a literal list"
  let n := elems.size
  let cons := mkApp (mkConst ``List.cons [Level.zero]) L.appArg!
  let mut tails : Array Expr := Array.replicate (n + 1) L
  for i in [0:n] do
    let k := n - 1 - i
    tails := tails.set! k (mkApp2 cons elems[k]! tails[k + 1]!)
  let mut prf := mkApp3 (mkConst ``monoFold_nil) F MT (mkRawNatLit n)
  for i in [0:n] do
    let k := n - 1 - i
    let tk := mkConst (pre.getId ++ Name.mkSimple s!"{base.getId}{k}")
    prf := mkAppN (mkConst ``monoFold_cons) #[F, MT, elems[k]!, tails[k + 1]!, mkRawNatLit k, tk, prf]
  g.assign (mkApp3 (mkConst ``monoTabOK_of_fold) F MT prf)

theorem wordEqB_eq : ∀ {u v : List Native.Gen}, wordEqB u v = true → u = v
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | g :: u, g' :: v, H => by
    change andB (genEq g g') (wordEqB u v) = true at H
    rw [andB_eq, Bool.and_eq_true] at H
    rw [genEq_eq H.1, wordEqB_eq H.2]

theorem wordsEqB_spec {W : ℕ → List ℕ} {words : ℕ → List Native.Gen} {N : ℕ}
    (h : wordsEqB W words N = true) : ∀ σ < N, decW (W σ) = words σ := by
  induction N with
  | zero => exact fun σ hσ => absurd hσ (Nat.not_lt_zero _)
  | succ N ih =>
    change andB (wordEqB (decW (W N)) (words N)) (wordsEqB W words N) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    intro σ hσ
    rcases Nat.lt_succ_iff_lt_or_eq.1 hσ with hσ | rfl
    · exact ih h.2 σ hσ
    · exact wordEqB_eq h.1

theorem decG_letterOK (c : ℕ) : letterOK (decG c) = true := by
  unfold decG
  beta_reduce
  generalize Nat.land c 7 = k
  generalize Nat.shiftRight c 3 = v
  cases Nat.blt k 2 <;> cases Nat.beq k 0 <;> cases Nat.beq k 2 <;> cases Nat.beq k 3
  all_goals first
    | rfl
    | exact letterOK_rho _ _ (Nat.and_lt_two_pow _ (by norm_num : 4095 < 2 ^ 12))

theorem decW_letterOK (l : List ℕ) : ∀ g ∈ decW l, letterOK g = true := by
  induction l with
  | nil => exact fun g hg => absurd hg List.not_mem_nil
  | cons c l ih =>
    intro g hg
    change g ∈ decG c :: decW l at hg
    rcases List.mem_cons.1 hg with rfl | hg
    · exact decG_letterOK c
    · exact ih g hg

theorem words_eq (l : List (List Native.Gen × List Native.Gen)) (s : ℕ) :
    Y443.words l s = Bool.rec (motive := fun _ => List Native.Gen)
      (l.getD (Nat.shiftRight s 1) ([], [])).1 (l.getD (Nat.shiftRight s 1) ([], [])).2
      (Nat.beq (Nat.land s 1) 1) := by
  unfold Y443.words
  generalize Nat.shiftRight s 1 = k
  induction l generalizing k with
  | nil => cases Nat.beq (Nat.land s 1) 1 <;> rfl
  | cons p l ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k

theorem words_even (l : List (List Native.Gen × List Native.Gen)) (t : ℕ) :
    Y443.words l (2 * t) = (l.getD t ([], [])).1 := by
  rw [words_eq]
  have h1 : Nat.shiftRight (2 * t) 1 = t := by
    change (2 * t) >>> 1 = t
    rw [Nat.shiftRight_one]
    omega
  have h2 : Nat.land (2 * t) 1 = 0 := by
    change (2 * t) &&& 1 = 0
    rw [Nat.and_one_is_mod]
    omega
  rw [h1, h2]
  rfl

theorem words_odd (l : List (List Native.Gen × List Native.Gen)) (t : ℕ) :
    Y443.words l (2 * t + 1) = (l.getD t ([], [])).2 := by
  rw [words_eq]
  have h1 : Nat.shiftRight (2 * t + 1) 1 = t := by
    change (2 * t + 1) >>> 1 = t
    rw [Nat.shiftRight_one]
    omega
  have h2 : Nat.land (2 * t + 1) 1 = 1 := by
    change (2 * t + 1) &&& 1 = 1
    rw [Nat.and_one_is_mod]
    omega
  rw [h1, h2]
  rfl

@[expose] def witsOK : List ℕ → List ℕ → Bool
  | [], [] => true
  | it :: IT, w :: ws => (Nat.beq (it % 4) w && Nat.beq (it / 4 % 2) 0) && witsOK IT ws
  | _, _ => false

theorem witsOK_spec : ∀ {IT ws : List ℕ}, witsOK IT ws = true →
    IT.length = ws.length ∧ ∀ t < IT.length, IT[t]! % 4 = ws.getD t 0 ∧ IT[t]! / 4 % 2 = 0
  | [], [], _ => ⟨rfl, fun t ht => absurd ht (Nat.not_lt_zero _)⟩
  | [], _ :: _, h => absurd h Bool.false_ne_true
  | _ :: _, [], h => absurd h Bool.false_ne_true
  | it :: IT, w :: ws, h => by
    simp only [witsOK, Bool.and_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    obtain ⟨l, hl⟩ := witsOK_spec h3
    refine ⟨by simp [l], fun t ht => ?_⟩
    rcases t with _ | t
    · simp [h1, h2]
    · have := hl t (by simpa using ht)
      simpa using this

@[expose] def wit (x : ℕ) : Native.DVec := if x = 1 then HS.axisM else HS.axisP

@[expose] noncomputable def wv (x : ℕ) : SpaceB := if x = 1 then aStarMinus else aStar

theorem wv_zero : wv 0 = aStar := rfl

theorem wv_one : wv 1 = aStarMinus := rfl

theorem wit_cases (x : ℕ) : wit x = HS.axisP ∨ wit x = HS.axisM := by
  unfold wit
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem interp_wit (x : ℕ) : interp (wit x) = wv x := by
  unfold wit wv
  split_ifs
  · exact HS.interp_axisM
  · exact HS.interp_axisP

theorem axisP_eq : HS.axisP = Native.DVec.ofList [(0, 1), (1, 1), (24, -1), (300, -2)] := rfl

theorem axisM_eq : HS.axisM = Native.DVec.ofList [(0, 1), (1, 1), (24, -1), (300, 2)] := rfl

theorem rep_wit {n : ℕ} (hn : 2 ≤ n) {S : ℕ → St}
    (h0 : listInitOK n [(0, 1), (1, 1), (24, -1), (300, -2)] (S 0) = true)
    (h1 : listInitOK n [(0, 1), (1, 1), (24, -1), (300, 2)] (S 1) = true) (h2 : S 2 = S 0) :
    ∀ x < 3, RepN n (wit x) (S x) := by
  intro x hx
  have e0 : wit 0 = HS.axisP := rfl
  have e1 : wit 1 = HS.axisM := rfl
  have e2 : wit 2 = HS.axisP := rfl
  interval_cases x
  · rw [e0, axisP_eq]
    exact listInit_sound hn _ _ h0
  · rw [e1, axisM_eq]
    exact listInit_sound hn _ _ h1
  · rw [e2, axisP_eq, h2]
    exact listInit_sound hn _ _ h0

@[expose] noncomputable def endSt (S : ℕ → St) (CHI : ℕ → ℕ) (IT : List ℕ) (t : ℕ) : St :=
  S (f20 (CHI fld(IT[t]!, 84, 1048575)) 3)

theorem item_facts {n lg q : ℕ} (hn : 2 ≤ n) (hlg : n ≤ 2 ^ lg) (hq : q ∣ 2 ^ n - 1)
    {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ} (hd : dataOKP F MT KT TH OCT DU1 = true)
    {T : List ((List Native.Gen × List Native.Gen) × ℕ)}
    {p : List (List Native.Gen × List Native.Gen)} (hp : p = T.map Prod.fst)
    {WD : ℕ → List ℕ} {N : ℕ} (hw : wordsEqB WD (Y443.words p) N = true)
    {WL : ℕ → List Native.Gen} (hWL : ∀ σ, WL σ = decW (WD σ))
    {S : ℕ → St} {CH IXf CHI : ℕ → ℕ} (hCHI : ∀ k, CHI k = CH (IXf k)) {nch nIX : ℕ}
    {IT : List ℕ} (hc : ∀ k < nch, chunkOKN n lg q F MT WL S (CH k) = true)
    (hix : ∀ k < nIX, IXf k < nch) (hplan : planOKP WL CHI nIX IT = true)
    (h0 : listInitOK n [(0, 1), (1, 1), (24, -1), (300, -2)] (S 0) = true)
    (h1 : listInitOK n [(0, 1), (1, 1), (24, -1), (300, 2)] (S 1) = true) (h2 : S 2 = S 0)
    (hws : witsOK IT (T.map Prod.snd) = true) (hN : 2 * IT.length ≤ N)
    (t : ℕ) (ht : t < T.length) :
    (∀ g ∈ T[t].1.1, g.validB = true) ∧ (∀ g ∈ T[t].1.2, g.validB = true) ∧
      RepN n (Native.evalWord T[t].1.1 (wit T[t].2)) (endSt S CHI IT t) ∧
      ∀ k < 196884, resN n (Native.evalWord T[t].1.1 (wit T[t].2)) k =
        resN n (Native.evalWord T[t].1.2 (wit T[t].2)) k := by
  obtain ⟨hl, hit⟩ := witsOK_spec hws
  rw [List.length_map] at hl
  have htI : t < IT.length := by omega
  obtain ⟨hx, hk⟩ := hit t htI
  have hx' : IT[t]! % 4 = T[t].2 := by
    rw [hx]
    simp [List.getD_eq_getElem?_getD, ht]
  have hch : ∀ k < nIX, chunkOKN n lg q F MT WL S (CHI k) = true := fun k hk' => by
    rw [hCHI]
    exact hc _ (hix k hk')
  have hinit := rep_wit hn h0 h1 h2
  have hL : ∀ σ, ∀ g ∈ WL σ, letterOK g = true := fun σ g hg => by
    rw [hWL] at hg
    exact decW_letterOK _ g hg
  obtain ⟨vA, vB, rA, -, -, -, -⟩ :=
    itemP_sound hn hlg hd WL hL S wit hinit CHI nIX IT hplan hch t htI
  obtain ⟨-, -, he, -⟩ := planP_sound hn hlg hq hd WL hL S wit hinit CHI nIX IT hplan hch t htI
  have hW : ∀ σ < N, WL σ = Y443.words p σ := fun σ hσ =>
    (hWL σ).trans (wordsEqB_spec hw σ hσ)
  have hg : p.getD t ([], []) = T[t].1 := by
    rw [hp]
    simp [List.getD_eq_getElem?_getD, ht]
  have e1 : WL (2 * t) = T[t].1.1 := by
    rw [hW _ (by omega), words_even, hg]
  have e2 : WL (2 * t + 1) = T[t].1.2 := by
    rw [hW _ (by omega), words_odd, hg]
  rw [e1] at vA
  rw [e1, hx'] at rA
  rw [e2] at vB
  rw [e1, e2, hx'] at he
  exact ⟨vA, vB, rA, he hk⟩

theorem eq_items
    {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ} (hd : dataOKP F MT KT TH OCT DU1 = true)
    {T : List ((List Native.Gen × List Native.Gen) × ℕ)}
    {p : List (List Native.Gen × List Native.Gen)} (hp : p = T.map Prod.fst)
    {WD : ℕ → List ℕ} {N : ℕ} (hw : wordsEqB WD (Y443.words p) N = true)
    {WL : ℕ → List Native.Gen} (hWL : ∀ σ, WL σ = decW (WD σ))
    {S : ℕ → St} {CH IXf CHI : ℕ → ℕ} (hCHI : ∀ k, CHI k = CH (IXf k)) {nch nIX : ℕ}
    {IT : List ℕ} (hc : ∀ k < nch, chunkOKN 3 2 7 F MT WL S (CH k) = true)
    (hix : ∀ k < nIX, IXf k < nch) (hplan : planOKP WL CHI nIX IT = true)
    (h0 : listInitOK 3 [(0, 1), (1, 1), (24, -1), (300, -2)] (S 0) = true)
    (h1 : listInitOK 3 [(0, 1), (1, 1), (24, -1), (300, 2)] (S 1) = true) (h2 : S 2 = S 0)
    (hws : witsOK IT (T.map Prod.snd) = true) (hN : 2 * IT.length ≤ N) :
    ∀ x ∈ T, wordLin x.1.1 (wv x.2) = wordLin x.1.2 (wv x.2) := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨vA, vB, -, hr⟩ := item_facts (by norm_num) (by norm_num) (by norm_num) hd hp hw hWL
    hCHI hc hix hplan h0 h1 h2 hws hN t ht
  have h := wordLin_interp_eq_of_cong7D vA vB (wit_cases _) (wit_cases _) (cong7D_of_resN hr)
  rwa [interp_wit] at h

theorem chunkOKN_loc {n lg q : ℕ} {F : Fix} {MT : MonoTab} {WL : ℕ → List Native.Gen} :
    ∀ (S S' : ℕ → St) (c : ℕ), S (f20 c (nat_lit 3)) = S' (f20 c (nat_lit 3)) →
      S (f20 c (nat_lit 4)) = S' (f20 c (nat_lit 4)) →
      chunkOKN n lg q F MT WL S c = chunkOKN n lg q F MT WL S' c := by
  intro S S' c h3 h4
  unfold chunkOKN
  rw [h3, h4]

theorem chunkOKN_prod {n lg q : ℕ} {F : Fix} {MT : MonoTab} {WL : ℕ → List Native.Gen} :
    ∀ (S : ℕ → St) (c : ℕ), Nat.beq (f20 c (nat_lit 5)) (nat_lit 1) = false →
      chunkOKN n lg q F MT WL S c = stEqN n (runN n lg F MT (WL (f20 c (nat_lit 0)))
        (f20 c (nat_lit 1)) (f20 c (nat_lit 2)) (S (f20 c (nat_lit 3))))
        (S (f20 c (nat_lit 4))) := by
  intro S c h
  unfold chunkOKN
  rw [h]

theorem rlS_init {n : ℕ} {L : List (ℕ × ℤ)} {run : ℕ → St → St} {CH PR : ℕ → ℕ} {S0 : ℕ → St}
    {x : ℕ} (hx : x < 3) (h : listInitOK n L (S0 x) = true) :
    listInitOK n L (rlS run CH PR S0 3 x) = true := by
  rw [rlS_lt hx]
  exact h

theorem rlS_wit2 {run : ℕ → St → St} {CH PR : ℕ → ℕ} {S0 : ℕ → St} (h : S0 2 = S0 0) :
    rlS run CH PR S0 3 2 = rlS run CH PR S0 3 0 := by
  rw [rlS_lt (by norm_num), rlS_lt (by norm_num)]
  exact h

open Lean in
macro "kd_axC% " pre:ident : term => do
  let n := fun (s : String) => mkIdentFrom pre (pre.getId ++ Name.mkSimple s)
  `(replay_sound (run := $(n "rn")) (chk := $(n "ck"))
      (fun S S' c h3 h4 => chunkOKN_loc S S' c h3 h4) (fun S c h => chunkOKN_prod S c h)
      (CH := $(n "CH")) (PR := $(n "PRf")) (GK := $(n "GKf")) (G := $(n "Gf"))
      (S0 := $(n "S0")) (w := 3) (ng := kd_count% $pre $(mkIdent `u))
      (nch := kd_count% $pre $(mkIdent `CH)) (by kd_allE $pre $(mkIdent `u)) (by quickRfl))

@[expose] def DyRes (n : ℕ) (x : ℚ) (r : ZMod (2 ^ n - 1)) : Prop :=
  ∃ (a : ℤ) (e : ℕ), x = a / 2 ^ e ∧ (a : ZMod (2 ^ n - 1)) * (2 ^ (n - 1)) ^ e = r

theorem dyRes_unique {n : ℕ} (hn : 1 ≤ n) {x : ℚ} {r r' : ZMod (2 ^ n - 1)} (h : DyRes n x r)
    (h' : DyRes n x r') : r = r' := by
  obtain ⟨a, e, rfl, rfl⟩ := h
  obtain ⟨b, f, hab, rfl⟩ := h'
  rw [div_eq_div_iff (by positivity) (by positivity)] at hab
  have hz : (a * 2 ^ f : ℤ) = b * 2 ^ e := by exact_mod_cast hab
  have hc := congrArg (fun z : ℤ => (z : ZMod (2 ^ n - 1))) hz
  push_cast at hc
  have u := two_mul_two_pow_pred hn
  calc (a : ZMod (2 ^ n - 1)) * (2 ^ (n - 1)) ^ e
      = a * (2 ^ (n - 1)) ^ e * (2 * 2 ^ (n - 1)) ^ f := by rw [u, one_pow, mul_one]
    _ = (a * 2 ^ f) * (2 ^ (n - 1)) ^ e * (2 ^ (n - 1)) ^ f := by ring
    _ = (b * 2 ^ e) * (2 ^ (n - 1)) ^ e * (2 ^ (n - 1)) ^ f := by rw [hc]
    _ = b * (2 ^ (n - 1)) ^ f * (2 * 2 ^ (n - 1)) ^ e := by ring
    _ = b * (2 ^ (n - 1)) ^ f := by rw [u, one_pow, mul_one]

@[expose] noncomputable def trOf (n : ℕ) (s : St) : ℕ := trRes n s.2.2.1

@[expose] noncomputable def xOf (n : ℕ) (s : St) : ℕ := resAt SX n s.2.1 114689

theorem trOf_lt (n : ℕ) (s : St) (hn : 1 ≤ n) : trOf n s < 2 ^ n - 1 := by
  unfold trOf
  rw [trRes_eq]
  exact Nat.mod_lt _ (pos_of_dvd_two_pow_sub_one hn dvd_rfl)

theorem xOf_lt (n : ℕ) (s : St) (hn : 1 ≤ n) : xOf n s < 2 ^ n - 1 := by
  unfold xOf
  rw [resAt_eq]
  exact Nat.mod_lt _ (pos_of_dvd_two_pow_sub_one hn dvd_rfl)

theorem val_dyRes {n : ℕ} {v : Native.DVec} {s : St} {tr xr : ℕ}
    (hs : RepN n v s) (h : valOK n s tr xr = true) :
    DyRes n (trA2 (interp v)) tr ∧ DyRes n (Baby.xStarCoord (interp v)) xr := by
  obtain ⟨h1, h2⟩ := valOK_sound hs h
  refine ⟨⟨HS.trA2N v, 2 * v.e, ?_, ?_⟩, ⟨v.D.getD 300 0, v.e, Baby.xStarCoord_interp v, ?_⟩⟩
  · rw [HS.trA2_interp, pow_mul]
    norm_num
  · have e : HS.trA2N v = ∑ i ∈ Finset.range 24, ∑ j ∈ Finset.range 24,
        (v.D.getD (Native.aIdx i j) 0) ^ 2 := by
      unfold HS.trA2N
      simp only [HS.sum_range_map]
    rw [h1, e]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold resN
    ring
  · rw [h2]
    rfl

theorem val_items
    {F : Fix} {MT : MonoTab} {KT TH OCT DU1 : ℕ} (hd : dataOKP F MT KT TH OCT DU1 = true)
    {T : List ((List Native.Gen × List Native.Gen) × ℕ)}
    {p : List (List Native.Gen × List Native.Gen)} (hp : p = T.map Prod.fst)
    {WD : ℕ → List ℕ} {N : ℕ} (hw : wordsEqB WD (Y443.words p) N = true)
    {WL : ℕ → List Native.Gen} (hWL : ∀ σ, WL σ = decW (WD σ))
    {S : ℕ → St} {CH IXf CHI : ℕ → ℕ} (hCHI : ∀ k, CHI k = CH (IXf k)) {nch nIX : ℕ}
    {IT : List ℕ} (hc : ∀ k < nch, chunkOKN 7 3 127 F MT WL S (CH k) = true)
    (hix : ∀ k < nIX, IXf k < nch) (hplan : planOKP WL CHI nIX IT = true)
    (h0 : listInitOK 7 [(0, 1), (1, 1), (24, -1), (300, -2)] (S 0) = true)
    (h1 : listInitOK 7 [(0, 1), (1, 1), (24, -1), (300, 2)] (S 1) = true) (h2 : S 2 = S 0)
    (hws : witsOK IT (T.map Prod.snd) = true) (hN : 2 * IT.length ≤ N) {nV : ℕ}
    (hnV : T.length = nV)
    (hv : ∀ t < nV, valOK 7 (endSt S CHI IT t) (trOf 7 (endSt S CHI IT t))
      (xOf 7 (endSt S CHI IT t)) = true)
    (t : ℕ) (ht : t < T.length) :
    DyRes 7 (trA2 (wordLin T[t].1.1 (wv T[t].2))) (trOf 7 (endSt S CHI IT t)) ∧
      DyRes 7 (Baby.xStarCoord (wordLin T[t].1.1 (wv T[t].2))) (xOf 7 (endSt S CHI IT t)) := by
  obtain ⟨vA, -, rA, -⟩ := item_facts (by norm_num) (by norm_num) (by norm_num) hd hp hw hWL
    hCHI hc hix hplan h0 h1 h2 hws hN t ht
  have e := evalWord_sound _ vA (wit T[t].2)
  rw [interp_wit] at e
  rw [← e]
  exact val_dyRes rA (hv t (hnV ▸ ht))

theorem natCast_inj_of_lt {m a b : ℕ} (h : (a : ZMod m) = b) (ha : a < m) (hb : b < m) : a = b := by
  rw [ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h

theorem res_inj {n : ℕ} (hn : 1 ≤ n) {ι : Type*} {f : ι → ℚ} {R : ι → ℕ}
    (hf : ∀ i, DyRes n (f i) (R i)) (hR : ∀ i, R i < 2 ^ n - 1) (hd : ∀ i j, R i = R j → i = j) :
    Function.Injective f := by
  intro i j h
  have hi := hf i
  rw [h] at hi
  exact hd i j (natCast_inj_of_lt (dyRes_unique hn hi (hf j)) (hR i) (hR j))

theorem res_inj₂ {n : ℕ} (hn : 1 ≤ n) {ι : Type*} {f g : ι → ℚ} {R Q : ι → ℕ}
    (hf : ∀ i, DyRes n (f i) (R i)) (hg : ∀ i, DyRes n (g i) (Q i)) (hR : ∀ i, R i < 2 ^ n - 1)
    (hQ : ∀ i, Q i < 2 ^ n - 1) (hd : ∀ i j, R i = R j → Q i = Q j → i = j) :
    Function.Injective fun i => (f i, g i) := by
  intro i j h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  have hi := hf i
  have hi' := hg i
  rw [h1] at hi
  rw [h2] at hi'
  exact hd i j (natCast_inj_of_lt (dyRes_unique hn hi (hf j)) (hR i) (hR j))
    (natCast_inj_of_lt (dyRes_unique hn hi' (hg j)) (hQ i) (hQ j))

end CertificateChecks.KernelKDenseP.Axis

end
