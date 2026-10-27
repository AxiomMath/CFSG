module

public import Certificates.Kernel.LocalComp.Weyl3222K
public import Certificates.Kernel.LocalComp.Weyl3186
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylUData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.WeylAbelData

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.W3186

open CFSG.KC.Enum CFSG.KS CFSG.KLC.E8 CFSG.EvenSmallLie.OmegaEight CFSG.EvenSmallLie.OmegaEight.Weyl
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CertificateChecks.KernelLC
open CFSG.RankThree.Native (rep_of_eqA permOfArr_eq_of_rep)

attribute [local irreducible] okC spMul

theorem eqA_code {a b : ℕ} (ha : okC a = true) (hb : okC b = true) {t u : Array ℕ}
    (ht : Rep 240 t (Φ a)) (hu : Rep 240 u (Φ b)) : eqA 240 t u = Nat.beq a b := by
  by_cases h : a = b
  · subst h
    rw [Nat.beq_refl]
    exact (eqA_iff ht hu).2 rfl
  · rw [beq_false h]
    exact Bool.eq_false_iff.2 fun e => h (Φ_inj ha hb ((eqA_iff ht hu).1 e))

theorem rep_mul {a b : ℕ} (ha : okC a = true) (hb : okC b = true) {t u : Array ℕ}
    (ht : Rep 240 t (Φ a)) (hu : Rep 240 u (Φ b)) : Rep 240 (compA 240 t u) (Φ (spMul a b)) := by
  have h := rep_compA ht hu
  rwa [Φ_mul ha hb] at h

theorem rep_id' : Rep 240 (idA 240) (Φ spId) := by
  rw [Φ_id]
  exact rep_idA

theorem memE1_code {c : ℕ} (hc : okC c = true) {t : Array ℕ} (ht : Rep 240 t (Φ c)) :
    memE1 frameArrs t = frameK' c := by
  rw [memE1_congr ((eqA_iff ht (rep_Φ hc)).2 rfl)]
  change memE1L rootList keyPts (frameArrsL rootList) (spArrC rootList c) = _
  exact spC_memE1 hSP hc

theorem allLt_eq_allN {n : ℕ} {p q : ℕ → Bool} (h : ∀ i < n, p i = q i) : allLt n p = allN n q := by
  rw [Bool.eq_iff_iff, allLt_iff, allN_iff]
  exact ⟨fun h' i hi => h i hi ▸ h' i hi, fun h' i hi => (h i hi).symm ▸ h' i hi⟩

theorem signC_eq (m : ℕ) : signC m = m * 2 ^ 24 + spId := by
  change m <<< 24 + spId = _
  rw [Nat.shiftLeft_eq]

theorem signArrs_eqL : signArrs = signArrsL rootList := rfl

theorem okSign : ∀ m ∈ [5, 15, 80, 85, 240], okC (signC m) = true := by decide +kernel

theorem rep_sign {m : ℕ} (hm : m < 256) (he : framePop m % 2 = 0) (hok : okC (signC m) = true) :
    Rep 240 signArrs[m]! (Φ (signC m)) := by
  have h := spC_sign hSP hm he
  rw [← signC_eq, ← signArrs_eqL] at h
  exact rep_of_eqA' (rep_Φ hok) (eqA_comm' h)

theorem rep_sign' {m : ℕ} (hm : m ∈ [5, 15, 80, 85, 240]) :
    Rep 240 signArrs[m]! (Φ (signC m)) := by
  have hl : m < 256 ∧ framePop m % 2 = 0 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl <;> decide
  exact rep_sign hl.1 hl.2 (okSign m hm)

theorem cg_codes : ∀ k < 6, spMask (e32 CGC k) = 0 ∧ ∀ j : Fin 8,
    ((cGens.getD k 1).symm j : ℕ) = (codeL (e32 CGC k)).idxOf (j : ℕ) := by
  decide +kernel

theorem okCG {k : ℕ} (hk : k < 6) : okC (e32 CGC k) = true := allN_spec kCG k hk

theorem rep_cg {k : ℕ} (hk : k < 6) : Rep 240 (permArr (cGens.getD k 1)) (Φ (e32 CGC k)) := by
  obtain ⟨h0, hl⟩ := cg_codes k hk
  rw [permArr_eq_listPermArr _ _ hl]
  exact rep_of_eqA' (rep_Φ (okCG hk)) (eqA_comm' (spC_perm hSP (okCG hk) h0))

theorem cGens_length : cGens.length = 6 := rfl

theorem cGens_all_eq (f : Equiv.Perm (Fin 8) → Bool) :
    cGens.all f = allN 6 (fun k => f (cGens.getD k 1)) := by
  rw [Bool.eq_iff_iff, List.all_eq_true, allN_iff]
  constructor
  · intro h k hk
    exact h _ (by rw [List.getD_eq_getElem _ _ (by rw [cGens_length]; exact hk)]; exact
      List.getElem_mem _)
  · intro h g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    have := h k hk
    rwa [List.getD_eq_getElem _ _ hk] at this

theorem u_at {i : ℕ} (hi : i < 8192) (b : Bool) :
    uniqueAt GC (tcB i b) = true ∧ centerCAt GC CGC (tcB i b) = true ∧
      centerModAt GC CGC (tcB i b) = true := by
  have h := range_all kU i hi
  simp only [uAt, strictB_eq', bAnd_eq, Bool.and_eq_true] at h
  cases b
  · exact ⟨h.1, h.2.2.1, h.2.2.2.2.1⟩
  · exact ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

theorem rec_true_eq (c t : Bool) : Bool.rec (motive := fun _ => Bool) true t c = (!c || t) := by
  cases c <;> rfl

theorem rec_true_left (c e : Bool) : Bool.rec (motive := fun _ => Bool) e true c = (c || e) := by
  cases c <;> rfl

theorem s0_sq : spMul s0C s0C = spId := by decide +kernel

theorem okId : okC spId = true := gens_facts.2.2.2.1
theorem okNeg : okC negC = true := gens_facts.2.2.1
theorem okS0 : okC s0C = true := gens_facts.2.1

theorem rep_inv_inv {g : ℕ} (hg : okC g = true) (hgg : spMul g g = spId) {a : Array ℕ}
    (ha : Rep 240 a (Φ g)) : Rep 240 (invCand 240 a) (Φ g) := by
  have h := rep_invCand' ha
  rwa [inv_eq_of_mul_eq_one_right (by rw [Φ_mul hg hg, hgg, Φ_id])] at h

theorem rep_GC {k : ℕ} (hk : k < 13) : Rep 240 tPlusGensArr[k]! (Φ (e32 GC k)) := rep_gen hk

theorem stab_code {x g : ℕ} (hx : okC x = true) (hg : okC g = true) (hgg : spMul g g = spId)
    {t a : Array ℕ} (ht : Rep 240 t (Φ x)) (ha : Rep 240 a (Φ g)) :
    (eqA 240 (compA 240 (compA 240 a t) (invCand 240 a)) t ||
      eqA 240 (compA 240 (compA 240 a t) (invCand 240 a)) (compA 240 t negArr)) = stabB x g := by
  have h1 := okC_mul hg hx
  have h2 := okC_mul h1 hg
  have h3 := okC_mul hx okNeg
  have hc := rep_mul h1 hg (rep_mul hg hx ha ht) (rep_inv_inv hg hgg ha)
  rw [eqA_code h2 hx hc ht, eqA_code h2 h3 hc (rep_mul hx okNeg ht rep_negArr'), stabB,
    strictB_eq', rec_true_left]

theorem s0_stab_code {x : ℕ} (hx : okC x = true) {t : Array ℕ}
    (ht : Rep 240 t (Φ x)) :
    (eqA 240 (compA 240 (compA 240 s0Arr t) s0Arr) t ||
      eqA 240 (compA 240 (compA 240 s0Arr t) s0Arr) (compA 240 t negArr)) = stabB x s0C := by
  have h1 := okC_mul okS0 hx
  have h2 := okC_mul h1 okS0
  have h3 := okC_mul hx okNeg
  have hc := rep_mul h1 okS0 (rep_mul okS0 hx rep_s0Arr' ht) rep_s0Arr'
  rw [eqA_code h2 hx hc ht, eqA_code h2 h3 hc (rep_mul hx okNeg ht rep_negArr'), stabB,
    strictB_eq', rec_true_left]

theorem unique_ok : uniqueCheck = true := by
  rw [uniqueCheck, allLt_iff]
  intro i hi
  rw [List.all_eq_true]
  intro b _
  dsimp only
  obtain ⟨hok, hrep, -⟩ := rep_tEltB hi b
  have hU := (u_at hi b).1
  generalize tcB i b = x at hok hrep hU
  generalize tElt tPlusCert i b = t at hrep
  unfold uniqueAt at hU
  have h2 := okC_mul hok hok
  have e4 : conjStable t = (allN 13 (fun k => stabB x (e32 GC k)) && stabB x s0C) := by
    rw [conjStable]
    congr 1
    · exact allLt_eq_allN fun k hk => stab_code hok (gens_facts.1 k hk).1 (gens_facts.1 k hk).2
        hrep (rep_GC hk)
    · exact s0_stab_code hok hrep
  have e1 : isId (compA 240 t t) = Nat.beq (spMul x x) spId :=
    eqA_code h2 okId (rep_mul hok hok hrep hrep) rep_id'
  have e2 : isId t = Nat.beq x spId := eqA_code hok okId hrep rep_id'
  have e3 : eqA 240 t negArr = Nat.beq x negC := eqA_code hok okNeg hrep rep_negArr'
  have e5 : eqA 240 t signArrs[15]! = Nat.beq x (signC 15) :=
    eqA_code hok (okSign 15 (by simp)) hrep (rep_sign' (by simp))
  have e6 : eqA 240 t signArrs[240]! = Nat.beq x (signC 240) :=
    eqA_code hok (okSign 240 (by simp)) hrep (rep_sign' (by simp))
  rw [e1, e2, e3, e4, e5, e6]
  simp only [bAnd_eq, notB'_eq, rec_true_eq, rec_true_left] at hU
  revert hU
  cases Nat.beq (spMul x x) spId <;> cases Nat.beq x spId <;> cases Nat.beq x negC <;>
    cases allN 13 (fun k => stabB x (e32 GC k)) <;> cases stabB x s0C <;>
    cases Nat.beq x (signC 15) <;> cases Nat.beq x (signC 240) <;> simp

theorem gc_sign {k : ℕ} (hk : k < 7) : e32 GC k = signC (1 + 2 ^ (k + 1)) := by
  rw [signC_eq, gen_codes.1 k hk]

theorem rep_sign_gc {k : ℕ} (hk : k < 7) : Rep 240 signArrs[1 + 2 ^ (k + 1)]! (Φ (e32 GC k)) := by
  rw [gc_sign hk]
  exact rep_sign (frameDecode_even k hk).2 (frameDecode_even k hk).1
    (by rw [← gc_sign hk]; exact (gens_facts.1 k (by omega)).1)

theorem comm_eq {x g : ℕ} (hx : okC x = true) (hg : okC g = true)
    {t a : Array ℕ} (ht : Rep 240 t (Φ x)) (ha : Rep 240 a (Φ g)) : commA' t a = commB x g :=
  eqA_code (okC_mul hx hg) (okC_mul hg hx) (rep_mul hx hg ht ha) (rep_mul hg hx ha ht)

theorem even_gc {k : ℕ} (hk : k < 7) : (1 + 2 ^ (k + 1)) ∈ List.range 256 ∧
    (!(framePop (1 + 2 ^ (k + 1)) % 2 == 0)) = false := by
  refine ⟨List.mem_range.2 (frameDecode_even k hk).2, ?_⟩
  rw [(frameDecode_even k hk).1]
  rfl

theorem rep_s15 : Rep 240 signArrs[15]! (Φ (signC 15)) := rep_sign' (by simp)

theorem centerC_ok : centerCCheck = true := by
  rw [centerCCheck, allLt_iff]
  intro i hi
  rw [List.all_eq_true]
  intro b _
  dsimp only
  obtain ⟨hok, hrep, -⟩ := rep_tEltB hi b
  have hC := (u_at hi b).2.1
  generalize tcB i b = x at hok hrep hC
  generalize tElt tPlusCert i b = t at hrep
  unfold centerCAt at hC
  have ok15 := okSign 15 (by simp)
  have ok240 := okSign 240 (by simp)
  cases hcomm : commGensC t
  · rfl
  rw [commGensC, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at hcomm
  obtain ⟨⟨c15, cE⟩, cC⟩ := hcomm
  rw [comm_eq hok ok15 hrep rep_s15] at c15
  have cE' : allN 7 (fun k => commB x (e32 GC k)) = true := allN_of_forall fun k hk => by
    have h := cE _ (even_gc hk).1
    rw [(even_gc hk).2, Bool.false_or] at h
    rwa [comm_eq hok (gens_facts.1 k (by omega)).1 hrep (rep_sign_gc hk)] at h
  have cC' : allN 6 (fun k => commB x (e32 CGC k)) = true := allN_of_forall fun k hk => by
    rw [cGens_all_eq] at cC
    have h := allN_spec cC k hk
    rwa [comm_eq hok (okCG hk) hrep (rep_cg hk)] at h
  rw [c15, cE', cC'] at hC
  simp only [rec_true_left] at hC
  have e1 : isId t = Nat.beq x spId := eqA_code hok okId hrep rep_id'
  rw [e1, eqA_code hok ok15 hrep rep_s15,
    eqA_code hok ok240 hrep (rep_sign' (by simp)), eqA_code hok okNeg hrep rep_negArr']
  simpa [Bool.or_assoc] using hC

theorem spInvK_spec {x : ℕ} (hx : okC x = true) (hxi : okC (spInvK x) = true)
    (h : Nat.beq (spMul x (spInvK x)) spId = true) : (Φ x)⁻¹ = Φ (spInvK x) := by
  rw [inv_eq_of_mul_eq_one_right]
  rw [Φ_mul hx hxi, Nat.eq_of_beq_eq_true h, Φ_id]

theorem rep_tInv' {i : ℕ} (hi : i < 8192) (b : Bool) :
    Rep 240 (tInv tPlusCert i b) (Φ (tcB i b))⁻¹ := by
  have h0 := rep_invCand' (rep_tElt hi)
  simp only [tElt, Bool.false_eq_true, ite_false] at h0
  cases b
  · rw [tInv, ite_eq_right_iff.2 (fun h => absurd h Bool.false_ne_true)]
    exact h0
  · rw [tInv, ite_eq_left_iff.2 (fun h => absurd rfl h)]
    have e : tcB i true = spMul (tcK PP i) s0C := rfl
    rw [e, ← Φ_mul (okTC hi) okS0, mul_inv_rev,
      inv_eq_of_mul_eq_one_right (by rw [Φ_mul okS0 okS0, s0_sq, Φ_id] : Φ s0C * Φ s0C = 1)]
    exact rep_compA rep_s0Arr' h0

theorem cf_eq {x xi d : ℕ} (hx : okC x = true) (hd : okC d = true) (hxi : okC xi = true)
    {t ti a : Array ℕ} (ht : Rep 240 t (Φ x)) (hti : Rep 240 ti (Φ xi))
    (ha : Rep 240 a (Φ d)) : memE1 frameArrs (commInv t ti a) = cfB x xi d := by
  have h1 := okC_mul hx hd
  have h2 := okC_mul h1 hxi
  have h3 := okC_mul h2 hd
  rw [cfB]
  exact memE1_code h3 (rep_mul h2 hd (rep_mul h1 hxi (rep_mul hx hd ht ha) hti) ha)

theorem centerMod_ok : centerModCheck = true := by
  rw [centerModCheck, allLt_iff]
  intro i hi
  rw [List.all_eq_true]
  intro b _
  dsimp only
  obtain ⟨hok, hrep, -⟩ := rep_tEltB hi b
  have hti := rep_tInv' hi b
  have hM := (u_at hi b).2.2
  generalize tcB i b = x at hok hrep hM hti
  generalize tElt tPlusCert i b = t at hrep
  generalize tInv tPlusCert i b = ti at hti
  unfold centerModAt at hM
  simp only [strictB_eq'] at hM
  obtain ⟨hxi, hM⟩ := (bAnd_iff _ _).1 hM
  obtain ⟨hinv, hM⟩ := (bAnd_iff _ _).1 hM
  rw [spInvK_spec hok hxi hinv] at hti
  have ok15 := okSign 15 (by simp)
  have ok5 := okSign 5 (by simp)
  have ok80 := okSign 80 (by simp)
  have ha := okC_mul hok ok5
  have hb := okC_mul hok ok80
  have hab := okC_mul ha ok80
  cases hcomm : commModGens t ti
  · rfl
  rw [commModGens, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at hcomm
  obtain ⟨⟨c15, cE⟩, cC⟩ := hcomm
  rw [comm_eq hok ok15 hrep rep_s15] at c15
  have cE' : allN 7 (fun k => cfB x (spInvK x) (e32 GC k)) = true := allN_of_forall fun k hk => by
    have h := cE _ (even_gc hk).1
    rw [(even_gc hk).2, Bool.false_or] at h
    rwa [cf_eq hok (gens_facts.1 k (by omega)).1 hxi hrep hti (rep_sign_gc hk)] at h
  have cC' : allN 6 (fun k => cfB x (spInvK x) (e32 CGC k)) = true := allN_of_forall fun k hk => by
    rw [cGens_all_eq] at cC
    have h := allN_spec cC k hk
    rwa [cf_eq hok (okCG hk) hxi hrep hti (rep_cg hk)] at h
  rw [c15, cE', cC'] at hM
  simp only [rec_true_left] at hM
  have r5 := rep_mul hok ok5 hrep (rep_sign' (by simp))
  have r80 := rep_mul hok ok80 hrep (rep_sign' (by simp))
  have r580 := rep_mul ha ok80 r5 (rep_sign' (by simp))
  rw [memE1_code hok hrep, memE1_code ha r5, memE1_code hb r80, memE1_code hab r580]
  simpa [Bool.or_assoc] using hM

theorem frameArrs_eqL : frameArrs = frameArrsL rootList := rfl

theorem rep_frame {v : ℕ} (hv : v < 256) : Rep 240 frameArrs[v]! (Φ (frameCodeK DPK E8.FR v)) := by
  have hf : okC (frameCodeK DPK E8.FR v) = true := by
    have h := kFr
    simp only [framesOK, bAnd_eq, Bool.and_eq_true] at h
    exact allN_spec h.2 v hv
  have h := spC_frame hSP (by rw [← dpk]; exact kFr) hv
  rw [← dpk, ← frameArrs_eqL] at h
  exact rep_of_eqA' (rep_Φ hf) h

theorem fsC_rep {S : ℕ} (hS : okC S = true) {s : Array ℕ} (hs : Rep 240 s (Φ S)) {v : ℕ}
    (hv : v < 256) : okC (fsC DPK E8.FR S v) = true ∧
      Rep 240 (commInv frameArrs[v]! frameArrs[v]! s) (Φ (fsC DPK E8.FR S v)) := by
  have hF := rep_frame hv
  have hf : okC (frameCodeK DPK E8.FR v) = true := by
    have h := kFr
    simp only [framesOK, bAnd_eq, Bool.and_eq_true] at h
    exact allN_spec h.2 v hv
  have e : fsC DPK E8.FR S v =
      spMul (spMul (spMul (frameCodeK DPK E8.FR v) S) (frameCodeK DPK E8.FR v)) S := by
    unfold fsC
    rw [strictN_eq']
  generalize frameCodeK DPK E8.FR v = F at e hF hf
  rw [e]
  have h1 := okC_mul hf hS
  have h2 := okC_mul h1 hf
  exact ⟨okC_mul h2 hS, rep_mul h2 hS (rep_mul h1 hf (rep_mul hf hS hF hs) hF) hs⟩

theorem okW : ∀ w ∈ pairMasks16, okC (signC w) = true ∧ w < 256 ∧ framePop w % 2 = 0 := by
  decide +kernel

theorem ws_sub : ∀ w ∈ [0, 3, 12, 15], w ∈ pairMasks16 := by decide
theorem ws_sub' : ∀ w ∈ [0, 48, 192, 240], w ∈ pairMasks16 := by decide

theorem commSet_of {S W n : ℕ} {ws : List ℕ} (hS : okC S = true) {s : Array ℕ}
    (hs : Rep 240 s (Φ S)) (hws : ∀ w ∈ ws, w ∈ pairMasks16) (hn : ws.length = n)
    (hW : ∀ j < n, ws.getD j 0 = pg 8 255 W j) (k : commSetK DPK E8.FR S W n = true) :
    commSetOK s ws = true := by
  have repW : ∀ w ∈ ws, Rep 240 signArrs[w]! (Φ (signC w)) := fun w hw => by
    obtain ⟨h1, h2, h3⟩ := okW w (hws w hw)
    exact rep_sign h2 h3 h1
  obtain ⟨k1, k2⟩ := (bAnd_iff _ _).1 k
  rw [commSetOK, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  constructor
  · intro v hv
    rw [List.mem_range] at hv
    have h := allN_spec k2 v hv
    simp only [inWK] at h
    obtain ⟨j, hj, hj'⟩ := not_allN h
    rw [notB'_eq, Bool.not_eq_false'] at hj'
    have he := Nat.eq_of_beq_eq_true hj'
    obtain ⟨hok, hrep⟩ := fsC_rep hS hs hv
    rw [List.any_eq_true]
    have hjm : ws.getD j 0 ∈ ws := by
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    refine ⟨_, hjm, ?_⟩
    rw [eqA_code hok (okW _ (hws _ hjm)).1 hrep (repW _ hjm), hW j hj, ← he, Nat.beq_refl]
  · intro w hw
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    have h := allN_spec k1 j (by omega)
    simp only [hitK, bAnd_eq, Bool.and_eq_true] at h
    obtain ⟨v, hv, hv'⟩ := not_allN h.2
    rw [notB'_eq, Bool.not_eq_false'] at hv'
    have he := Nat.eq_of_beq_eq_true hv'
    obtain ⟨hok, hrep⟩ := fsC_rep hS hs hv
    rw [List.any_eq_true]
    refine ⟨v, List.mem_range.2 hv, ?_⟩
    have hjw : ws[j] = pg 8 255 W j := by
      rw [← hW j (by omega), List.getD_eq_getElem]
    rw [eqA_code hok (okW _ (hws _ hw)).1 hrep (repW _ hw), hjw, he, Nat.beq_refl]

theorem commSet_ok : commSetCheck = true := by
  rw [commSetCheck, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨commSet_of (okSign 5 (by simp)) (rep_sign' (by simp)) ws_sub rfl
      (by decide +kernel) kCS5, commSet_of (okSign 80 (by simp)) (rep_sign' (by simp)) ws_sub' rfl
      (by decide +kernel) kCS80⟩,
    commSet_of (okSign 85 (by simp)) (rep_sign' (by simp)) (fun w hw => hw) rfl
      (by decide +kernel) kCS85⟩

open CFSG.EvenSmallLie.OmegaEight.Weyl in
theorem cert3222 : (uniqueCheck = true)
    ∧ (centerCCheck = true)
    ∧ (centerModCheck = true)
    ∧ (commSetCheck = true) :=
  ⟨unique_ok, centerC_ok, centerMod_ok, commSet_ok⟩

end CertificateChecks.KernelLC.W3186

end
