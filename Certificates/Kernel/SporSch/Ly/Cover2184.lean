module

public import Certificates.Kernel.SporSch.Ly.CoverData
public import Certificates.Kernel.SporSch.Ly.BS18009
public import CFSG.Certificates.Kernel.Spor.TabWords
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Spor.RawSlSound
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LyCvF

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
open CFSG.Sporadic.Th.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.LyBS
open CertificateChecks.KernelSporSch.LyBSF CertificateChecks.KernelSporSch.LyCv

local notation "U" X:max => unpackL 111 12 1332 X

noncomputable abbrev CS : Array (Mat × Mat) := cStarArr (U B4)

theorem vTq {q : Nat} (hq : q < 121) : vld (TT q) = true ∧ vld (TTI q) = true :=
  (bAnd_iff _ _).1 (allN_spec vT q hq)

theorem vTTk (i y : Nat) : vld (TTk i y) = true ∧ vld (TTIk i y) = true := by
  unfold TTk TTIk
  by_cases h : i < 11 ∧ y < 11
  · rw [bl h.1, bl h.2]
    exact vTq (by rw [Nat.add_eq, Nat.mul_eq]; omega)
  · have hb : Bool.rec (motive := fun _ => Bool) false (Nat.blt y 11) (Nat.blt i 11) = false := by
      by_cases hi : i < 11
      · rw [bl hi, bl' (by omega)]
      · rw [bl' hi]
    rw [hb]
    exact ⟨vOne, vOne⟩

theorem foldM {G : Nat → Nat} (hG : ∀ j, vld (G j) = true) : ∀ (ws : List Nat) (X : Nat),
    vld X = true → ws.foldl (fun M j => mulM 5 111 M (U (G j))) (U X) =
      U (ws.foldl (fun X j => mul X (G j)) X) ∧ vld (ws.foldl (fun X j => mul X (G j)) X) = true
  | [], _, hX => ⟨rfl, hX⟩
  | j :: vs, X, hX => by
    simp only [List.foldl_cons]
    rw [mulE hX (hG j)]
    exact foldM hG vs _ (mulV hX (hG j))

theorem blk_of {f : Nat → Bool} (h : ∀ b < 11, allBlk (Nat.mul 11 b) f 11 = true) (q : Nat)
    (hq : q < 121) : f q = true := by
  have := allBlk_spec (h (q / 11) (by omega)) (q % 11) (Nat.mod_lt q (by norm_num))
  have e : Nat.add (Nat.mul 11 (q / 11)) (q % 11) = q := by
    rw [Nat.add_eq, Nat.mul_eq]
    exact Nat.div_add_mod q 11
  rwa [e] at this

theorem ttAll : ∀ q < 121, ttOK q = true := blk_of fun b hb => by
  interval_cases b
  exacts [tt0, tt1, tt2, tt3, tt4, tt5, tt6, tt7, tt8, tt9, tt10]

theorem ttiAll : ∀ q < 121, ttiOK q = true := blk_of fun b hb => by
  interval_cases b
  exacts [tti0, tti1, tti2, tti3, tti4, tti5, tti6, tti7, tti8, tti9, tti10]

theorem tab_eq (i y : Nat) : tabAt (transTab CS) i y = (U (TTk i y), U (TTIk i y)) := by
  by_cases h : i < 11 ∧ y < 11
  · have e : TTk i y = TT (11 * i + y) ∧ TTIk i y = TTI (11 * i + y) := by
      unfold TTk TTIk
      rw [bl h.1, bl h.2]
      exact ⟨rfl, rfl⟩
    have hq : 11 * i + y < 121 := by omega
    simp only [tabAt, transTab, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, h.1, h.2,
      dite_true, Option.getD_some]
    simp only [csCF, csCI]
    rw [idE, (foldM (fun j => (vCFx le_rfl j).1) _ _ vOne).1,
      (foldM (fun j => (vCFx le_rfl j).2) _ _ vOne).1, e.1, e.2]
    have h1 := Nat.eq_of_beq_eq_true (ttAll _ hq)
    have h2 := Nat.eq_of_beq_eq_true (ttiAll _ hq)
    have e1 : (11 * i + y) / 11 = i := by omega
    have e2 : (11 * i + y) % 11 = y := by omega
    rw [e1, e2] at h1 h2
    rw [h1, h2]
  · have e : TTk i y = ONE ∧ TTIk i y = ONE := by
      unfold TTk TTIk
      by_cases hi : i < 11
      · rw [bl hi, bl' (by omega)]
        exact ⟨rfl, rfl⟩
      · rw [bl' hi]
        exact ⟨rfl, rfl⟩
    rw [e.1, e.2, ← idE]
    by_cases hi : i < 11
    · have hy : ¬ y < 11 := by omega
      simp [tabAt, transTab, Array.getD_eq_getD_getElem?, hi, hy]
    · simp [tabAt, transTab, Array.getD_eq_getD_getElem?, hi]

theorem strip_eq : ∀ (ls : List Nat) (P : Array Nat) (X : Nat), vld X = true →
    ls.foldl (stripStep (transTab CS)) (P, U X) =
      ((ls.foldl stripK (P, X)).1, U (ls.foldl stripK (P, X)).2) ∧
      vld (ls.foldl stripK (P, X)).2 = true
  | [], _, _, hX => ⟨rfl, hX⟩
  | l :: ls, P, X, hX => by
    simp only [List.foldl_cons]
    have e2 : stripStep (transTab CS) (P, U X) l = ((stripK (P, X) l).1, U (stripK (P, X) l).2) := by
      unfold stripStep stripK
      dsimp only
      rw [tab_eq]
      dsimp only
      rw [mulE (vTTk _ _).2 hX]
    rw [e2]
    exact strip_eq ls _ _ (by unfold stripK; exact mulV (vTTk _ _).2 hX)

theorem res_eq (i x j : Nat) : relResidue CS (transTab CS) i x j =
    ((resK i x j).1, U (resK i x j).2) ∧ vld (resK i x j).2 = true := by
  unfold relResidue resK
  dsimp only
  rw [tab_eq, tab_eq, csCF]
  dsimp only
  have v0 := mulV (vCFx le_rfl j).1 (vTTk i x).1
  rw [mulE (vCFx le_rfl j).1 (vTTk i x).1, mulE (vTTk _ _).2 v0]
  exact strip_eq _ _ _ (mulV (vTTk _ _).2 v0)

theorem rel_one (i x j : Nat) (h : relJ i x j = true) :
    (!fixesBelow j i || (relResidue CS (transTab CS) i x j).1 == id11 &&
      ((relResidue CS (transTab CS) i x j).2 == idM 111 ||
        (relResidue CS (transTab CS) i x j).2 == matA)) = true := by
  obtain ⟨e, v⟩ := res_eq i x j
  rw [e]
  unfold relJ at h
  generalize hr : resK i x j = r at h v
  obtain ⟨P, X⟩ := r
  dsimp only at h v ⊢
  rw [CFSG.KS.Raw.strictB_eq] at h
  rw [idE, matA_eq, beqE v vOne, beqE v vA]
  exact h

theorem relOK_cs : relOK CS (transTab CS) = true := by
  unfold CFSG.Sporadic.LySchreier.Native.relOK
  rw [CFSG.KS.TW.allIn_iff]
  intro i hi
  rw [List.all_eq_true]
  intro x hx
  rw [CFSG.KS.TW.allIn_iff]
  intro j hj
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hx
  have hq := Co3hrel i k j hi hk hj
  exact rel_one i _ j hq
where
  Co3hrel (i k j : Nat) (hi : i < 11) (hk : k < (chainOrbits[i]!).length) (hj : j < 12) :
      relJ i (chainOrbits[i]!)[k] j = true := by
    have hk11 : k < 11 := by
      have : (chainOrbits[i]!).length ≤ 11 := by interval_cases i <;> decide
      omega
    have hg : 11 * i + k < 121 := by omega
    have h := LyCv.hrel (11 * i + k) hg j hj
    unfold relQ at h
    have e1 : Nat.add (Nat.mul (11 * i + k) 12) j / 132 = i := by
      rw [Nat.add_eq, Nat.mul_eq]
      omega
    have e2 : Nat.add (Nat.mul (11 * i + k) 12) j / 12 % 11 = k := by
      rw [Nat.add_eq, Nat.mul_eq]
      omega
    have e3 : Nat.add (Nat.mul (11 * i + k) 12) j % 12 = j := by
      rw [Nat.add_eq, Nat.mul_eq]
      omega
    rw [e1, e2, e3, bl hk] at h
    unfold orbAt at h
    rwa [getElem!_pos (chainOrbits[i]!) k hk] at h

theorem extend_size : ∀ (ws : List (List Int)) (acc : Array (Mat × Mat)),
    (extendM acc ws).size = acc.size + ws.length
  | [], _ => rfl
  | w :: vs, acc => by
    have e : extendM acc (w :: vs) = extendM (acc.push
        (evalWordM (fun i => (pairAt acc i).1) (fun i => (pairAt acc i).2) w,
          invM 5 111 (evalWordM (fun i => (pairAt acc i).1) (fun i => (pairAt acc i).2) w))) vs :=
      rfl
    rw [e, extend_size vs, Array.size_push, List.length_cons]
    omega

theorem cs_size : CS.size = 12 := by
  unfold CS cStarArr
  rw [extend_size]
  rfl

theorem cs_get {i : Nat} (hi : i < CS.size) : CS[i] = (U (CFx 12 i), U (CIx 12 i)) := by
  have e : CS[i] = pairAt CS i := by
    unfold pairAt
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
  rw [e, ← csCF, ← csCI]

theorem invPairs : invPairsOK CS = true := by
  unfold invPairsOK
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < 12 := by rw [← cs_size]; exact hi
  have e := cs_get hi
  have ef : CFx 12 i = CF i ∧ CIx 12 i = CI i := by
    unfold CFx CIx
    rw [bl hi']
    exact ⟨rfl, rfl⟩
  rw [ef.1, ef.2] at e
  rw [e]
  dsimp only
  rw [mulE (vCFi hi').1 (vCFi hi').2, idE, beqE (mulV (vCFi hi').1 (vCFi hi').2) vOne]
  exact allN_spec iCF i hi'

theorem cf0 : (pairAt CS 0).1 = U (CF 0) := by
  rw [csCF]
  unfold CFx
  rw [bl (by norm_num)]

theorem cf1 : (pairAt CS 1).1 = U (CF 1) := by
  rw [csCF]
  unfold CFx
  rw [bl (by norm_num)]

theorem facts : coverCertificate () = true := by
  unfold coverCertificate
  simp only []
  rw [b4_eq]
  have v0 := (vCFi (i := 0) (by norm_num)).1
  have v1 := (vCFi (i := 1) (by norm_num)).1
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, invPairs⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, transInv⟩, relOK_cs⟩, ?_⟩
  · rw [matB_eq, mulE vB vB4, idE, beqE (mulV vB vB4) vOne]
    exact bB
  · rw [cs_size]
    rfl
  · rw [cf0, matA_eq, mulE vA v0, mulE v0 vA, beqE (mulV vA v0) (mulV v0 vA)]
    exact c0A
  · rw [cf1, matA_eq, mulE vA v1, mulE v1 vA, beqE (mulV vA v1) (mulV v1 vA)]
    exact c1A
  · rw [cf0, idE, diffMod5_eq consts (hv v0) (hv vOne)]
    exact c0n1
  · rw [cf0, matA_eq, diffMod5_eq consts (hv v0) (hv vA)]
    exact c0nA
  · obtain ⟨e, v⟩ := res_eq 0 1 0
    rw [e, matA_eq, beqE v vA]
    have := r010
    exact this

end CertificateChecks.KernelSporSch.LyCvF

end
