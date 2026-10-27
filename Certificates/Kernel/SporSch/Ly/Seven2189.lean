module

public import Certificates.Kernel.SporSch.Ly.SevD
public import Certificates.Kernel.SporSch.Ly.SevCSort
public import Certificates.Kernel.SporSch.Ly.BS18009
public import CFSG.Sporadic.Th.TableSpec
public import CFSG.Certificates.Kernel.Spor.RawSlSound
import Init.Data.Nat.Fold
import Init.Data.Array.Basic
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LySvF

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy CFSG.KS.SporSch.LySev
open CFSG.Sporadic.LySchreier.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.LyBS
open CertificateChecks.KernelSporSch.LyBSF CertificateChecks.KernelSporSch.LySv

local notation "U" X:max => unpackL 111 12 1332 X

theorem chain_at {Q : Nat → Bool} {nG R : Nat}
    (h : ∀ g < nG, ∀ r < R, Q (Nat.add (Nat.mul g R) r) = true) {t : Nat} (ht : t < nG * R) :
    Q t = true := by
  have hR : 0 < R := Nat.pos_of_ne_zero fun e => by simp [e] at ht
  have e : Nat.add (Nat.mul (t / R) R) (t % R) = t := Nat.div_add_mod' t R
  rw [← e]
  exact h _ (Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])) _ (Nat.mod_lt _ hR)

theorem chain_atB {Q : Nat → Bool} {nG R : Nat}
    (h : ∀ g < nG, ∀ r < R, Q (Nat.add (Nat.mul g R) r) = true) {t B : Nat} (ht : t < B)
    (hB : B ≤ nG * R := by decide) : Q t = true :=
  chain_at h (Nat.lt_of_lt_of_le ht hB)

theorem vAFi {i : Nat} (hi : i < 7) : vld (AF i) = true ∧ vld (AI i) = true :=
  andOf (allN_spec vAF i hi)

theorem vAFx {k : Nat} (hk : k ≤ 7) (i : Nat) : vld (AFx k i) = true ∧ vld (AIx k i) = true := by
  unfold AFx AIx
  by_cases h : i < k
  · rw [bl h]
    exact vAFi (by omega)
  · rw [bl' h]
    exact ⟨vOne, vOne⟩

def Rep7 (acc : Array (Mat × Mat)) (k : Nat) : Prop :=
  acc.size = k ∧ ∀ i < k, acc[i]! = (U (AF i), U (AI i))

theorem pairAt_rep7 {acc : Array (Mat × Mat)} {k : Nat} (h : Rep7 acc k) (i : Nat) :
    pairAt acc i = (U (AFx k i), U (AIx k i)) := by
  have hs := h.1
  unfold pairAt AFx AIx
  by_cases hi : i < k
  · rw [bl hi, ← h.2 i hi, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega),
      Option.getD_some, getElem!_pos acc i (by omega)]
  · rw [bl' hi, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega), Option.getD_none,
      idE]

theorem extend_rep7 : ∀ (ws : List (List Int)) (acc : Array (Mat × Mat)) (k : Nat),
    Rep7 acc k → k + ws.length ≤ 7 →
    (∀ t < ws.length, wordR 5 12 1332 111 8 L H CM RM (AFx (k + t)) (AIx (k + t)) ONE
      (ws.getD t []) = AF (k + t)) →
    Rep7 (extendM acc ws) (k + ws.length)
  | [], acc, k, h, _, _ => h
  | w :: vs, acc, k, h, hk, hw => by
    have e : extendM acc (w :: vs) = extendM (acc.push
        (evalWordM (fun i => (pairAt acc i).1) (fun i => (pairAt acc i).2) w,
          invM 5 111 (evalWordM (fun i => (pairAt acc i).1) (fun i => (pairAt acc i).2) w))) vs :=
      rfl
    have hlen : (w :: vs).length = vs.length + 1 := rfl
    have hs := h.1
    have hk' : k < 7 := by omega
    obtain ⟨hX, _⟩ := word_of (G := AFx k) (GI := AIx k) (g := fun i => (pairAt acc i).1)
      (gi := fun i => (pairAt acc i).2) (fun i => by rw [pairAt_rep7 h i])
      (fun i => by rw [pairAt_rep7 h i]) (fun i => (vAFx (by omega) i).1)
      (fun i => (vAFx (by omega) i).2) w
    have h0 := hw 0 (by simp)
    simp only [Nat.add_zero, List.getD_cons_zero] at h0
    rw [h0] at hX
    have hinv : invM 5 111 (U (AF k)) = U (AI k) :=
      invM_eq Nat.prime_five consts (hv (vAFi hk').1) (hv (vAFi hk').2) (allN_spec iAF k hk')
    have hrep : Rep7 (acc.push (U (AF k), U (AI k))) (k + 1) := by
      refine ⟨by rw [Array.size_push, h.1], fun i hi => ?_⟩
      rcases Nat.lt_or_ge i k with hik | hik
      · rw [getElem!_pos _ i (by rw [Array.size_push, h.1]; omega), Array.getElem_push_lt (by omega),
          ← getElem!_pos acc i (by omega), h.2 i hik]
      · have : i = k := by omega
        subst this
        rw [getElem!_pos _ i (by rw [Array.size_push, h.1]; omega)]
        simp [Array.getElem_push, hs]
    rw [e, hX, hinv, hlen, ← Nat.add_assoc, Nat.add_right_comm]
    refine extend_rep7 vs _ (k + 1) hrep (by omega) fun t ht => ?_
    have := hw (t + 1) (by simp; omega)
    simp only [List.getD_cons_succ] at this
    rw [Nat.add_right_comm k 1 t]
    exact this

theorem word_j {j : Nat} {W : List Int} {K : Nat → Nat} {m : Nat}
    (hall : ∀ k < m, Nat.beq (wordR 5 12 1332 111 8 L H CM RM (AFx j) (AIx j) (K k)
      (List.take 16 (List.drop (Nat.mul k 16) W))) (K (Nat.succ k)) = true)
    (hk : bAnd(Nat.beq (K 0) ONE, bAnd(Nat.beq (K m) (AF j), Nat.ble W.length (Nat.mul m 16))) =
      true) :
    wordR 5 12 1332 111 8 L H CM RM (AFx j) (AIx j) ONE W = AF j := by
  obtain ⟨h0, h⟩ := andOf hk
  obtain ⟨hm, hl⟩ := andOf h
  rw [← Nat.eq_of_beq_eq_true h0, chain hall (Nat.le_of_ble_eq_true hl), Nat.eq_of_beq_eq_true hm]

theorem tail_eq : strongWordsTail = [SW2, SW3, SW4, SW5, SW6] := by
  have hl := lines_sound lines
  rw [lsLen] at hl
  have e : strongWordsTail = (List.range 5).map fun j => LS.getD (j + 2) [] := by
    unfold strongWordsTail
    rw [LySWT.eq]
    exact List.map_congr_left fun j hj => hl (j + 2) (by simp at hj; omega)
  rw [e]
  decide +kernel

theorem f0 : Nat.beq (AF 0) A = true := by quickRfl
theorem i0 : Nat.beq (AI 0) A = true := by quickRfl
theorem f1 : Nat.beq (AF 1) B = true := by quickRfl
theorem i1 : Nat.beq (AI 1) B4 = true := by quickRfl
theorem vVV : vld V = true := by quickRfl
theorem vVI : vld VI = true := by quickRfl
theorem vTT : vld TT = true := by quickRfl
theorem zc : Nat.beq LySc.c 406875 = true := by quickRfl
theorem zcov : Nat.ble LySc.c (Nat.mul LySc.nS 32) = true := by quickRfl
theorem zns : Nat.ble LySc.nS 12736 = true := by quickRfl
theorem zc0 : Nat.beq (LySc.C 0) 1 = true := by quickRfl
theorem zcn : Nat.beq (LySc.C LySc.nS) LySc.c = true := by quickRfl
theorem zpt : Nat.beq (rowR LySc.PT 24 0) 0 = true := by quickRfl

theorem as_rep : Rep7 (aStarArr (U B4)) 7 := by
  have e : aStarArr (U B4) = extendM #[(U (AF 0), U (AI 0)), (U (AF 1), U (AI 1))]
      [SW2, SW3, SW4, SW5, SW6] := by
    unfold aStarArr
    rw [tail_eq, matA_eq, matB_eq, Nat.eq_of_beq_eq_true f0, Nat.eq_of_beq_eq_true i0,
      Nat.eq_of_beq_eq_true f1, Nat.eq_of_beq_eq_true i1]
  rw [e]
  have h2 : Rep7 #[(U (AF 0), U (AI 0)), (U (AF 1), U (AI 1))] 2 := by
    refine ⟨rfl, fun i hi => ?_⟩
    interval_cases i <;> rfl
  refine extend_rep7 _ _ 2 h2 (by simp) fun t ht => ?_
  simp only [List.length_cons, List.length_nil] at ht
  interval_cases t
  · exact word_j K2.all k2
  · exact word_j K3.all k3
  · exact word_j K4.all k4
  · exact word_j K5.all k5
  · exact word_j K6.all k6

theorem asF {j : Nat} (hj : j < 7) : (pairAt (aStarArr (U B4)) j).1 = U (AF j) := by
  rw [pairAt_rep7 as_rep j]
  unfold AFx
  rw [bl hj]

theorem bp_eq : bpRootArr = LySvD.bpD := by
  unfold bpRootArr LySvD.bpD
  rw [LyRDT.eq, digits_sound digs (by rw [ndg]; decide), ndg]

theorem uArr_eq : uArr = LySvD.uD := by
  unfold uArr LySvD.uD
  rw [bp_eq]

theorem key_eq : bpRootKey = LySvD.keyD := by
  unfold bpRootKey LySvD.keyD
  rw [bp_eq]

theorem up_eq : unpackL 111 12 1332 LySv.UP = padU uArr := by
  rw [uArr_eq]
  unfold unpackL padU
  refine congrArg (Array.ofFn (n := 111)) (funext fun i => ?_)
  refine congrArg (Array.ofFn (n := 111)) (funext fun j => ?_)
  have c := allN_spec (allN_spec upOK i.val i.isLt) j.val j.isLt
  have e := Nat.eq_of_beq_eq_true c
  by_cases hj : j.val < 7
  · rw [ite_eq_left hj]
    rw [bl hj] at e
    have e2 : (LySvD.uD[i.val]!)[j.val]! = fld(LySv.DG, 4 * (111 * j.val + i.val), 15) := by
      unfold LySvD.uD LySvD.bpD
      rw [getElem!_pos _ i.val (by simp), Array.getElem_ofFn, getElem!_pos _ j.val (by simpa using hj),
        Array.getElem_ofFn, getElem!_pos _ _ (by simp; omega), Array.getElem_ofFn]
    rw [e2]
    exact e
  · rw [ite_eq_right hj]
    rw [bl' hj] at e
    exact e

theorem ofFn_of_rOK {X : Nat} {R : Array Nat} (h : rOK X R = true) (hs : R.size = 49) :
    (Array.ofFn (n := 49) fun t =>
      fld(mulR 5 12 1332 111 8 L H CM RM X LySv.UP, 1332 * (t.val / 7) + 12 * (t.val % 7), 2 ^ 12 - 1)) =
      R := by
  unfold rOK at h
  rw [CFSG.KS.Raw.strictB_eq] at h
  apply Array.ext (by simp [hs])
  intro t h1 _
  have ht : t < 49 := by simpa using h1
  rw [Array.getElem_ofFn]
  have := Nat.eq_of_beq_eq_true (allN_spec h t ht)
  rw [← getElem!_pos R t (by omega)]
  exact this

theorem restrA {j : Nat} (h2 : 2 ≤ j) (h7 : j < 7) :
    restrArr (pairAt (aStarArr (U B4)) j).1 = RA[j - 2]! := by
  rw [asF h7, restr_eq consts (hv (vAFi h7).1) (hv vUP) up_eq]
  have hs : ∀ k < 5, (RA[k]!).size = 49 := by decide +kernel
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  refine ofFn_of_rOK ?_ (hs k (by omega))
  have hk : k < 5 := by omega
  interval_cases k
  · exact rA2
  · exact rA3
  · exact rA4
  · exact rA5
  · exact rA6

set_option exponentiation.threshold 10000 in
theorem stabA {j : Nat} (h2 : 2 ≤ j) (h7 : j < 7) : stabOK (pairAt (aStarArr (U B4)) j).1 = true := by
  rw [asF h7, stab_eq consts (hv (vAFi h7).1) (hv vUP) up_eq]
  have s : sOK (AF j) = true := by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    have hk : k < 5 := by omega
    interval_cases k
    · exact sA2
    · exact sA3
    · exact sA4
    · exact sA5
    · exact sA6
  unfold sOK at s
  rw [CFSG.KS.Raw.strictB_eq] at s
  exact s

theorem keyA {j : Nat} (h2 : 2 ≤ j) (h7 : j < 7) :
    actKey (frTable (pairAt (aStarArr (U B4)) j).1) bpRootKey = some bpRootKey := by
  have hst := stabA h2 h7
  have hr := restrA h2 h7
  rw [asF h7] at hst hr ⊢
  refine actKey_fix consts (hv (vAFi h7).1) (hv vUP) up_eq ?_ hst ?_ ?_
  · rw [key_eq, uArr_eq]
    exact LySvD.keyFacts
  · rw [hr]
    exact LySvD.rInv _ (by omega)
  · rw [hr, key_eq]
    exact LySvD.rKey _ (by omega)

theorem gens5' (k : Nat) (h : hDag[k]!.1 = 0) : hDag[k]!.2.1 < 5 := by
  by_cases hk : k < hDag.size
  · exact LySvD.gens5 k hk h
  · rw [getElem!_neg hDag k hk]
    decide

theorem foldl_congr {α β : Type} {f f' : β → α → β} :
    ∀ (l : List α) (b : β), (∀ x ∈ l, ∀ y, f y x = f' y x) → l.foldl f b = l.foldl f' b
  | [], _, _ => rfl
  | x :: l, b, h => by
    rw [List.foldl_cons, List.foldl_cons, h x (by simp)]
    exact foldl_congr l _ fun x' hx' => h x' (by simp [hx'])

theorem dag_congr {g g' : Nat → Array Nat} (h : ∀ j < 5, g j = g' j) : dagArr g = dagArr g' := by
  unfold dagArr
  rw [← Array.foldl_toList, ← Array.foldl_toList]
  refine foldl_congr _ _ fun e he y => ?_
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
  rw [Array.getElem_toList]
  by_cases h0 : hDag[k].1 = 0
  · rw [ite_eq_left h0, ite_eq_left h0]
    have := gens5' k (by rw [getElem!_pos hDag k (by simpa using hk)]; exact h0)
    rw [getElem!_pos hDag k (by simpa using hk)] at this
    rw [h _ this]
  · rw [ite_eq_right h0, ite_eq_right h0]

theorem dagLocal_congr {g g' : Nat → Array Nat} {v : Array (Array Nat)} (h : ∀ j < 5, g j = g' j) :
    dagLocalOK g v = dagLocalOK g' v := by
  unfold dagLocalOK
  refine congrArg (CFSG.Sporadic.Th.Native.allIn 0 hDag.size) (funext fun k => ?_)
  by_cases h0 : hDag[k]!.1 = 0
  · simp only [ite_eq_left h0, h _ (gens5' k h0)]
  · simp only [ite_eq_right h0]

theorem gensA (j : Nat) (hj : j < 5) :
    restrArr (pairAt (aStarArr (U B4)) (j + 2)).1 = RA[j]! := by
  rw [restrA (by omega) (by omega), Nat.add_sub_cancel]

theorem vals_eq : dagArr (fun j => restrArr (pairAt (aStarArr (U B4)) (j + 2)).1) = VALS := by
  rw [dag_congr (g' := fun j => RA[j]!) gensA]
  exact LySvD.dag_eq

theorem hp_eq : hGenPairs (aStarArr (U B4)) = HP := by
  have e : hGenPairs (aStarArr (U B4)) = Array.ofFn (n := 5) fun j => (RA[j.val]!, inv7 RA[j.val]!) := by
    unfold hGenPairs
    refine congrArg (Array.ofFn (n := 5)) (funext fun j => ?_)
    simp only []
    rw [gensA j.val j.isLt]
  rw [e]
  exact LySvD.hp

theorem g00 : Nat.beq (LySvV.GP0 0) (LySvD.VP 0) = true := by quickRfl
theorem g01 : Nat.beq (LySvV.GP0 1) (LySvD.VP 1) = true := by quickRfl
theorem g10 : Nat.beq (LySvV.GP1 0) (LySvD.VP 60) = true := by quickRfl
theorem g11 : Nat.beq (LySvV.GP1 1) (LySvD.VP 62) = true := by quickRfl
theorem g20 : Nat.beq (LySvV.GP2 0) (LySvD.VP 85) = true := by quickRfl
theorem g21 : Nat.beq (LySvV.GP2 1) (LySvD.VP 91) = true := by quickRfl
theorem kg0 : Nat.beq LySvV.kg0 2 = true := by quickRfl
theorem kg1 : Nat.beq LySvV.kg1 2 = true := by quickRfl
theorem kg2 : Nat.beq LySvV.kg2 2 = true := by quickRfl

theorem lvg {i : Nat} (hi : i < 3) {GP : Nat → Nat} {kg : Nat} (hkg : Nat.beq kg 2 = true)
    (h0 : Nat.beq (GP 0) (LySvD.VP ((hLevelGens[i]!)[0]!)) = true)
    (h1 : Nat.beq (GP 1) (LySvD.VP ((hLevelGens[i]!)[1]!)) = true) :
    (LySvD.lvV i).size = kg ∧ ∀ j < kg, (LySvD.lvV i)[j]! = dec49 (GP j) := by
  have hk := Nat.eq_of_beq_eq_true hkg
  subst hk
  refine ⟨(LySvD.lvGet i 0 hi (by decide)).1, fun j hj => ?_⟩
  rw [(LySvD.lvGet i j hi hj).2]
  interval_cases j
  · rw [Nat.eq_of_beq_eq_true h0]
  · rw [Nat.eq_of_beq_eq_true h1]

theorem allN_lt {n m : Nat} {f : Nat → Nat} (h : allN n (fun r => Nat.blt (f r) m) = true) :
    ∀ r < n, f r < m := fun r hr => Nat.blt_eq.mp (allN_spec h r hr)

@[expose] noncomputable def vrec (c : Nat) (E P : Nat → Nat) : Array (Array Nat) × Array Nat × Array Nat :=
  (Array.ofFn (n := c) fun i => dec7 (E i.val), Array.ofFn (n := c) fun i => Nat.land (P i.val) 1048575,
    Array.ofFn (n := c) fun i => Nat.shiftRight (P i.val) 20)

theorem orb0 : vecBFS (stdVec 0) (LySvD.lvV 0) = vrec LySvV.c0 LySvV.E0 LySvV.P0 ∧
    vecTreeOK (stdVec 0) (LySvD.lvV 0) (vrec LySvV.c0 LySvV.E0 LySvV.P0) = true := by
  have hns := Nat.le_of_ble_eq_true LySvV.ns0
  exact vbfs_sound (Hh := 128) (lvg (i := 0) (by decide) kg0 g00 g01) (eq_of_beq LySvD.root0)
    (allN_lt LySvD.red0) (Nat.eq_of_beq_eq_true LySvV.pl0)
    (by rw [Nat.eq_of_beq_eq_true LySvV.sz0]; decide) (Nat.le_of_ble_eq_true LySvV.cv0)
    (Nat.eq_of_beq_eq_true LySvV.st0) (fun q hq => by
      have c := chain_atB LySvV.vr0All (t := q) (B := 124) (by omega)
      unfold LySvV.vq0 at c
      rw [bl hq] at c
      exact Nat.eq_of_beq_eq_true c) (Nat.eq_of_beq_eq_true LySvV.fin0)

theorem orb1 : vecBFS (stdVec 1) (LySvD.lvV 1) = vrec LySvV.c1 LySvV.E1 LySvV.P1 ∧
    vecTreeOK (stdVec 1) (LySvD.lvV 1) (vrec LySvV.c1 LySvV.E1 LySvV.P1) = true := by
  have hns := Nat.le_of_ble_eq_true LySvV.ns1
  exact vbfs_sound (Hh := 128) (lvg (i := 1) (by decide) kg1 g10 g11) (eq_of_beq LySvD.root1)
    (allN_lt LySvD.red1) (Nat.eq_of_beq_eq_true LySvV.pl1)
    (by rw [Nat.eq_of_beq_eq_true LySvV.sz1]; decide) (Nat.le_of_ble_eq_true LySvV.cv1)
    (Nat.eq_of_beq_eq_true LySvV.st1) (fun q hq => by
      have c := chain_atB LySvV.vr1All (t := q) (B := 28) (by omega)
      unfold LySvV.vq1 at c
      rw [bl hq] at c
      exact Nat.eq_of_beq_eq_true c) (Nat.eq_of_beq_eq_true LySvV.fin1)

theorem orb2 : vecBFS (stdVec 2) (LySvD.lvV 2) = vrec LySvV.c2 LySvV.E2 LySvV.P2 ∧
    vecTreeOK (stdVec 2) (LySvD.lvV 2) (vrec LySvV.c2 LySvV.E2 LySvV.P2) = true := by
  have hns := Nat.le_of_ble_eq_true LySvV.ns2
  exact vbfs_sound (Hh := 128) (lvg (i := 2) (by decide) kg2 g20 g21) (eq_of_beq LySvD.root2)
    (allN_lt LySvD.red2) (Nat.eq_of_beq_eq_true LySvV.pl2)
    (by rw [Nat.eq_of_beq_eq_true LySvV.sz2]; decide) (Nat.le_of_ble_eq_true LySvV.cv2)
    (Nat.eq_of_beq_eq_true LySvV.st2) (fun q hq => by
      have c := chain_atB LySvV.vr2All (t := q) (B := 1) (by omega)
      unfold LySvV.vq2 at c
      rw [bl hq] at c
      exact Nat.eq_of_beq_eq_true c) (Nat.eq_of_beq_eq_true LySvV.fin2)

@[expose] noncomputable def crec : Array (Array Nat) × Array Nat × Array Nat :=
  (Array.ofFn (n := LySc.c) fun i => dec49 (rowR LySc.ET 147 i.val),
    Array.ofFn (n := LySc.c) fun i => Nat.land (rowR LySc.PT 24 i.val) 524287,
    Array.ofFn (n := LySc.c) fun i => Nat.shiftRight (rowR LySc.PT 24 i.val) 19)

set_option exponentiation.threshold 5000 in
theorem orbC : conjBFS RT HP 406875 = crec ∧ conjTreeOK RT HP crec = true := by
  have hc := Nat.eq_of_beq_eq_true zc
  have hcov := Nat.le_of_ble_eq_true zcov
  have hns := Nat.le_of_ble_eq_true zns
  refine cbfs_sound (kg := 5) (Hh := 32) (WT := LySc.WT) (SO := LySc.SOf) (SOI := LySc.SOIf) LySvD.hpSz
    le_rfl LySvD.kc
    (fun t ht => Nat.blt_eq.mp (allN_spec LySc.kb t ht)) (Nat.eq_of_beq_eq_true LySc.qm)
    LySvD.rt (allN_lt LySc.e0) (Nat.eq_of_beq_eq_true zpt) (fun i hi => ?_)
    (by omega) (by omega) hcov (Nat.eq_of_beq_eq_true zc0) (fun q hq => ?_)
    (Nat.eq_of_beq_eq_true zcn)
  · have c := chain_atB LySc.soAll (t := i / 256) (B := 1600) (by omega)
    unfold LySc.soQ at c
    have ei : Nat.add (Nat.mul (i / 256) 256) (i % 256) = i := Nat.div_add_mod' i 256
    have e : bIf(Nat.blt i LySc.c, sortB LySc.EE LySc.SOf LySc.SOIf LySc.c i, true) = true := by
      have := allBlk_spec c (i % 256) (Nat.mod_lt _ (by decide))
      rw [ei] at this
      exact this
    rw [bl hi] at e
    exact e
  · have c := chain_atB LySc.crAll (t := q) (B := 12736) (by omega)
    unfold LySc.crQ at c
    rw [bl hq] at c
    exact Nat.eq_of_beq_eq_true c

theorem hgS : ∀ i, seedM i = U (GS i) := fun i => by
  cases i with
  | zero => exact matA_eq
  | succ i => exact matB_eq

theorem hgiS : ∀ i, seedMInv (U B4) i = U (GSI i) := fun i => by
  cases i with
  | zero => exact matA_eq
  | succ i => rfl

theorem vGS : ∀ i, vld (GS i) = true := fun i => by
  cases i with
  | zero => exact vA
  | succ i => exact vB

theorem vGSI : ∀ i, vld (GSI i) = true := fun i => by
  cases i with
  | zero => exact vA
  | succ i => exact vB4

theorem v_eq : evalWordM seedM (seedMInv (U B4)) (transporterWord ()) = U V := by
  rw [(word_of hgS hgiS vGS vGSI _).1, Nat.eq_of_beq_eq_true vw]

theorem rt_eq : restrArr (mulM 5 111 (mulM 5 111 (invM 5 111 (U V)) matA) (U V)) = RT := by
  have v1 := vVV
  have v2 := vVI
  have v3 := vTT
  rw [invM_eq Nat.prime_five consts (hv v1) (hv v2) vvi, matA_eq, mulE v2 vA, mulE (mulV v2 vA) v1,
    Nat.eq_of_beq_eq_true tt, restr_eq consts (hv v3) (hv vUP) up_eq]
  exact ofFn_of_rOK rT (by decide +kernel)

theorem invPairsA : invPairsOK (aStarArr (U B4)) = true := by
  unfold invPairsOK
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < 7 := by rw [← as_rep.1]; exact hi
  have e := as_rep.2 i hi'
  rw [getElem!_pos _ i hi] at e
  rw [e]
  dsimp only
  rw [mulE (vAFi hi').1 (vAFi hi').2, idE, beqE (mulV (vAFi hi').1 (vAFi hi').2) vOne]
  exact allN_spec iAF i hi'

theorem facts : sevenCertificate () = true := by
  have v1 := vVV
  have v2 := vVI
  unfold sevenCertificate
  simp only []
  rw [b4_eq, vals_eq, v_eq, rt_eq, invM_eq Nat.prime_five consts (hv v1) (hv v2) vvi, hp_eq]
  have l0 : ((hLevelGens.getD 0 []).map fun k => VALS.getD k (id7 ())).toArray = LySvD.lvV 0 := rfl
  have l1 : ((hLevelGens.getD 1 []).map fun k => VALS.getD k (id7 ())).toArray = LySvD.lvV 1 := rfl
  have l2 : ((hLevelGens.getD 2 []).map fun k => VALS.getD k (id7 ())).toArray = LySvD.lvV 2 := rfl
  rw [l0, l1, l2, orb0.1, orb1.1, orb2.1, orbC.1]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, ?_⟩, invPairsA⟩, ?_⟩, LySvD.dagSz⟩, ?_⟩, LySvD.dagInv⟩,
    LySvD.dagStr⟩, LySvD.fix1⟩, LySvD.fix2⟩, orb0.2⟩, ?_⟩, orb1.2⟩, ?_⟩, orb2.2⟩, ?_⟩, ?_⟩,
    LySvD.hpInv⟩, orbC.2⟩, ?_⟩
  · rw [matB_eq, mulE vB vB4, idE, beqE (mulV vB vB4) vOne]
    exact bb
  · rw [as_rep.1]
    rfl
  · rw [CFSG.Sporadic.Th.allIn_eq_true]
    intro j h2 h7
    rw [keyA h2 h7, stabA h2 h7, Bool.and_true]
    exact (beq_self_eq_true bpRootKey.data : _)
  · rw [dagLocal_congr (g' := fun j => RA[j]!) gensA]
    exact LySvD.dagLoc
  · simp [vrec, Nat.eq_of_beq_eq_true LySvV.sz0]
  · simp [vrec, Nat.eq_of_beq_eq_true LySvV.sz1]
  · simp [vrec, Nat.eq_of_beq_eq_true LySvV.sz2]
  · rw [mulE v1 v2, idE, beqE (mulV v1 v2) vOne]
    exact vvi
  · simp [crec, Nat.eq_of_beq_eq_true zc]

end CertificateChecks.KernelSporSch.LySvF

end
