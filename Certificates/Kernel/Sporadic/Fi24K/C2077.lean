
module

public import Certificates.Kernel.Sporadic.Fi24K.T2077
public import CFSG.Certificates.Kernel.Spor.RawTreeSound
public import CFSG.Certificates.Kernel.Spor.ConjTreeSound
public import CFSG.Certificates.Kernel.Spor.SiftEq
public import CFSG.Certificates.Kernel.Spor.RawBaseEq
public import CFSG.Sporadic.FischerOddCore.Fi24R2KCheckInputs
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fi24C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.ConjTree
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Sporadic.FischerOddCore CertificateChecks.KernelSpor

theorem mask_eq (x : Nat) : mask x = 2 ^ x - 1 := by
  change (1 <<< x) - 1 = 2 ^ x - 1
  rw [Nat.one_shiftLeft]

theorem pg_row {w m P i t : Nat} (ht : t < m) :
    pg w (mask w) (pg (m * w) (mask (m * w)) P i) t = pg w (mask w) P (i * m + t) := by
  unfold pg
  rw [mask_eq, mask_eq]
  change ((P >>> (m * w * i) &&& (2 ^ (m * w) - 1)) >>> (w * t) &&& (2 ^ w - 1)) =
    (P >>> (w * (i * m + t)) &&& (2 ^ w - 1))
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < w
  · have h1 : w * t + j < m * w := by nlinarith
    have h2 : m * w * i + (w * t + j) = w * (i * m + t) + j := by ring
    simp [hj, h1, h2]
  · simp [hj]

theorem rowsOf_unpack {m k w N F : Nat} {PS : Nat → Nat} (hm : 0 < m) (hN : N = k * m)
    (h : ∀ j < k, PS j = pg (m * w) (mask (m * w)) F j) :
    rowsOf m (unpack N w F) = Array.ofFn (n := k) fun j => unpack m w (PS j.val) := by
  subst hN
  apply Array.ext
  · simp [rowsOf, unpack, Nat.mul_div_cancel k hm]
  · intro i h1 h2
    have hi : i < k := by simpa using h2
    have hle : i * m + m ≤ k * m := by
      have h := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hi)
      rwa [Nat.succ_mul] at h
    apply Array.ext
    · simp [rowsOf, unpack]
      omega
    · intro t t1 t2
      have ht : t < m := by simpa [unpack] using t2
      simp only [rowsOf, unpack, Array.getElem_ofFn, Array.getElem_extract]
      rw [h i hi, pg_row ht]

theorem kRows : allN 12 (fun j => Nat.beq (Fi24KC.S j) (pg 4536 (mask 4536) Fi24T.K.F j)) = true := by
  quickRfl
theorem pRows : allN 10 (fun j => Nat.beq (Fi24PC.S j) (pg 3402 (mask 3402) Fi24T.P.F j)) = true := by
  quickRfl
theorem kBase : allN 7 (fun t => Nat.beq fi24KBase[t]! (pg 9 (mask 9) Fi24KC.BP t)) = true := by
  quickRfl
theorem pBase : allN 4 (fun t => Nat.beq fi24PBase[t]! (pg 9 (mask 9) Fi24PC.BP t)) = true := by
  quickRfl
theorem permK : allN 12 (fun j => permOK 504 9 (mask 9) (504 * 9) (Fi24KC.S j) (Fi24KC.SI j)) =
    true := by quickRfl
theorem permP : allN 10 (fun j => permOK 378 9 (mask 9) (378 * 9) (Fi24PC.S j) (Fi24PC.SI j)) =
    true := by quickRfl
theorem cnK : allN 2 (fun j => bAnd(canonK 504 9 (mask 9) (504 * 9) (Fi24KC.S j),
    bAnd(canonK 504 9 (mask 9) (504 * 9) (Fi24KC.SI j),
      permOK 504 9 (mask 9) (504 * 9) (Fi24KC.S j) (Fi24KC.SI j)))) = true := by quickRfl
theorem s0T : Nat.beq (Fi24ST.T 0) Fi24T.S0.F = true := by quickRfl
theorem cnS0 : canonK 504 9 (mask 9) (504 * 9) Fi24T.S0.F = true := by quickRfl
theorem pS0 : permOK 504 9 (mask 9) (504 * 9) Fi24T.S0.F (pinvS 504 9 (mask 9) Fi24T.S0.F) = true := by
  quickRfl

noncomputable abbrev SA (n w kS : Nat) (PS : Nat → Nat) : Array (Array Nat) :=
  Array.ofFn (n := kS) fun j => unpack n w (PS j.val)

theorem ofFn_get {n w kS : Nat} {PS : Nat → Nat} {j : Nat} (hj : j < kS) :
    (SA n w kS PS)[j]! = unpack n w (PS j) := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem kS : fi24KStrong = SA 504 9 12 Fi24KC.S := by
  rw [fi24KStrong, Fi24T.k_eq]
  exact rowsOf_unpack (by norm_num) (by norm_num)
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec kRows j hj)

theorem pS : fi24PStrong = SA 378 9 10 Fi24PC.S := by
  rw [fi24PStrong, Fi24T.p_eq]
  exact rowsOf_unpack (by norm_num) (by norm_num)
    fun j hj => Nat.eq_of_beq_eq_true (allN_spec pRows j hj)

theorem bindsK : Binds 504 9 Fi24KC.S 12 7 Fi24KC.BP (SA 504 9 12 Fi24KC.S) fi24KBase :=
  ⟨by norm_num, by norm_num, by norm_num, by simp, fun j hj => ofFn_get hj, rfl,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec kBase t ht)⟩

theorem bindsP : Binds 378 9 Fi24PC.S 10 4 Fi24PC.BP (SA 378 9 10 Fi24PC.S) fi24PBase :=
  ⟨by norm_num, by norm_num, by norm_num, by simp, fun j hj => ofFn_get hj, rfl,
    fun t ht => Nat.eq_of_beq_eq_true (allN_spec pBase t ht)⟩

theorem prodK : ((List.range 7).map fun i => rcnt (Fi24KC.LR i)).prod = 80263249920 := by
  decide +kernel
theorem prodP : ((List.range 4).map fun i => rcnt (Fi24PC.LR i)).prod = 19595520 := by
  decide +kernel

theorem kChain : fi24KChainOK fi24KStrong fi24KWords = true := by
  unfold fi24KChainOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [kS, Fi24W.kW, rawOrbitSizesK_sound bindsK permK Fi24KC.hl, prodK]
  exact ⟨⟨by simp, rawChainK_sound (NS := 32) (CH := 16) bindsK Fi24KC.head Fi24KC.hl
    (by norm_num) Fi24KC.hs⟩, rfl⟩

theorem pChain : fi24PChainOK fi24PStrong fi24PWords = true := by
  unfold fi24PChainOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [pS, Fi24W.pW, rawOrbitSizesK_sound bindsP permP Fi24PC.hl, prodP]
  exact ⟨⟨by simp, rawChainK_sound (NS := 24) (CH := 16) bindsP Fi24PC.head Fi24PC.hl
    (by norm_num) Fi24PC.hs⟩, rfl⟩

theorem unpack_get' {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem ofFn1_get {n w m : Nat} {T : Nat → Nat} {j : Nat} (hj : j < m) :
    (Array.ofFn (n := m) fun i => unpack n w (T i.val))[j]! = unpack n w (T j) := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

theorem ct_of_sl {N NS CH : Nat} {f : Nat → Bool} (hN : N ≤ NS * CH)
    (hs : ∀ s < NS, allN CH (fun d => strictB (Nat.add (s * CH) d) (fun i =>
      bIf(Nat.blt i N, f i, true))) = true) : ∀ i < N, f i = true := by
  intro i hi
  obtain ⟨hCH, hsk, e⟩ := slice_cover hN hi
  have h1 := allN_spec (hs (i / CH) hsk) (i % CH) (Nat.mod_lt _ hCH)
  rw [strictB_eq, e] at h1
  exact bIf_of_true (Nat.blt_eq ▸ hi) h1

theorem steps_of {n w r N wt NS CH TF : Nat} {GS GSI T : Nat → Nat} (hN : N ≤ NS * CH)
    (hs : ∀ s < NS, stepSl n w r GS GSI T TF wt N (s * CH) CH = true) :
    ∀ i < N, pg wt (mask wt) TF i / r < i + 1 ∧
      T (i + 1) = pconj n w (GS (pg wt (mask wt) TF i % r)) (T (pg wt (mask wt) TF i / r))
        (GSI (pg wt (mask wt) TF i % r)) := by
  intro i hi
  have h := ct_of_sl (f := fun i => strictB (pg wt (mask wt) TF i) (fun t =>
    bAnd(Nat.blt (Nat.div t r) (Nat.succ i), Nat.beq (T (Nat.succ i))
      (pconj n w (GS (Nat.mod t r)) (T (Nat.div t r)) (GSI (Nat.mod t r)))))) hN hs i hi
  rw [strictB_eq] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  exact ⟨Nat.blt_eq ▸ h1, Nat.eq_of_beq_eq_true h2⟩

theorem acts_of {n w r wp m NS CH : Nat} {GS GSI T PA : Nat → Nat} (hN : m ≤ NS * CH)
    (hs : ∀ s < NS, actSl n w r GS GSI T PA wp m (s * CH) CH = true) :
    ∀ j < m, ∀ i < r, pg wp (mask wp) (PA i) j < m ∧
      pconj n w (GS i) (T j) (GSI i) = T (pg wp (mask wp) (PA i) j) := by
  intro j hj i hi
  have h := ct_of_sl (f := fun j => allN r (fun i => strictB (pg wp (mask wp) (PA i) j)
    (fun j' => bAnd(Nat.blt j' m, Nat.beq (pconj n w (GS i) (T j) (GSI i)) (T j'))))) hN hs j hj
  have h' := allN_spec h i hi
  rw [strictB_eq] at h'
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h'
  exact ⟨Nat.blt_eq ▸ h1, Nat.eq_of_beq_eq_true h2⟩

theorem dists_of {m NS CH : Nat} {T : Nat → Nat} (hN : m ≤ NS * CH)
    (hs : ∀ s < NS, distSl T m (s * CH) CH = true) :
    ∀ j < m, ∀ k < j, Nat.beq (T j) (T k) = false := by
  intro j hj k hk
  have h := ct_of_sl (f := fun j => strictB (T j) (fun x => allN j (fun k =>
    Bool.not (Nat.beq x (T k))))) hN hs j hj
  rw [strictB_eq] at h
  have h' := allN_spec h k hk
  simpa using h'

theorem rep_of_perm {n w p q : Nat} (h : permOK n w (mask w) (n * w) p q = true) :
    Rep n (unpack n w p) (permOfArr n (unpack n w p)) ∧
      isInvA n (unpack n w p) (invCand n (unpack n w p)) = true := by
  have h' := invEqK_sound h
  rw [h'.1]
  exact ⟨(rep_permOfArr h'.2).1, h'.2⟩

theorem cnK' : ∀ k < 2, Cn 504 9 (Fi24KC.S k) ∧ Cn 504 9 (Fi24KC.SI k) ∧
    permOK 504 9 (mask 9) (504 * 9) (Fi24KC.S k) (Fi24KC.SI k) = true := by
  intro k hk
  obtain ⟨a, b, c⟩ := by simpa only [bAnd_iff] using allN_spec cnK k hk
  exact ⟨a, b, c⟩

theorem gens : ∀ k < 2, (#[(SA 504 9 12 Fi24KC.S)[0]!, (SA 504 9 12 Fi24KC.S)[1]!] :
    Array (Array Nat))[k]! = unpack 504 9 (Fi24KC.S k) := by
  intro k hk
  interval_cases k
  · exact ofFn_get (n := 504) (w := 9) (kS := 12) (PS := Fi24KC.S) (j := 0) (by norm_num)
  · exact ofFn_get (n := 504) (w := 9) (kS := 12) (PS := Fi24KC.S) (j := 1) (by norm_num)

theorem treeConj_eq (n : Nat) (g₀ g₁ s₀ tree : Array Nat) :
    treeConj n g₀ g₁ s₀ tree = treeConjN n 2 #[g₀, g₁] s₀ tree := by
  unfold treeConj treeConjN
  congr 1
  funext acc t
  rcases Nat.mod_two_eq_zero_or_one t with h | h <;> simp [h]

theorem tree_facts :
    treeConjN 504 2 #[(SA 504 9 12 Fi24KC.S)[0]!, (SA 504 9 12 Fi24KC.S)[1]!]
        (unpack 504 9 Fi24T.S0.F) (unpack 377 10 Fi24T.Tree.F) =
      (Array.ofFn (n := 377 + 1) fun i => unpack 504 9 (Fi24ST.T i.val)) ∧
      (∀ i < 377 + 1, Cn 504 9 (Fi24ST.T i)) ∧
      ∀ i < 377 + 1, ∃ X, Rep 504 (unpack 504 9 (Fi24ST.T i)) X := by
  have e0 := Nat.eq_of_beq_eq_true s0T
  refine treeConjN_eq (by norm_num) gens (fun k hk => (cnK' k hk).1)
    (fun k hk => (cnK' k hk).2.1) (fun k hk => (cnK' k hk).2.2) (by rw [e0])
    (by rw [e0]; exact cnS0) ⟨_, by rw [e0]; exact (rep_of_perm pS0).1⟩ rfl
    (steps_of (n := 504) (w := 9) (r := 2) (N := 377) (wt := 10) (NS := 6) (CH := 64)
      (by norm_num) Fi24ST.hS)

theorem hi_of {G : Nat} (h : Cn 504 9 G) : Nat.shiftRight G (504 * 9) = 0 := by
  have h' : bAnd(szOK 504 9, bAnd(Nat.beq (Nat.shiftRight G (504 * 9)) (nat_lit 0),
      allN 504 (fun i => Nat.blt (pg 9 (mask 9) G i) 504))) = true := h
  obtain ⟨-, h2⟩ := (bAnd_iff (szOK 504 9) (bAnd(Nat.beq (Nat.shiftRight G (504 * 9)) (nat_lit 0),
    allN 504 (fun i => Nat.blt (pg 9 (mask 9) G i) 504)))).1 h'
  exact Nat.eq_of_beq_eq_true ((bAnd_iff (Nat.beq (Nat.shiftRight G (504 * 9)) (nat_lit 0))
    (allN 504 (fun i => Nat.blt (pg 9 (mask 9) G i) 504))).1 h2).1

theorem sOK_of {S : Array (Array Nat)} {s₀ tree : Array Nat} {P : Array (Array Nat)}
    {T : Array (Array Nat)} (hT : treeConjN 504 2 #[S[0]!, S[1]!] s₀ tree = T)
    (hsz : T.size = 378)
    (h1 : ∀ j < 378, ((isInvA 504 T[j]! (invCand 504 T[j]!) = true ∧
      siftA 504 (rawLevels 504 S fi24KBase) fi24KBase 0 T[j]! = true) ∧
      eqA 504 (conjA 504 S[0]! T[j]!) T[(P[0]!)[j]!]! = true) ∧
      eqA 504 (conjA 504 S[1]! T[j]!) T[(P[1]!)[j]!]! = true)
    (h2 : ∀ j < 378, ∀ k < 378, j = k ∨ eqA 504 T[j]! T[k]! = false)
    (h3 : ∀ j < 378, ∀ k < 378, eqA 504 (compA 504 T[j]! T[k]!) (compA 504 T[k]! T[j]!) = true) :
    fi24SOK S s₀ tree P = true := by
  unfold fi24SOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [treeConj_eq, hT]
  refine ⟨⟨⟨hsz, allLt_iff.2 fun j hj => ?_⟩, allLt_iff.2 fun j hj => allLt_iff.2 fun k hk => ?_⟩,
    allLt_iff.2 fun j hj => allLt_iff.2 fun k hk => h3 j hj k hk⟩
  · simp only [Bool.and_eq_true]
    exact h1 j hj
  · simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
    exact h2 j hj k hk

theorem baseComm {j k t : Nat} (hj : j < 378) (hk : k < 378) (ht : t < 7) :
    pg 9 (mask 9) (Fi24ST.T j) (pg 9 (mask 9) (Fi24ST.T k) (pg 9 (mask 9) Fi24KC.BP t)) =
      pg 9 (mask 9) (Fi24ST.T k) (pg 9 (mask 9) (Fi24ST.T j) (pg 9 (mask 9) Fi24KC.BP t)) := by
  have row : ∀ {j k : Nat}, j < 378 → k < j →
      pg 9 (mask 9) (Fi24ST.T j) (pg 9 (mask 9) (Fi24ST.T k) (pg 9 (mask 9) Fi24KC.BP t)) =
        pg 9 (mask 9) (Fi24ST.T k) (pg 9 (mask 9) (Fi24ST.T j) (pg 9 (mask 9) Fi24KC.BP t)) := by
    intro j k hj hk
    have h := Fi24ST.baseCommAll j hj
    unfold Fi24ST.baseCommRow at h
    simp only [strictB_eq] at h
    exact Nat.eq_of_beq_eq_true (allN_spec (allN_spec h k hk) t ht)
  rcases lt_trichotomy j k with h | h | h
  · exact (row hk h).symm
  · subst h
    rfl
  · exact row hj h

theorem sOK : fi24SOK fi24KStrong fi24S0 fi24STree fi24PStrong = true := by
  rw [kS, pS, Fi24T.s0_eq, Fi24T.tree_eq]
  obtain ⟨hT, hcn, hrep⟩ := tree_facts
  have hA := acts_of (n := 504) (w := 9) (r := 2) (wp := 9) (m := 378) (NS := 6) (CH := 64)
    (by norm_num) Fi24ST.hA
  have hD := dists_of (m := 378) (NS := 6) (CH := 64) (by norm_num) Fi24ST.hD
  have hsift : ∀ j < 378, siftK 504 9 (mask 9) (504 * 9) (pidn 504 9) Fi24KC.LR Fi24KC.TRI
      Fi24KC.BP 7 0 (Fi24ST.T j) = true := by
    intro j hj
    have h6 : j / 63 < 6 := by omega
    have h := allN_spec (Fi24ST.siftAll (j / 63) h6) (j % 63) (Nat.mod_lt _ (by norm_num))
    have e : Nat.add (j / 63 * 63) (j % 63) = j := by
      rw [Nat.add_eq]
      exact Nat.div_add_mod' j 63
    rw [e] at h
    exact h
  refine sOK_of hT (by simp) (fun j hj => ?_) (fun j hj k hk => ?_) (fun j hj k hk => ?_)
  · rw [ofFn1_get hj]
    obtain ⟨X, hX⟩ := hrep j hj
    have hinv : isInvA 504 (unpack 504 9 (Fi24ST.T j))
        (invCand 504 (unpack 504 9 (Fi24ST.T j))) = true :=
      isInvA_of_rep hX (rep_invCand hX)
    have hs : siftA 504 (rawLevels 504 (SA 504 9 12 Fi24KC.S) fi24KBase) fi24KBase 0
        (unpack 504 9 (Fi24ST.T j)) = true := by
      rw [siftK_eq bindsK permK Fi24KC.hl rfl (hi_of (hcn j hj)) (range_of_canonK (hcn j hj))]
      exact hsift j hj
    have hact : ∀ i < 2, eqA 504 (conjA 504 (SA 504 9 12 Fi24KC.S)[i]! (unpack 504 9 (Fi24ST.T j)))
        (Array.ofFn (n := 377 + 1) fun i => unpack 504 9 (Fi24ST.T i.val))[((SA 378 9 10
          Fi24PC.S)[i]!)[j]!]! = true := by
      intro i hi
      obtain ⟨h1, h2⟩ := hA j hj i hi
      obtain ⟨c1, c2, c3⟩ := cnK' i hi
      have hi12 : i < 12 := by omega
      have hi10 : i < 10 := by omega
      rw [ofFn_get (kS := 12) (PS := Fi24KC.S) hi12, ofFn_get (kS := 10) (PS := Fi24PC.S) hi10,
        unpack_get' hj, ofFn1_get h1, conj_unpack c1 (hcn j hj) c2 c3,
        eqA_unpack (cn_pconj c1 (hcn j hj) c2) (hcn _ h1), h2]
      exact Nat.beq_refl _
    exact ⟨⟨⟨hinv, hs⟩, hact 0 (by norm_num)⟩, hact 1 (by norm_num)⟩
  · rw [ofFn1_get hj, ofFn1_get hk, eqA_unpack (hcn j hj) (hcn k hk)]
    rcases lt_trichotomy j k with h | h | h
    · right
      have h1 := hD k hk j h
      cases h' : Nat.beq (Fi24ST.T j) (Fi24ST.T k)
      · rfl
      · rw [Nat.eq_of_beq_eq_true h', Nat.beq_refl] at h1
        exact absurd h1 (by decide)
    · left
      exact h
    · right
      exact hD j hj k h
  · rw [ofFn1_get hj, ofFn1_get hk]
    have hgrp := CFSG.KS.Raw.BaseEq.groupN (NS := 32) (CH := 16) bindsK Fi24KC.head Fi24KC.hl
      (by norm_num) Fi24KC.hs
    obtain ⟨γ, hγ, hPγ⟩ := hgrp.2.1 _ (hcn j hj) (hsift j hj)
    obtain ⟨δ, hδ, hPδ⟩ := hgrp.2.1 _ (hcn k hk) (hsift k hk)
    have ha := CFSG.KS.Raw.Orb.rep_unpack hPγ
    have hb := CFSG.KS.Raw.Orb.rep_unpack hPδ
    rw [CFSG.Monster.B.Co2.eqA_iff (CFSG.Monster.B.Co2.rep_compA ha hb)
      (CFSG.Monster.B.Co2.rep_compA hb ha)]
    refine CFSG.KS.Raw.BaseEq.eq_of_baseN (NS := 32) (CH := 16) bindsK Fi24KC.head Fi24KC.hl
      (by norm_num) Fi24KC.hs (Subgroup.mul_mem _ hγ hδ) (Subgroup.mul_mem _ hδ hγ)
      fun t ht hb' => Fin.ext ?_
    have e1 := hPγ (δ ⟨_, hb'⟩)
    have e2 := hPδ ⟨_, hb'⟩
    have e3 := hPδ (γ ⟨_, hb'⟩)
    have e4 := hPγ ⟨_, hb'⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← e1, ← e3, ← e2, ← e4]
    exact baseComm hj hk ht

open Certificates in
open CFSG CFSG.Sporadic CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2.Native in
open CFSG.Certificates.Native in
theorem certificate2077 : (fi24KChainOK fi24KStrong fi24KWords = true)
    ∧ (fi24PChainOK fi24PStrong fi24PWords = true)
    ∧ (fi24SOK fi24KStrong fi24S0 fi24STree fi24PStrong = true) := ⟨kChain, pChain, sOK⟩

end CertificateChecks.KernelSpor.Fi24C

end
