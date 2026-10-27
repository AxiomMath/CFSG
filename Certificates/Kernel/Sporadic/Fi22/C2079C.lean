module

public import Certificates.Kernel.Sporadic.Fi22.C2079B
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Fo22C

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.ConjTree
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CertificateChecks.KernelSpor

theorem pS03 : permOK 3510 12 (mask 12) (3510 * 12) Fo22T.S03.F
    (pinvS 3510 12 (mask 12) Fo22T.S03.F) = true := by quickRfl
theorem pS02 : permOK 3510 12 (mask 12) (3510 * 12) Fo22T.S02.F
    (pinvS 3510 12 (mask 12) Fo22T.S02.F) = true := by quickRfl

theorem unpack_get' {n w P i : Nat} (hi : i < n) : (unpack n w P)[i]! = pg w (mask w) P i := by
  rw [unpack, getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem ofFn1_get {n w m : Nat} {T : Nat → Nat} {j : Nat} (hj : j < m) :
    (Array.ofFn (n := m) fun i => unpack n w (T i.val))[j]! = unpack n w (T j) := by
  rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]

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

theorem gens2_of {n w : Nat} {S : Array (Array Nat)} {GS : Nat → Nat}
    (h : ∀ k < 2, S[k]! = unpack n w (GS k)) :
    ∀ k < 2, (#[S[0]!, S[1]!] : Array (Array Nat))[k]! = unpack n w (GS k) := by
  intro k hk
  interval_cases k
  · exact h 0 (by norm_num)
  · exact h 1 (by norm_num)

theorem gens3 : ∀ k < 2, (#[SN3[0]!, SN3[1]!] : Array (Array Nat))[k]! =
    unpack 3510 12 (Fo22N3.S k) :=
  gens2_of fun k hk => ofFn_get (kS := 7) (by omega)

theorem cnN3' : ∀ k < 7, Cn 3510 12 (Fo22N3.S k) ∧ Cn 3510 12 (Fo22N3.SI k) ∧
    permOK 3510 12 (mask 12) (3510 * 12) (Fo22N3.S k) (Fo22N3.SI k) = true := by
  intro k hk
  obtain ⟨a, b, c⟩ := by simpa only [bAnd_iff] using allN_spec Fo22M.cnN3 k hk
  exact ⟨a, b, c⟩

theorem tree3_facts :
    treeConjN 3510 2 #[SN3[0]!, SN3[1]!] (unpack 3510 12 Fo22T.S03.F)
        (unpack 1574 12 Fo22T.Tree3.F) =
      (Array.ofFn (n := 1574 + 1) fun i => unpack 3510 12 (Fo22T3.T i.val)) ∧
      (∀ i < 1574 + 1, Cn 3510 12 (Fo22T3.T i)) ∧
      ∀ i < 1574 + 1, ∃ X, Rep 3510 (unpack 3510 12 (Fo22T3.T i)) X := by
  have e0 := Nat.eq_of_beq_eq_true Fo22M.s0T3
  refine treeConjN_eq (by norm_num) gens3 (fun k hk => (cnN3' k (by omega)).1)
    (fun k hk => (cnN3' k (by omega)).2.1) (fun k hk => (cnN3' k (by omega)).2.2) (by rw [e0])
    (by rw [e0]; exact Fo22M.cnS03) ⟨_, by rw [e0]; exact (rep_of_perm pS03).1⟩ rfl
    (steps_of (n := 3510) (w := 12) (r := 2) (N := 1574) (wt := 12) (NS := 25) (CH := 64)
      (by norm_num) Fo22T3.hS)

theorem classOK_of {S : Array (Array Nat)} {s₀ tree : Array Nat} {P : Array (Array Nat)} {m : Nat}
    {T : Array (Array Nat)} (hT : treeConjN 3510 2 #[S[0]!, S[1]!] s₀ tree = T) (hsz : T.size = m)
    (h1 : ∀ j < m, (isInvA 3510 T[j]! (invCand 3510 T[j]!) = true ∧
      eqA 3510 (conjA 3510 S[0]! T[j]!) T[(P[0]!)[j]!]! = true) ∧
      eqA 3510 (conjA 3510 S[1]! T[j]!) T[(P[1]!)[j]!]! = true)
    (h2 : ∀ j < m, ∀ k < j, eqA 3510 T[j]! T[k]! = false) :
    fo22ClassOK S s₀ tree P m = true := by
  unfold fo22ClassOK
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [hT]
  refine ⟨⟨hsz, allLt_iff.2 fun j hj => ?_⟩, allLt_iff.2 fun j hj => allLt_iff.2 fun k hk => ?_⟩
  · simp only [Bool.and_eq_true]
    exact h1 j hj
  · simpa using h2 j hj k hk

theorem class3 : fo22ClassOK fo22N3Strong fo22S03 fo22Tree3 fo22P3Strong 1575 = true := by
  rw [n3S, p3S, Fo22T.s03_eq, Fo22T.tree3_eq]
  obtain ⟨hT, hcn, hrep⟩ := tree3_facts
  have hA := acts_of (n := 3510) (w := 12) (r := 2) (wp := 11) (m := 1575) (NS := 25) (CH := 64)
    (by norm_num) Fo22T3.hA
  have hD := dists_of (m := 1575) (NS := 25) (CH := 64) (by norm_num) Fo22T3.hD
  refine classOK_of hT (by simp) (fun j hj => ?_) (fun j hj k hk => ?_)
  · rw [ofFn1_get hj]
    obtain ⟨X, hX⟩ := hrep j hj
    have hinv : isInvA 3510 (unpack 3510 12 (Fo22T3.T j))
        (invCand 3510 (unpack 3510 12 (Fo22T3.T j))) = true :=
      isInvA_of_rep hX (rep_invCand hX)
    have hact : ∀ i < 2, eqA 3510 (conjA 3510 SN3[i]! (unpack 3510 12 (Fo22T3.T j)))
        (Array.ofFn (n := 1574 + 1) fun i => unpack 3510 12 (Fo22T3.T i.val))[(SP3[i]!)[j]!]! =
          true := by
      intro i hi
      obtain ⟨h1, h2⟩ := hA j hj i hi
      obtain ⟨c1, c2, c3⟩ := cnN3' i (by omega)
      have hi7 : i < 7 := by omega
      have hi11 : i < 11 := by omega
      rw [ofFn_get (kS := 7) (PS := Fo22N3.S) hi7, ofFn_get (kS := 11) (PS := Fo22P3.S) hi11,
        unpack_get' hj, ofFn1_get h1,
        conj_unpack c1 (hcn j hj) c2 c3, eqA_unpack (cn_pconj c1 (hcn j hj) c2) (hcn _ h1), h2]
      exact Nat.beq_refl _
    exact ⟨⟨hinv, hact 0 (by norm_num)⟩, hact 1 (by norm_num)⟩
  · rw [ofFn1_get hj, ofFn1_get (by omega), eqA_unpack (hcn j hj) (hcn k (by omega))]
    exact hD j hj k hk

theorem cnH2' : ∀ k < 3, Cn 3510 12 (Fi22H2.S k) ∧ Cn 3510 12 (Fi22H2.SI k) ∧
    permOK 3510 12 (mask 12) (3510 * 12) (Fi22H2.S k) (Fi22H2.SI k) = true := by
  intro k hk
  obtain ⟨a, b, c⟩ := by simpa only [bAnd_iff] using allN_spec Fo22M.cnH2 k hk
  exact ⟨a, b, c⟩

theorem getElem_extract3 {a : Array (Array Nat)} {j : Nat} (hj : j < 3) (ha : 3 ≤ a.size) :
    (a.extract 0 3)[j]! = a[j]! := by
  rw [getElem!_pos _ j (by simp; omega), getElem!_pos a j (by omega), Array.getElem_extract]
  simp

theorem gens2 (htext : fi22Cent3510Text = Fi22E2065.textP) :
    ∀ k < 3, ((fi22CentStrong 2).extract 0 3)[k]! = unpack 3510 12 (Fi22H2.S k) := by
  intro k hk
  have hb := bindsH2 htext
  rw [getElem_extract3 hk (by rw [hb.2.2.2.1]; norm_num), hb.2.2.2.2.1 k (by omega)]

theorem tree2_facts (htext : fi22Cent3510Text = Fi22E2065.textP) :
    treeConjN 3510 3 ((fi22CentStrong 2).extract 0 3) (unpack 3510 12 Fo22T.S02.F)
        (unpack 26 7 Fo22T.Tree2.F) =
      (Array.ofFn (n := 26 + 1) fun i => unpack 3510 12 (Fo22T2.T i.val)) ∧
      (∀ i < 26 + 1, Cn 3510 12 (Fo22T2.T i)) ∧
      ∀ i < 26 + 1, ∃ X, Rep 3510 (unpack 3510 12 (Fo22T2.T i)) X := by
  have e0 := Nat.eq_of_beq_eq_true Fo22M.s0T2
  refine treeConjN_eq (by norm_num) (gens2 htext) (fun k hk => (cnH2' k hk).1)
    (fun k hk => (cnH2' k hk).2.1) (fun k hk => (cnH2' k hk).2.2) (by rw [e0])
    (by rw [e0]; exact Fo22M.cnS02) ⟨_, by rw [e0]; exact (rep_of_perm pS02).1⟩ rfl
    (steps_of (n := 3510) (w := 12) (r := 3) (N := 26) (wt := 7) (NS := 1) (CH := 27)
      (by norm_num) Fo22T2.hS)

theorem mem_T2
    (htext : fi22Cent3510Text = Fi22E2065.textP) :
    ∀ i < 27, ∀ X, Rep 3510 (unpack 3510 12 (Fo22T2.T i)) X → X ∈ fi22H 2 := by
  have hb := bindsH2 htext
  obtain ⟨-, hcn, hrep⟩ := tree2_facts htext
  have hS := steps_of (n := 3510) (w := 12) (r := 3) (N := 26) (wt := 7) (NS := 1) (CH := 27)
    (by norm_num) Fo22T2.hS
  have e0 := Nat.eq_of_beq_eq_true Fo22M.s0T2
  have hgH : ∀ k < 3, permOfArr 3510 (unpack 3510 12 (Fi22H2.S k)) ∈ fi22H 2 := by
    intro k hk
    have := strong_le_H (c := 2) (by norm_num) (Subgroup.subset_closure
      ⟨k, by rw [hb.2.2.2.1]; omega, rfl⟩)
    rwa [hb.2.2.2.2.1 k (by omega)] at this
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi X hX
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      rw [e0] at hX
      have hr := (rep_of_perm pS02).1
      rw [hX.unique hr]
      exact mem_H (by norm_num) hb Fi22H2.head Fi22H2.tl Fi22H2.hst hr
        (mem_P Fo22M.cnS02 Fo22M.pS02 pS02) Fo22M.hS02
    · obtain ⟨hlt, hstep⟩ := hS (i - 1) (by omega)
      rw [show i - 1 + 1 = i by omega] at hstep hlt
      set t := pg 7 (mask 7) Fo22T.Tree2.F (i - 1)
      have hk : t % 3 < 3 := Nat.mod_lt _ (by norm_num)
      obtain ⟨Y, hY⟩ := hrep (t / 3) (by omega)
      obtain ⟨c1, c2, c3⟩ := cnH2' (t % 3) hk
      have hg := rep_of_perm c3
      have hc := rep_conj hg.1 hg.2 hY
      rw [conj_unpack c1 (hcn _ (by omega)) c2 c3, ← hstep] at hc
      rw [hX.unique hc]
      have hYH := ih (t / 3) (by omega) (by omega) Y hY
      exact (fi22H 2).mul_mem (hgH _ hk) ((fi22H 2).mul_mem hYH ((fi22H 2).inv_mem (hgH _ hk)))

theorem h2OK_of {Sh hgens : Array (Array Nat)} {s₀ tree : Array Nat} {P : Array (Array Nat)}
    {T : Array (Array Nat)} (hT : treeConjN 3510 3 hgens s₀ tree = T) (hsz : T.size = 27)
    (h1 : ∀ j < 27, (isInvA 3510 T[j]! (invCand 3510 T[j]!) = true ∧
      siftA 3510 (rawLevels 3510 Sh fo22HBase) fo22HBase 0 T[j]! = true) ∧
      ∀ i < 3, (P[i]!)[j]! < 27 ∧ eqA 3510 (conjA 3510 hgens[i]! T[j]!) T[(P[i]!)[j]!]! = true)
    (h2 : ∀ j < 27, ∀ k < 27, j = k ∨ eqA 3510 T[j]! T[k]! = false)
    (h3 : ∀ j < 27, ∀ k < 27, eqA 3510 (compA 3510 T[j]! T[k]!) (compA 3510 T[k]! T[j]!) = true) :
    fo22H2OK Sh hgens s₀ tree P = true := by
  unfold fo22H2OK
  simp only [Bool.and_eq_true, beq_iff_eq]
  rw [hT]
  refine ⟨⟨⟨hsz, allLt_iff.2 fun j hj => ?_⟩, allLt_iff.2 fun j hj => allLt_iff.2 fun k hk => ?_⟩,
    allLt_iff.2 fun j hj => allLt_iff.2 fun k hk => h3 j hj k hk⟩
  · simp only [Bool.and_eq_true]
    exact ⟨(h1 j hj).1, allLt_iff.2 fun i hi => by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact (h1 j hj).2 i hi⟩
  · simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true']
    exact h2 j hj k hk

theorem h2
    (htext : fi22Cent3510Text = Fi22E2065.textP) :
    fo22H2OK (fi22CentStrong 2) ((fi22CentStrong 2).extract 0 3) fo22S02 fo22Tree2
      fo22P2Strong = true := by
  rw [p2S, Fo22T.s02_eq, Fo22T.tree2_eq]
  obtain ⟨hT, hcn, hrep⟩ := tree2_facts htext
  have hA := acts_of (n := 3510) (w := 12) (r := 3) (wp := 5) (m := 27) (NS := 1) (CH := 27)
    (by norm_num) Fo22T2.hA
  have hD := dists_of (m := 27) (NS := 1) (CH := 27) (by norm_num) Fo22T2.hD
  have hM := mem_T2 htext
  have hcomm := Fo22T2.comm2
  refine h2OK_of hT (by simp) (fun j hj => ?_) (fun j hj k hk => ?_) (fun j hj k hk => ?_)
  · rw [ofFn1_get hj]
    obtain ⟨X, hX⟩ := hrep j hj
    have hinv : isInvA 3510 (unpack 3510 12 (Fo22T2.T j))
        (invCand 3510 (unpack 3510 12 (Fo22T2.T j))) = true :=
      isInvA_of_rep hX (rep_invCand hX)
    have hsift : siftA 3510 (rawLevels 3510 (fi22CentStrong 2) fo22HBase) fo22HBase 0
        (unpack 3510 12 (Fo22T2.T j)) = true :=
      (siftA_iff_mem_fi22H (c := 2) (by norm_num) hX).2 (hM j hj X hX)
    refine ⟨⟨hinv, hsift⟩, fun i hi => ?_⟩
    obtain ⟨h1, h2⟩ := hA j hj i hi
    obtain ⟨c1, c2, c3⟩ := cnH2' i hi
    have hi11 : i < 11 := by omega
    rw [ofFn_get (kS := 11) (PS := Fo22P2.S) hi11, unpack_get' hj, ofFn1_get h1, gens2 htext i hi,
      conj_unpack c1 (hcn j hj) c2 c3, eqA_unpack (cn_pconj c1 (hcn j hj) c2) (hcn _ h1), h2]
    exact ⟨h1, Nat.beq_refl _⟩
  · rw [ofFn1_get hj, ofFn1_get hk, eqA_unpack (hcn j hj) (hcn k hk)]
    rcases lt_trichotomy j k with h | h | h
    · right
      have h1 := hD k hk j h
      cases h' : Nat.beq (Fo22T2.T j) (Fo22T2.T k)
      · rfl
      · rw [Nat.eq_of_beq_eq_true h', Nat.beq_refl] at h1
        exact absurd h1 (by decide)
    · left
      exact h
    · right
      exact hD j hj k h
  · rw [ofFn1_get hj, ofFn1_get hk, compA_unpack (hcn j hj) (hcn k hk),
      compA_unpack (hcn k hk) (hcn j hj),
      eqA_unpack (canonK_pcomp (hcn j hj) (hcn k hk)) (canonK_pcomp (hcn k hk) (hcn j hj))]
    exact allN_spec (allN_spec hcomm j hj) k hk

end CertificateChecks.KernelSpor.Fo22C

end
