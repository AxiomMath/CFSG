module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4C0pKData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4C0pKData
public import Certificates.Kernel.J4M2.C12633
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs
public import CFSG.Sporadic.Th.F2Spec
public meta import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4M2 CertificateChecks.KernelJ4Q CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
  CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCheck

@[expose] noncomputable def encN (A : Array Nat) : Nat :=
  (List.range 112).foldr (fun i acc => Nat.lor (Nat.shiftLeft (A.toList.getD i 0) (128 * i)) acc) 0

@[expose] def natRowsOK (A : Array Nat) : Bool :=
  A.size == 112 && A.toList.all fun n => Nat.blt n (2 ^ 112)

theorem v2N_natV2 {n : Nat} (hn : n < 2 ^ 112) : v2N (natV2 n) = n := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 112
  · rw [← testBit_v2N _ (by omega)]
    exact V2.ofFn_testBit _ hk
  · have hle : 2 ^ 112 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : v2N (natV2 n) < 2 ^ 112 := v2N_lt112 (V2.ofFn_wf _)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h1 hle),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn hle)]

theorem foldr_congr_mem {α β : Type} {f g : α → β → β} :
    ∀ (l : List α) (b : β), (∀ a ∈ l, ∀ x, f a x = g a x) → l.foldr f b = l.foldr g b
  | [], _, _ => rfl
  | a :: l, b, h => by
    rw [List.foldr_cons, List.foldr_cons,
      foldr_congr_mem l b fun a' ha x => h a' (List.mem_cons_of_mem _ ha) x, h a List.mem_cons_self]

theorem natRows_enc (A : Array Nat) (h : natRowsOK A = true) :
    WfA (A.map natV2) ∧ encR (A.map natV2) = encN A := by
  unfold natRowsOK at h
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨hs, hb⟩ := h
  refine ⟨⟨by rw [Array.size_map, hs], ?_⟩, ?_⟩
  · rw [Array.all_eq_true]
    intro i hi
    rw [Array.getElem_map]
    exact V2.ofFn_wf _
  · unfold encR encN
    refine foldr_congr_mem _ _ fun i hi x => ?_
    have hi' : i < A.size := by rw [hs]; exact List.mem_range.1 hi
    have e1 : (A.map natV2).getD i V2.zero = natV2 A[i] := by
      simp [Array.getD_eq_getD_getElem?, hi']
    have e2 : A.toList.getD i 0 = A[i] := by simp [hi']
    have hlt : A[i] < 2 ^ 112 := by
      have := hb A[i] (Array.getElem_mem_toList hi')
      exact Nat.le_of_ble_eq_true this
    rw [e1, e2, v2N_natV2 hlt]

@[expose] noncomputable def letK : List Nat :=
  [encN gamAFwd, encN gamBFwd, encN gamZFwd, encN gamABwd, encN gamBBwd, encN gamZBwd]

theorem gam_rows_ok : (natRowsOK gamAFwd && natRowsOK gamBFwd && natRowsOK gamZFwd &&
    natRowsOK gamABwd && natRowsOK gamBBwd && natRowsOK gamZBwd) = true := by quickRfl

theorem let_enc {l : Nat} (hl : l < 6) :
    WfA c0pLetRows[l]! ∧ encR c0pLetRows[l]! = letK.getD l 0 := by
  have h := gam_rows_ok
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hA, hB⟩, hZ⟩, hAi⟩, hBi⟩, hZi⟩ := h
  rcases l with _ | _ | _ | _ | _ | _ | l
  · exact natRows_enc gamAFwd hA
  · exact natRows_enc gamBFwd hB
  · exact natRows_enc gamZFwd hZ
  · exact natRows_enc gamABwd hAi
  · exact natRows_enc gamBBwd hBi
  · exact natRows_enc gamZBwd hZi
  · omega

@[expose] noncomputable def wordK (w : List Nat) : Nat :=
  w.foldl (fun acc l => mulJ c rm acc (letK.getD l 0)) one

@[expose] noncomputable def eta12K (m : Nat) : Nat :=
  (List.range 12).foldl (fun acc j => if m.testBit j then mulJ c rm acc (gmK j) else acc) one

@[expose] noncomputable def qNFK (e : Bool) (m : Nat) : Nat :=
  mulJ c rm (if e then ZM else one) (eta12K m)

@[expose] noncomputable def kEltK (f : Bool × Nat × Nat) : Nat :=
  mulJ c rm (qNFK f.1 f.2.1) (powJ c rm one cK f.2.2)

theorem word_enc (w : List Nat) (hw : ∀ l ∈ w, l < 6) :
    WfA (c0pWordRows w) ∧ encR (c0pWordRows w) = wordK w := by
  have key : ∀ (l : List Nat), (∀ n ∈ l, n < 6) → ∀ (acc : Array V2) (a : Nat),
      WfA acc ∧ encR acc = a → WfA (l.foldl (fun acc n => mulRows acc c0pLetRows[n]!) acc) ∧
        encR (l.foldl (fun acc n => mulRows acc c0pLetRows[n]!) acc) =
          l.foldl (fun acc n => mulJ c rm acc (letK.getD n 0)) a := by
    intro l
    induction l with
    | nil => intro _ acc a h; exact h
    | cons n l ih =>
      intro hl acc a h
      rw [List.foldl_cons, List.foldl_cons]
      exact ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)) _ _
        (mul_enc hK h (let_enc (hl n List.mem_cons_self)))
  exact key w hw _ _ (id_enc hK)

theorem eta12_enc (m : Nat) : WfA (etaRows12 m) ∧ encR (etaRows12 m) = eta12K m := by
  have key : ∀ (l : List Nat), (∀ j ∈ l, j < 12) → ∀ (acc : Array V2) (a : Nat),
      WfA acc ∧ encR acc = a →
      WfA (l.foldl (fun acc j => if m.testBit j then mulRows acc gmats[j]! else acc) acc) ∧
        encR (l.foldl (fun acc j => if m.testBit j then mulRows acc gmats[j]! else acc) acc) =
          l.foldl (fun acc j => if m.testBit j then mulJ c rm acc (gmK j) else acc) a := by
    intro l
    induction l with
    | nil => intro _ acc a h; exact h
    | cons j l ih =>
      intro hl acc a h
      have hj := hl j List.mem_cons_self
      rw [List.foldl_cons, List.foldl_cons]
      apply ih (fun i hi => hl i (List.mem_cons_of_mem _ hi))
      by_cases hb : m.testBit j
      · simp only [hb, ↓reduceIte]
        exact mul_enc hK h (gm_enc (by omega))
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact h
  exact key (List.range 12) (fun j hj => List.mem_range.1 hj) _ _ (id_enc hK)

theorem qNF_enc (e : Bool) (m : Nat) : WfA (qNFRows e m) ∧ encR (qNFRows e m) = qNFK e m := by
  have h0 : WfA (if e then zM else idRows) ∧ encR (if e then zM else idRows) = (if e then ZM else one) := by
    cases e
    · exact id_enc hK
    · exact zM_enc
  exact mul_enc hK h0 (eta12_enc m)

theorem kElt_enc (f : Bool × Nat × Nat) : WfA (kEltRows f) ∧ encR (kEltRows f) = kEltK f :=
  mul_enc hK (qNF_enc _ _) (pow_enc hK cMat_encK _)

@[expose] def distN : List Nat → Bool
  | [] => true
  | x :: xs => xs.all (fun y => !Nat.beq x y) && distN xs

theorem zip_eq {α : Type} {R : α → Array V2} {K : α → Nat} (hR : ∀ f, WfA (R f) ∧ encR (R f) = K f) :
    ∀ (ws : List (List Nat)) (fs : List α), (∀ w ∈ ws, ∀ l ∈ w, l < 6) →
      (List.zip ws (fs.map R)).all (fun p => eqRows (c0pWordRows p.1) p.2) =
        (List.zip ws (fs.map K)).all (fun p => Nat.beq (wordK p.1) p.2)
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | w :: ws, f :: fs, hw => by
    simp only [List.map_cons, List.zip_cons_cons, List.all_cons]
    rw [eqRows_of (word_enc w (hw w List.mem_cons_self)) (hR f),
      zip_eq hR ws fs fun w' hw' => hw w' (List.mem_cons_of_mem _ hw')]

theorem dist_eq {α : Type} {R : α → Array V2} {K : α → Nat} (hR : ∀ f, WfA (R f) ∧ encR (R f) = K f) :
    ∀ fs : List α, allDistinct (fs.map R) = distN (fs.map K)
  | [] => rfl
  | x :: xs => by
    have e : ∀ y, eqRows (R x) (R y) = Nat.beq (K x) (K y) := fun y => eqRows_of (hR x) (hR y)
    simp only [List.map_cons, allDistinct, distN, List.all_map, Function.comp_def, e, dist_eq hR xs]

theorem c0pK_chk : ((List.zip k3Words (k3FormsN.map kEltK)).all (fun p => Nat.beq (wordK p.1) p.2) &&
    (List.zip q8Words (q8FormsN.map fun f => qNFK f.1 f.2)).all (fun p => Nat.beq (wordK p.1) p.2) &&
    distN (k3FormsN.map kEltK) && distN (q8FormsN.map fun f => qNFK f.1 f.2)) = true := by
  quickRfl

theorem c0pKWF_ok : c0pKWF = true := by
  unfold c0pKWF wfR
  rw [wf_bool zM_enc.1, wf_bool cMat_enc.1, Bool.true_and, Bool.true_and, List.all_eq_true]
  intro j hj
  exact wf_bool (gm_enc (n := j) (by have := List.mem_range.1 hj; omega)).1

theorem lens_ok : (k3Words.length == 24 && k3FormsN.length == 24 && q8Words.length == 8 &&
    q8FormsN.length == 8) = true := by quickRfl

theorem k3let_ok : (k3Words.all fun w => w.all fun l => decide (l < 6)) = true := by quickRfl

theorem q8let_ok : (q8Words.all fun w => w.all fun l => decide (l < 6)) = true := by quickRfl

theorem lets_of {ws : List (List Nat)} (h : (ws.all fun w => w.all fun l => decide (l < 6)) = true) :
    ∀ w ∈ ws, ∀ l ∈ w, l < 6 :=
  fun w hw l hl => of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 h w hw) l hl)

theorem c0pKOK_ok : c0pKOK = true := by
  have h := c0pK_chk
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hl := lens_ok
  simp only [Bool.and_eq_true] at hl
  obtain ⟨⟨⟨l1, l2⟩, l3⟩, l4⟩ := hl
  unfold c0pKOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨c0pKWF_ok, l1⟩, l2⟩, l3⟩, l4⟩, k3let_ok⟩, q8let_ok⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [zip_eq kElt_enc _ _ (lets_of k3let_ok)]
    exact h1
  · rw [zip_eq (R := fun f : Bool × Nat => qNFRows f.1 f.2) (K := fun f => qNFK f.1 f.2)
      (fun f => qNF_enc f.1 f.2) _ _ (lets_of q8let_ok)]
    exact h2
  · rw [dist_eq kElt_enc]
    exact h3
  · rw [dist_eq (R := fun f : Bool × Nat => qNFRows f.1 f.2) (K := fun f => qNFK f.1 f.2)
      (fun f => qNF_enc f.1 f.2)]
    exact h4

open CFSG.AGLEmbeddingD2.Wilson.NormalizerAction in
theorem c12608 : c0pKOK = true := c0pKOK_ok

end CertificateChecks.KernelJ4M2

end
