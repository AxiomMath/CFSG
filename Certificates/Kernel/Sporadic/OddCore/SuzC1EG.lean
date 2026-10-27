module

public import Certificates.Kernel.Sporadic.OddCore.SuzC1BF
public import Certificates.Kernel.Sporadic.OddCore.SuzC1ED
public import CFSG.Certificates.Kernel.Spor.PEnumSound
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzC1EG

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.LevelTwoData
open CFSG.Sporadic.SuzRecog.C1Model CFSG.Sporadic.SuzRecog.C1ModelData CFSG.PSL3Four.Native
open CFSG.ComponentClassification.AS81.SuzB0
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore
open CertificateChecks.KernelSpor.SuzTwCF CertificateChecks.KernelSpor.SuzMGF
  CertificateChecks.KernelSpor.SuzC1BF

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "ie" => invEqK 1782 11 (mask 11) (1782 * 11)
local notation "Id" => pidn 1782 11
local notation "W0" => SuzTwG 6
local notation "T1" => SuzInvT1.F 0

@[expose] noncomputable def qProdK (v : Nat) : Nat :=
  (List.range 6).foldl (fun R i => if v.testBit i then pc R (KernelLC.SuzB0Q.F i) else R) Id

@[expose] noncomputable def qEK (j : Nat) : Nat :=
  pc (qProdK (j / 2)) (if j % 2 == 1 then T1 else Id)

@[expose] noncomputable def decK (d : List Nat × Nat) : Nat := pc (cWK d.1) (qEK d.2)

@[expose] noncomputable def v0K (j : Nat) : Nat :=
  if j < 4 then SuzC1ET.G j else if j = 4 then W0 else if j = 5 then SuzC1BT 11 else SuzMGG 4

@[expose] noncomputable def b0K (j : Nat) : Nat :=
  if j < 4 then SuzC1ET.G j else if j = 4 then W0 else if j = 5 then SuzTwG 2 else SuzMGG 4

@[expose] noncomputable def nt0K (j : Nat) : Nat :=
  if j < 7 then SuzC1EV.G j else decK (nt0Decs.getD (j - 7) ([], 0))

@[expose] noncomputable def kK (i : Nat) : Nat := cWK (kWords.getD i [])

@[expose] noncomputable def wK (G : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) Id (fun k _ ih => pc (G k) ih) w

@[expose] noncomputable def tzK (k : Nat) : Nat := if k = 0 then T1 else SuzC1BT 9

@[expose] noncomputable def e3xK : Nat := cWK e3Word

@[expose] noncomputable def e3K : Nat := pc (pc e3xK (cWK [1])) (SuzC1EI 0)

theorem kBT : allN 4 (fun j => Nat.beq (SuzC1ET.G j) (decK (t0Decs.getD j ([], 0)))) = true := by
  quickRfl

theorem kBV : allN 7 (fun j => Nat.beq (SuzC1EV.G j) (v0K j)) = true := by quickRfl

theorem kBA : (Nat.beq (SuzC1EA.G 0) W0 && Nat.beq (SuzC1EA.G 1) (SuzTwG 2)) = true := by
  quickRfl

theorem kBB : allN 7 (fun j => Nat.beq (SuzC1EB.G j) (b0K j) && ie (SuzC1EB.G j) (SuzC1EB.GI j) &&
    cn (SuzC1EB.GI j)) = true := by quickRfl

theorem kBN : allN 11 (fun j => Nat.beq (SuzC1EN.G j) (nt0K j) && ie (SuzC1EN.G j) (SuzC1EN.GI j) &&
    cn (SuzC1EN.GI j)) = true := by quickRfl

theorem kBE : (ie e3xK (SuzC1EI 0) && cn (SuzC1EI 0)) = true := by quickRfl

theorem kBR : (Nat.beq SuzC1EB.R W0 && Nat.beq SuzC1EN.R W0) = true := by quickRfl

theorem kSz : szOK 1782 11 = true := by quickRfl

theorem negBind : Bool.not (allN 4 (fun j =>
    Nat.beq (Nat.xor (SuzC1ET.G j) 2) (decK (t0Decs.getD j ([], 0))))) = true := by quickRfl

theorem negInv : Bool.not (ie (SuzC1EB.G 4) (Nat.xor (SuzC1EB.GI 4) 1)) = true := by quickRfl

theorem ofFn_get {α : Type} [Inhabited α] {n : Nat} (f : Nat → α) {i : Nat} (hi : i < n) :
    (Array.ofFn (n := n) fun j => f j.val)[i]! = f i := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem pqProd (v : Nat) : P (qProd v) (qProdK v) := by
  have key : ∀ l : List Nat, (∀ i ∈ l, i < 6) → ∀ r R, P r R →
      P (l.foldl (fun r i => if v.testBit i then compA 1782 r (qArr i) else r) r)
        (l.foldl (fun R i => if v.testBit i then pc R (KernelLC.SuzB0Q.F i) else R) R) := by
    intro l
    induction l with
    | nil => exact fun _ _ _ h => h
    | cons a l ih =>
      intro hl r R h
      rw [List.foldl_cons, List.foldl_cons]
      refine ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)) _ _ ?_
      by_cases hb : v.testBit a = true
      · simp only [hb, ↓reduceIte]
        exact p_comp h (pQ (hl a List.mem_cons_self))
      · simp only [hb, Bool.false_eq_true, ↓reduceIte]
        exact h
  exact key (List.range 6) (fun i hi => List.mem_range.1 hi) _ _ pId'

theorem pqE {j : Nat} (hj : j < 128) : P qElts[j]! (qEK j) := by
  have e : qElts[j]! = compA 1782 qProds[j / 2]! (tPow (j % 2)) := by
    unfold qElts
    rw [getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn]
  have e2 : qProds[j / 2]! = qProd (j / 2) := by
    unfold qProds
    rw [getElem!_pos _ (j / 2) (by simp only [Array.size_ofFn]; omega), Array.getElem_ofFn]
  rw [e, e2]
  unfold qEK tPow
  refine p_comp (pqProd _) ?_
  by_cases h : j % 2 = 1
  · simp only [h, beq_self_eq_true, ↓reduceIte]
    exact pt1
  · have hb : (j % 2 == 1) = false := by simpa using h
    simp only [hb, Bool.false_eq_true, ↓reduceIte]
    exact pId'

theorem pDec {d : List Nat × Nat} (hw : ∀ k ∈ d.1, k < 10) (hj : d.2 < 128) :
    P (decTab d) (decK d) :=
  pc' (cWord_P d.1 hw) (pqE hj)

theorem t0Decs_ok {i : Nat} (hi : i < 4) : (∀ k ∈ (t0Decs.getD i ([], 0)).1, k < 10) ∧
    (t0Decs.getD i ([], 0)).2 < 128 := by
  interval_cases i <;> decide

theorem nt0Decs_ok (i : Nat) : (∀ k ∈ (nt0Decs.getD i ([], 0)).1, k < 10) ∧
    (nt0Decs.getD i ([], 0)).2 < 128 := by
  rcases Nat.lt_or_ge i 4 with h | h
  · interval_cases i <;> decide
  · rw [List.getD_eq_default _ _ (by simp [nt0Decs]; omega)]
    decide

theorem ce3Decs_ok (i : Nat) : (∀ k ∈ (ce3Decs.getD i ([], 0)).1, k < 10) ∧
    (ce3Decs.getD i ([], 0)).2 < 128 := by
  rcases Nat.lt_or_ge i 2 with h | h
  · interval_cases i <;> decide
  · rw [List.getD_eq_default _ _ (by simp [ce3Decs]; omega)]
    decide

theorem kWords_ok (i : Nat) : ∀ k ∈ kWords.getD i [], k < 10 := by
  rcases Nat.lt_or_ge i 8 with h | h
  · interval_cases i <;> decide
  · rw [List.getD_eq_default _ _ (by simp [kWords]; omega)]
    decide

theorem and3 {a b c : Bool} (h : (a && b && c) = true) : a = true ∧ b = true ∧ c = true := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem and2 {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem bindB {j : Nat} (hj : j < 7) : Nat.beq (SuzC1EB.G j) (b0K j) = true ∧
    ie (SuzC1EB.G j) (SuzC1EB.GI j) = true ∧ cn (SuzC1EB.GI j) = true := and3 (allN_spec kBB j hj)

theorem bindN {j : Nat} (hj : j < 11) : Nat.beq (SuzC1EN.G j) (nt0K j) = true ∧
    ie (SuzC1EN.G j) (SuzC1EN.GI j) = true ∧ cn (SuzC1EN.GI j) = true := and3 (allN_spec kBN j hj)

theorem pT0 {i : Nat} (hi : i < 4) : P t0Tabs[i]! (SuzC1ET.G i) := by
  rw [show t0Tabs[i]! = t0Tab i from ofFn_get _ hi]
  exact p_eq (pDec (t0Decs_ok hi).1 (t0Decs_ok hi).2) (allN_spec kBT i hi)

theorem pV0 {j : Nat} (hj : j < 7) : P v0Tabs[j]! (SuzC1EV.G j) := by
  rw [show v0Tabs[j]! = v0Tab j from ofFn_get _ hj]
  refine p_eq ?_ (allN_spec kBV j hj)
  unfold v0Tab v0K
  split_ifs with h1 h2 h3
  · have := pT0 h1
    rwa [show t0Tabs[j]! = t0Tab j from ofFn_get _ h1] at this
  · exact pw0
  · exact pr1
  · exact ptau

theorem pB0 {j : Nat} (hj : j < 7) : P b0Tabs[j]! (SuzC1EB.G j) := by
  rw [show b0Tabs[j]! = b0Tab j from ofFn_get _ hj]
  refine p_eq ?_ (bindB hj).1
  unfold b0Tab b0K
  split_ifs with h1 h2 h3
  · have := pT0 h1
    rwa [show t0Tabs[j]! = t0Tab j from ofFn_get _ h1] at this
  · exact pw0
  · exact prho
  · exact ptau

theorem pNT0 {j : Nat} (hj : j < 11) : P nt0Tabs[j]! (SuzC1EN.G j) := by
  rw [show nt0Tabs[j]! = nt0Tab j from ofFn_get _ hj]
  refine p_eq ?_ (bindN hj).1
  unfold nt0Tab nt0K
  split_ifs with h1
  · have := pV0 h1
    rwa [show v0Tabs[j]! = v0Tab j from ofFn_get _ h1] at this
  · exact pDec (nt0Decs_ok _).1 (nt0Decs_ok _).2

theorem pCE3 (i : Nat) : P (ce3Tab i) (decK (ce3Decs.getD i ([], 0))) :=
  pDec (ce3Decs_ok i).1 (ce3Decs_ok i).2

theorem pK (i : Nat) : P (kTab i) (kK i) := cWord_P _ (kWords_ok i)

theorem map_get {α β : Type} [Inhabited α] [Inhabited β] {A : Array α} (f : α → β) {i : Nat}
    (hi : i < A.size) : (A.map f)[i]! = f A[i]! := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_map, getElem!_pos _ i hi]

theorem pB0I {j : Nat} (hj : j < 7) : P b0Invs[j]! (SuzC1EB.GI j) := by
  rw [show b0Invs[j]! = invTab 1782 b0Tabs[j]! from map_get _ (by simpa [b0Tabs] using hj)]
  exact (p_invR (pB0 hj) (bindB hj).2.1 (bindB hj).2.2).1

theorem pNT0I {j : Nat} (hj : j < 11) : P nt0Invs[j]! (SuzC1EN.GI j) := by
  rw [show nt0Invs[j]! = invTab 1782 nt0Tabs[j]! from map_get _ (by simpa [nt0Tabs] using hj)]
  exact (p_invR (pNT0 hj) (bindN hj).2.1 (bindN hj).2.2).1

theorem gT0 : GensOK 1782 11 4 SuzC1ET.G t0Tabs := ⟨by simp [t0Tabs], fun _ hj => pT0 hj⟩

theorem gV0 : GensOK 1782 11 7 SuzC1EV.G v0Tabs := ⟨by simp [v0Tabs], fun _ hj => pV0 hj⟩

theorem gA4 : GensOK 1782 11 2 SuzC1EA.G #[w0T, rhoT] := by
  refine ⟨rfl, fun j hj => ?_⟩
  interval_cases j
  · exact p_eq pw0 (and2 kBA).1
  · exact p_eq prho (and2 kBA).2

theorem gB0 : GensOK 1782 11 7 SuzC1EB.G b0Tabs := ⟨by simp [b0Tabs], fun _ hj => pB0 hj⟩

theorem gB0I : GensOK 1782 11 7 SuzC1EB.GI b0Invs :=
  ⟨by simp [b0Invs, b0Tabs], fun _ hj => pB0I hj⟩

theorem gNT0 : GensOK 1782 11 11 SuzC1EN.G nt0Tabs := ⟨by simp [nt0Tabs], fun _ hj => pNT0 hj⟩

theorem gNT0I : GensOK 1782 11 11 SuzC1EN.GI nt0Invs :=
  ⟨by simp [nt0Invs, nt0Tabs], fun _ hj => pNT0I hj⟩

theorem wP {gens : Array Tab} {G : Nat → Nat} (hg : ∀ k < gens.size, P gens[k]! (G k)) :
    ∀ w : List Nat, (∀ k ∈ w, k < gens.size) → P (wordTab 1782 gens w) (wK G w)
  | [], _ => pId'
  | k :: w, h => by
    unfold wordTab wK
    rw [List.foldr_cons]
    exact pc' (hg k (h k List.mem_cons_self)) (wP hg w fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem pTZ : ∀ k < (#[tTab, CFSG.Sporadic.SuzRecog.C1Model.zT] : Array Tab).size,
    P (#[tTab, CFSG.Sporadic.SuzRecog.C1Model.zT] : Array Tab)[k]! (tzK k) := by
  intro k hk
  have hk2 : k < 2 := by simpa using hk
  interval_cases k
  · exact pt1
  · exact pz

theorem t0ConjWords_ok (i : Nat) :
    ∀ k ∈ t0ConjWords.getD i [],
      k < (#[tTab, CFSG.Sporadic.SuzRecog.C1Model.zT] : Array Tab).size := by
  rcases Nat.lt_or_ge i 4 with h | h
  · interval_cases i <;> decide
  · rw [List.getD_eq_default _ _ (by simp [t0ConjWords]; omega)]
    decide

theorem pConj (i : Nat) : P (t0ConjTab i) (wK tzK (t0ConjWords.getD i [])) :=
  wP pTZ _ (t0ConjWords_ok i)

theorem pe3x : P e3xT e3xK := cWord_P _ (by decide)

theorem pe3xI : P e3xI (SuzC1EI 0) := (p_invR pe3x (and2 kBE).1 (and2 kBE).2).1

theorem pe3 : P e3T e3K := by
  unfold e3T conjTab e3K
  exact pc' (pc' pe3x (cWord_P [1] (by decide))) pe3xI

end CertificateChecks.KernelSpor.SuzC1EG

end
