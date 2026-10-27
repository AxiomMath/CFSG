module

public import Certificates.Kernel.Sporadic.OddCore.SuzMcK
public import Certificates.Kernel.Sporadic.OddCore.SuzRTF
public import Certificates.Kernel.Sporadic.OddCore.SuzC1EV
public import Certificates.Kernel.Sporadic.L2.G5
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzMcF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore
open CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.MixedCellData CFSG.Sporadic.SuzRecog.MixedCell
open CFSG.Sporadic.SuzRecog.MixedCellCheck CFSG.Sporadic.SuzRecog.LevelTwoData
open CFSG.Sporadic.SuzRecog.B0TwistData
open CFSG.Sporadic.SuzRecog.ModelGroupsCheck (conjA t1A commA permOK tauA w1A w2A normR0 inR0)
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore
open CertificateChecks.KernelSpor.SuzTwCF (P p_comp eqA_P pidn_P commA_P)

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "ie" => invEqK 1782 11 (mask 11) (1782 * 11)
local notation "Idn" => pidn 1782 11

theorem getD_lt {α : Type} {l : List α} {i : Nat} (d : α) (hi : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem getD_mem {α : Type} {l : List α} {i : Nat} (d : α) (hi : i < l.length) :
    l.getD i d ∈ l := by
  rw [getD_lt d hi]
  exact List.getElem_mem hi

theorem all_of_get {α : Type} {l : List α} (d : α) {f : α → Bool}
    (h : ∀ i < l.length, f (l.getD i d) = true) : l.all f = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := h i hi
  rwa [getD_lt d hi] at this

theorem wget_eq (D : List (List Nat)) (i : Nat) : SuzMcK.wget D i = D.getD i [] := by
  induction D generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem pget_eq (D : List (List Nat × List Nat)) (i : Nat) : SuzMcK.pget D i = D.getD i ([], []) := by
  induction D generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i

theorem blk {b len : Nat} {f : Nat → Bool} (h : allBlk b f len = true) {i : Nat} (h1 : b ≤ i)
    (h2 : i < b + len) : f i = true := by
  have h' := allBlk_spec h (i - b) (by omega)
  have e : Nat.add b (i - b) = i := by
    change b + (i - b) = i
    omega
  rwa [e] at h'

theorem or_of_all {α : Type} {l : List α} {f : α → Bool} {x : α} (hx : x ∈ l)
    (h : f x = false) (b : Bool) : (!l.all f || b) = true := by
  have : l.all f = false := by
    rw [List.all_eq_false]
    exact ⟨x, hx, by rw [h]; exact Bool.false_ne_true⟩
  rw [this]
  rfl

theorem or_of_any {α : Type} {l : List α} {f : α → Bool} {x : α} (hx : x ∈ l)
    (h : f x = true) (a : Bool) : (a || l.any f) = true := by
  have : l.any f = true := List.any_eq_true.2 ⟨x, hx, h⟩
  rw [this, Bool.or_true]

theorem or_true_of {b : Bool} (h : b = true) (a : Bool) : (a || b) = true := by
  rw [h, Bool.or_true]

theorem p_eq {a : Array Nat} {A B : Nat} (ha : P a A) (h : Nat.beq B A = true) : P a B := by
  rw [Nat.eq_of_beq_eq_true h]
  exact ha

theorem p_eq' {a : Array Nat} {A B : Nat} (ha : P a A) (h : Nat.beq A B = true) : P a B := by
  rw [← Nat.eq_of_beq_eq_true h]
  exact ha

theorem eqA_false {t u : Array Nat} {x : Nat} (hx : x < 1782) (h : t[x]! ≠ u[x]!) :
    eqA 1782 t u = false := by
  rw [Bool.eq_false_iff]
  intro he
  have := (CFSG.Monster.B.Co2.allLt_iff.1 he) x hx
  rw [beq_iff_eq] at this
  exact h this

theorem comm_false {T G x : Nat} (hT : cn T = true) (hG : cn G = true) (hx : x < 1782)
    (h : SuzRKZ.movK T G x = true) : commA (unpack 1782 11 T) (unpack 1782 11 G) = false := by
  unfold commA
  refine eqA_false hx ?_
  rw [CFSG.Monster.B.Co2.compA_get hx, CFSG.Monster.B.Co2.compA_get hx,
    unpack_get hx, unpack_get hx, unpack_get (canon_lt hG hx), unpack_get (canon_lt hT hx)]
  unfold SuzRKZ.movK at h
  intro e
  rw [e, Nat.beq_refl] at h
  exact Bool.false_ne_true h

theorem bnd : Nat.beq (SuzMcG 0) (SuzTwG 0) = true ∧ Nat.beq (SuzMcG 1) (SuzTwG 1) = true ∧
    Nat.beq (SuzMcG 2) (SuzTwG 2) = true ∧ Nat.beq (SuzMcG 3) (SuzTwG 3) = true ∧
    Nat.beq (SuzMcG 4) (SuzTwG 4) = true ∧ Nat.beq (SuzMcG 5) (L2EL.F 12) = true ∧
    Nat.beq (SuzMcG 6) (SuzMGG 4) = true ∧ Nat.beq (SuzMcG 7) (SuzTwG 6) = true ∧
    Nat.beq (SuzMcGI 0) (SuzTwGI 0) = true ∧ Nat.beq (SuzMcGI 1) (SuzTwGI 1) = true ∧
    Nat.beq (SuzMcGI 2) (SuzTwGI 2) = true ∧ Nat.beq (SuzMcGI 3) (SuzTwGI 3) = true ∧
    Nat.beq (SuzMcGI 4) (SuzTwGI 4) = true ∧ Nat.beq (SuzMcGI 5) (L2EI 12) = true ∧
    Nat.beq (SuzMcGI 6) (SuzMGGI 4) = true ∧ Nat.beq (SuzMcGI 7) (SuzTwGI 6) = true := by
  have h := SuzMcK.kBind
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, i0⟩, i1⟩, i2⟩, i3⟩, i4⟩, i5⟩, i6⟩,
    i7⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, i0, i1, i2, i3, i4, i5, i6, i7⟩

theorem tw_inv {a : Array Nat} {i : Nat} (hi : i < 8) (ha : P a (SuzTwG i)) :
    P (invCand 1782 a) (SuzTwGI i) := (SuzTwCF.p_inv hi ha.1).1

theorem pS : P sA (SuzMcK.S) := p_eq (L2G.eltP (k := 12) (by norm_num)).1 bnd.2.2.2.2.2.1

theorem pSI : P (invCand 1782 sA) (SuzMcK.SI) :=
  p_eq (L2G.eltP (k := 12) (by norm_num)).2.1 bnd.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem pTau : P tauA (SuzMcK.TAU) := p_eq SuzMGF.pTauM bnd.2.2.2.2.2.2.1

theorem pTauI : P (invCand 1782 tauA) (SuzMcGI 6) :=
  p_eq (SuzMGF.pGI_of (by norm_num) SuzMGF.pTauM).1 bnd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem pG : ∀ i < 8, P mcGens[i]! (SuzMcG i) := by
  intro i hi
  interval_cases i <;>
    simp only [mcGens, List.getElem!_toArray, List.getElem!_cons_zero, List.getElem!_cons_succ]
  · exact p_eq SuzTwCF.pH1 bnd.1
  · exact p_eq SuzTwCF.pH2 bnd.2.1
  · exact p_eq SuzTwCF.pRho bnd.2.2.1
  · exact p_eq SuzTwCF.pA bnd.2.2.2.1
  · exact p_eq SuzTwCF.pB bnd.2.2.2.2.1
  · exact pS
  · exact pTau
  · exact p_eq SuzTwCF.pW0 bnd.2.2.2.2.2.2.2.1

theorem pGI : ∀ i < 8, P (invCand 1782 mcGens[i]!) (SuzMcGI i) := by
  intro i hi
  interval_cases i <;>
    simp only [mcGens, List.getElem!_toArray, List.getElem!_cons_zero, List.getElem!_cons_succ]
  · exact p_eq (tw_inv (by norm_num) SuzTwCF.pH1) bnd.2.2.2.2.2.2.2.2.1
  · exact p_eq (tw_inv (by norm_num) SuzTwCF.pH2) bnd.2.2.2.2.2.2.2.2.2.1
  · exact p_eq (tw_inv (by norm_num) SuzTwCF.pRho) bnd.2.2.2.2.2.2.2.2.2.2.1
  · exact p_eq (tw_inv (by norm_num) SuzTwCF.pA) bnd.2.2.2.2.2.2.2.2.2.2.2.1
  · exact p_eq (tw_inv (by norm_num) SuzTwCF.pB) bnd.2.2.2.2.2.2.2.2.2.2.2.2.1
  · exact pSI
  · exact pTauI
  · exact p_eq (tw_inv (by norm_num) SuzTwCF.pW0) bnd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem word_P : ∀ w : List Nat, (∀ c ∈ w, c < 16) → P (mcWordA w) (SuzMcK.wK w) := by
  intro w
  induction w with
  | nil => intro _; exact pidn_P
  | cons c w ih =>
    intro hw
    have hc := hw c List.mem_cons_self
    have hl : P (mcCodeA c) (SuzTwCF.letK SuzMcG SuzMcGI c) := by
      unfold mcCodeA SuzTwCF.letK
      rcases Nat.mod_two_eq_zero_or_one c with h | h
      · have hb : Nat.beq (Nat.mod c 2) 0 = true := by
          change Nat.beq (c % 2) 0 = true
          rw [h]
          rfl
        simp only [h, ↓reduceIte]
        rw [hb]
        exact pG (c / 2) (by omega)
      · have hb : Nat.beq (Nat.mod c 2) 0 = false := by
          change Nat.beq (c % 2) 0 = false
          rw [h]
          rfl
        simp only [h, Nat.one_ne_zero, ↓reduceIte]
        rw [hb]
        exact pGI (c / 2) (by omega)
    exact p_comp hl (ih fun y hy => hw y (List.mem_cons_of_mem _ hy))

theorem pT1 : P t1A SuzMcK.T1 := SuzTwCF.pT1

theorem pW0 : P w0Arr SuzMcK.W0 := SuzTwCF.pW0

theorem pP1 : P p1A SuzMcK.P1 := SuzRTF.pAP

theorem pinParts : Nat.beq SuzMcK.W1 (pc SuzMcK.RHO (pc SuzMcK.W0 (SuzTwGI 2))) = true ∧
    Nat.beq SuzMcK.W2 (pc SuzMcK.W0 SuzMcK.W1) = true ∧
    Nat.beq (SuzMcE 0) (pc (SuzMcK.CI 0) (pc SuzMcK.S (SuzMcK.CP 0))) = true ∧
    Nat.beq (SuzMcE 2) (pc (SuzMcK.CI 2) (pc SuzMcK.S (SuzMcK.CP 2))) = true ∧
    ie (SuzMcE 0) (SuzMcEI 0) = true ∧ ie (SuzMcE 2) (SuzMcEI 2) = true ∧
    cn (SuzMcEI 0) = true ∧ cn (SuzMcEI 2) = true ∧
    Nat.beq SuzMcK.X (SuzMcK.wK xW) = true ∧ ie SuzMcK.X SuzMcK.XI = true ∧
    cn SuzMcK.XI = true := by
  have h := SuzMcK.kPin
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem pW1 : P w1A SuzMcK.W1 := p_eq SuzTwCF.pW1 pinParts.1

theorem pW2 : P w2A SuzMcK.W2 := by
  unfold w2A
  exact p_eq (p_comp pW0 pW1) pinParts.2.1

theorem pC {k : Nat} (hk : k = 0 ∨ k = 2) : P (cA k) (SuzMcK.C k) := by
  rcases hk with rfl | rfl
  · exact (L2G.eltP (k := 13) (by norm_num)).1
  · exact (L2G.eltP (k := 15) (by norm_num)).1

theorem pCI {k : Nat} (hk : k = 0 ∨ k = 2) : P (invCand 1782 (cA k)) (SuzMcK.CI k) := by
  rcases hk with rfl | rfl
  · exact (L2G.eltP (k := 13) (by norm_num)).2.1
  · exact (L2G.eltP (k := 15) (by norm_num)).2.1

theorem pCP {k : Nat} (hk : k = 0 ∨ k = 2) : P (cpA k) (SuzMcK.CP k) := by
  rcases hk with rfl | rfl
  · exact (L2G.eltP (k := 17) (by norm_num)).1
  · exact (L2G.eltP (k := 19) (by norm_num)).1

theorem pCPI {k : Nat} (hk : k = 0 ∨ k = 2) : P (invCand 1782 (cpA k)) (SuzMcK.CPI k) := by
  rcases hk with rfl | rfl
  · exact (L2G.eltP (k := 17) (by norm_num)).2.1
  · exact (L2G.eltP (k := 19) (by norm_num)).2.1

theorem pE {k : Nat} (hk : k = 0 ∨ k = 2) : P (eA k) (SuzMcE k) := by
  have h : P (eA k) (pc (SuzMcK.CI k) (pc SuzMcK.S (SuzMcK.CP k))) := by
    unfold eA
    exact p_comp (pCI hk) (p_comp pS (pCP hk))
  rcases hk with rfl | rfl
  · exact p_eq h pinParts.2.2.1
  · exact p_eq h pinParts.2.2.2.1

theorem pEI {k : Nat} (hk : k = 0 ∨ k = 2) : P (invCand 1782 (eA k)) (SuzMcEI k) := by
  rcases hk with rfl | rfl
  · exact (SuzMGF.p_invR (pE (Or.inl rfl)) pinParts.2.2.2.2.1 pinParts.2.2.2.2.2.2.1).1
  · exact (SuzMGF.p_invR (pE (Or.inr rfl)) pinParts.2.2.2.2.2.1 pinParts.2.2.2.2.2.2.2.1).1

theorem pWA : P wA (pc SuzMcK.T1 SuzMcK.P1) := p_comp pT1 pP1

theorem codesX : ∀ c ∈ xW, c < 16 := by decide +kernel

theorem pX : P (mcWordA xW) SuzMcK.X := p_eq (word_P xW codesX) pinParts.2.2.2.2.2.2.2.2.1

theorem pXI : P (invCand 1782 (mcWordA xW)) SuzMcK.XI :=
  (SuzMGF.p_invR pX pinParts.2.2.2.2.2.2.2.2.2.1 pinParts.2.2.2.2.2.2.2.2.2.2).1

theorem conj_P {g a : Array Nat} {G GI A : Nat} (hg : P g G) (hgi : P (invCand 1782 g) GI)
    (ha : P a A) : P (conjA g a) (pc G (pc A GI)) := p_comp hg (p_comp ha hgi)

theorem conjInv_P {g a : Array Nat} {G GI A : Nat} (hg : P g G) (hgi : P (invCand 1782 g) GI)
    (ha : P a A) : P (conjInvA g a) (pc GI (pc A G)) := p_comp hgi (p_comp ha hg)

theorem inR0_P {x : Array Nat} {X : Nat} (hx : P x X) : inR0 x = SuzMcK.inR0K X := by
  unfold inR0 SuzMcK.inR0K
  rw [eqA_P hx pW0, eqA_P hx pW1, eqA_P hx pW2]

theorem normR0_P {g : Array Nat} {G GI : Nat} (hg : P g G) (hgi : P (invCand 1782 g) GI) :
    normR0 g = SuzMcK.nR0K G GI := by
  unfold normR0 SuzMcK.nR0K
  rw [inR0_P (conj_P hg hgi pW0), inR0_P (conj_P hg hgi pW1)]

theorem permElt {k : Nat} (hk : k < 21) : permOK (CFSG.Sporadic.SuzRecog.LevelTwo.eltPin k).1 =
    true := by
  have h := (L2G.eltP hk).2.2
  unfold CFSG.Sporadic.SuzRecog.LevelTwo.elemOK at h
  rw [Bool.and_eq_true] at h
  exact h.1

theorem permTw {a : Array Nat} {i : Nat} (hi : i < 8) (ha : P a (SuzTwG i)) : permOK a = true :=
  SuzRTF.permOK_of ha.1 (allN_spec SuzTwCF.gInv i hi)

theorem perms : mcPermsOK = true := by
  have hA := (L2G.aVt_parts (SuzRTF.hvA 342 (by norm_num))).2.2.2
  have e1 : permOK p1A = true := SuzRTF.permOK_of pP1.1 hA
  have e2 : permOK sA = true := permElt (k := 12) (by norm_num)
  have e3 : permOK (cA 0) = true := permElt (k := 13) (by norm_num)
  have e4 : permOK (cpA 0) = true := permElt (k := 17) (by norm_num)
  have e5 : permOK (cA 2) = true := permElt (k := 15) (by norm_num)
  have e6 : permOK (cpA 2) = true := permElt (k := 19) (by norm_num)
  unfold mcPermsOK
  rw [permTw (by norm_num) SuzTwCF.pH1, permTw (by norm_num) SuzTwCF.pH2,
    permTw (by norm_num) SuzTwCF.pA, permTw (by norm_num) SuzTwCF.pB, e1, e2, e3, e4, e5, e6]
  rfl

theorem members : mcMembersOK = true := by
  have hm := SuzTwCF.mem
  simp only [bAnd_iff] at hm
  unfold mcMembersOK
  rw [inM_eq SuzTwCF.pH1.1 SuzTwCF.pH1.2, inM_eq SuzTwCF.pH2.1 SuzTwCF.pH2.2,
    inM_eq SuzTwCF.pA.1 SuzTwCF.pA.2, inM_eq SuzTwCF.pB.1 SuzTwCF.pB.2, hm.1, hm.2.1, hm.2.2.1,
    hm.2.2.2.1]
  rfl

theorem letters : mcLettersOK = true := by quickRfl

theorem comm : mcCommOK = true := by
  have h := SuzMcK.kComm
  unfold SuzMcK.cmK SuzMcK.T1 SuzMcK.RHO at h
  unfold mcCommOK
  rw [commA_P SuzTwCF.pH1 SuzTwCF.pT1, commA_P SuzTwCF.pH1 SuzTwCF.pRho,
    commA_P SuzTwCF.pH2 SuzTwCF.pT1, commA_P SuzTwCF.pH2 SuzTwCF.pRho,
    commA_P SuzTwCF.pA SuzTwCF.pRho, normR0_P SuzTwCF.pA (tw_inv (by norm_num) SuzTwCF.pA),
    commA_P SuzTwCF.pB SuzTwCF.pRho, normR0_P SuzTwCF.pB (tw_inv (by norm_num) SuzTwCF.pB)]
  exact h

theorem codesH1 : ∀ w ∈ relsH1, ∀ c ∈ w, c < 16 := by decide +kernel
theorem codesH2 : ∀ w ∈ relsH2, ∀ c ∈ w, c < 16 := by decide +kernel
theorem codesA : ∀ p ∈ relsA, (∀ c ∈ p.1, c < 16) ∧ ∀ c ∈ p.2, c < 16 := by decide +kernel
theorem codesE : ∀ p ∈ edge, (∀ c ∈ p.1, c < 16) ∧ ∀ c ∈ p.2, c < 16 := by decide +kernel
theorem codesSq : ∀ c ∈ sq, c < 16 := by decide +kernel

theorem idWords {ws : List (List Nat)} (hc : ∀ w ∈ ws, ∀ c ∈ w, c < 16)
    (h : ∀ i < ws.length, Nat.beq (SuzMcK.wK (SuzMcK.wget ws i)) Idn = true) :
    ws.all (fun w => eqA 1782 (mcWordA w) (idA 1782)) = true := by
  refine all_of_get [] fun i hi => ?_
  have h' := h i hi
  rw [wget_eq] at h'
  try dsimp only
  rw [eqA_P (word_P _ (hc _ (getD_mem [] hi))) pidn_P]
  exact h'

theorem relsH1_ok : ∀ i < relsH1.length, SuzMcK.rH1 i = true := by
  intro i hi
  have hl : relsH1.length = 7 := rfl
  rcases (by omega : i < 3 ∨ (3 ≤ i ∧ i < 6) ∨ i = 6) with h | h | h
  · exact blk SuzMcK.kH1a (by omega) (by omega)
  · exact blk SuzMcK.kH1b (by omega) (by omega)
  · subst h
    have := SuzMcK.kH1c
    rw [Bool.and_eq_true] at this
    exact this.1

theorem relsH2_ok : ∀ i < relsH2.length, SuzMcK.rH2 i = true := by
  intro i hi
  have hl : relsH2.length = 8 := rfl
  rcases (by omega : i < 5 ∨ (5 ≤ i ∧ i < 8)) with h | h
  · exact blk SuzMcK.kH2a (by omega) (by omega)
  · exact blk SuzMcK.kH2b (by omega) (by omega)

theorem relsA_ok : ∀ i < relsA.length, SuzMcK.rA i = true := by
  intro i hi
  have hl : relsA.length = 8 := rfl
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [SuzMcK.kA0, SuzMcK.kA1, SuzMcK.kA2, SuzMcK.kA3, SuzMcK.kA4, SuzMcK.kA5, SuzMcK.kA6,
    SuzMcK.kA7]

theorem edge_ok : ∀ i < edge.length, SuzMcK.rE i = true := by
  intro i hi
  have hl : edge.length = 5 := rfl
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
  exacts [SuzMcK.kE0, SuzMcK.kE1, SuzMcK.kE2, SuzMcK.kE3, SuzMcK.kE4]

theorem rels : mcRelsOK = true := by
  unfold mcRelsOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_append, Bool.and_eq_true]
    refine ⟨idWords codesH1 fun i hi => ?_, idWords codesH2 fun i hi => ?_⟩
    · have h := relsH1_ok i hi
      unfold SuzMcK.rH1 at h
      exact h
    · have h := relsH2_ok i hi
      unfold SuzMcK.rH2 at h
      exact h
  · refine all_of_get ([], []) fun i hi => ?_
    have hc := codesA _ (getD_mem ([], []) hi)
    have h := relsA_ok i hi
    unfold SuzMcK.rA at h
    rw [pget_eq] at h
    try dsimp only
    rw [eqA_P (word_P _ hc.1) (word_P _ hc.2)]
    exact h
  · refine all_of_get ([], []) fun i hi => ?_
    have hc := codesE _ (getD_mem ([], []) hi)
    have h := edge_ok i hi
    unfold SuzMcK.rE at h
    rw [strictB_eq, pget_eq] at h
    have hu := word_P _ hc.1
    try dsimp only
    rw [commA_P hu pP1, eqA_P (word_P _ hc.2) (conj_P pS pSI hu)]
    unfold SuzMcK.cmK at h
    exact h
  · have h := SuzMcK.kH1c
    rw [Bool.and_eq_true] at h
    rw [eqA_P (word_P sq codesSq) (p_comp pS pS)]
    exact h.2

theorem codesCell : (∀ c ∈ cW0, c < 16) ∧ (∀ c ∈ cpW0, c < 16) ∧ (∀ c ∈ eW0, c < 16) ∧
    (∀ c ∈ cW2, c < 16) ∧ (∀ c ∈ cpW2, c < 16) ∧ (∀ c ∈ eW2, c < 16) ∧
    (∀ c ∈ kGenAW, c < 16) ∧ (∀ c ∈ kGenBW, c < 16) := by
  decide +kernel

theorem codesD0 : ∀ w ∈ deltaW0, ∀ c ∈ w, c < 16 := by decide +kernel
theorem codesD2 : ∀ w ∈ deltaW2, ∀ c ∈ w, c < 16 := by decide +kernel
theorem codesB0 : ∀ w ∈ boundW0, ∀ c ∈ w, c < 16 := by decide +kernel
theorem codesB2 : ∀ w ∈ boundW2, ∀ c ∈ w, c < 16 := by decide +kernel

theorem deltaW_eq0 : deltaW 0 = deltaW0 := rfl
theorem deltaW_eq2 : deltaW 2 = deltaW2 := rfl
theorem boundW_eq0 : boundW 0 = boundW0 := rfl
theorem boundW_eq2 : boundW 2 = boundW2 := rfl

theorem pinD_of {dw : List (List Nat)} {k : Nat} (hc : ∀ w ∈ dw, ∀ c ∈ w, c < 16)
    (hl : dw.length = 16) (ha : allBlk 0 (SuzMcK.pinD dw k) 6 = true)
    (hb : allBlk 6 (SuzMcK.pinD dw k) 5 = true) (hc' : allBlk 11 (SuzMcK.pinD dw k) 5 = true) :
    ∀ i < 16, P (mcWordA (dw.getD i [])) (SuzMcK.D k i) := by
  intro i hi
  have h : SuzMcK.pinD dw k i = true := by
    rcases (by omega : i < 6 ∨ (6 ≤ i ∧ i < 11) ∨ (11 ≤ i ∧ i < 16)) with h | h | h
    · exact blk ha (by omega) (by omega)
    · exact blk hb (by omega) (by omega)
    · exact blk hc' (by omega) (by omega)
  unfold SuzMcK.pinD at h
  rw [wget_eq] at h
  exact p_eq' (word_P _ (hc _ (getD_mem [] (by omega)))) h

theorem pD0 : ∀ i < 16, P (mcWordA (deltaW0.getD i [])) (SuzMcK.D 0 i) :=
  pinD_of codesD0 rfl SuzMcK.kD0a SuzMcK.kD0b SuzMcK.kD0c

theorem pD2 : ∀ i < 16, P (mcWordA (deltaW2.getD i [])) (SuzMcK.D 2 i) :=
  pinD_of codesD2 rfl SuzMcK.kD2a SuzMcK.kD2b SuzMcK.kD2c

theorem cell_of {k : Nat} (hk : k = 0 ∨ k = 2) {cw cpw ew : List Nat} {dw : List (List Nat)}
    (hcw : cW k = cw) (hcpw : cpW k = cpw) (hew : eW k = ew) (hdw : deltaW k = dw)
    (c1 : ∀ c ∈ cw, c < 16) (c2 : ∀ c ∈ cpw, c < 16) (c3 : ∀ c ∈ ew, c < 16)
    (pd : P (mcWordA (dw.getD 1 [])) (SuzMcK.D k 1))
    (h : (Nat.beq (SuzMcK.wK cw) (SuzMcK.C k) && Nat.beq (SuzMcK.wK cpw) (SuzMcK.CP k) &&
      Nat.beq (SuzMcK.wK ew) (SuzMcE k) && Nat.beq (SuzMcK.D k 1) (pc SuzMcK.T1 SuzMcK.P1)) =
      true) :
    eqA 1782 (mcWordA (cW k)) (cA k) = true ∧ eqA 1782 (mcWordA (cpW k)) (cpA k) = true ∧
      eqA 1782 (mcWordA (eW k)) (eA k) = true ∧
      eqA 1782 (mcWordA ((deltaW k).getD 1 [])) wA = true := by
  rw [hcw, hcpw, hew, hdw, eqA_P (word_P cw c1) (pC hk), eqA_P (word_P cpw c2) (pCP hk),
    eqA_P (word_P ew c3) (pE hk), eqA_P pd pWA]
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem cells : mcCellsOK = true := by
  have hg := SuzMcK.kGen
  simp only [Bool.and_eq_true] at hg
  obtain ⟨⟨⟨g1, g2⟩, g3⟩, g4⟩ := hg
  have c := codesCell
  obtain ⟨a1, a2, a3, a4⟩ := cell_of (Or.inl rfl) rfl rfl rfl rfl c.1 c.2.1 c.2.2.1
    (pD0 1 (by norm_num)) SuzMcK.kCell0
  obtain ⟨b1, b2, b3, b4⟩ := cell_of (Or.inr rfl) rfl rfl rfl rfl c.2.2.2.1 c.2.2.2.2.1
    c.2.2.2.2.2.1 (pD2 1 (by norm_num)) SuzMcK.kCell2
  have a0 : decide ((deltaW 0).getD 0 [0] = []) = true := by decide
  have b0 : decide ((deltaW 2).getD 0 [0] = []) = true := by decide
  have d1 : eqA 1782 (mcWordA kGenAW) RootTwistData.kGenAArr = true := by
    rw [eqA_P (word_P _ c.2.2.2.2.2.2.1) SuzRTF.pKA]
    exact g1
  have d2 : eqA 1782 (mcWordA kGenBW) RootTwistData.kGenBArr = true := by
    rw [eqA_P (word_P _ c.2.2.2.2.2.2.2) SuzRTF.pKB]
    exact g2
  have d3 : eqA 1782 (conjA sA t1A) p1A = true := by
    rw [eqA_P (conj_P pS pSI pT1) pP1]
    exact g3
  have d4 : eqA 1782 (conjA sA p1A) t1A = true := by
    rw [eqA_P (conj_P pS pSI pP1) pT1]
    exact g4
  unfold mcCellsOK
  simp only [List.all_cons, List.all_nil, Bool.and_true, a1, a2, a3, a4, b1, b2, b3, b4, a0, b0,
    d1, d2, d3, d4]

theorem pinM_of {bw : List (List Nat)} {k : Nat} (hk : k = 0 ∨ k = 2)
    (hc : ∀ w ∈ bw, ∀ c ∈ w, c < 16) {j : Nat} (hj : j < bw.length)
    (h : SuzMcK.pinM bw k j = true) :
    P (mcWordA (bw.getD j [])) (SuzMcK.M k j) ∧
      P (conjInvA (cpA k) (mcWordA (bw.getD j []))) (SuzMcK.Y k j) ∧
      P (invCand 1782 (conjInvA (cpA k) (mcWordA (bw.getD j [])))) (SuzMcK.YI k j) := by
  unfold SuzMcK.pinM at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [wget_eq] at h1
  have pm := p_eq' (word_P _ (hc _ (getD_mem [] hj))) h1
  have py := p_eq (conjInv_P (pCP hk) (pCPI hk) pm) h2
  exact ⟨pm, py, (SuzMGF.p_invR py h3 h4).1⟩

theorem bound_of {k nk : Nat} (hk : k = 0 ∨ k = 2) {bw dw : List (List Nat)}
    (hb : boundW k = bw) (hd : deltaW k = dw) (hbl : bw.length = nk) (hdl : dw.length = 16)
    (h0 : bw.getD 0 [] = [4]) (hn1 : 1 < nk)
    (pm : ∀ j < nk, P (mcWordA (bw.getD j [])) (SuzMcK.M k j) ∧
      P (conjInvA (cpA k) (mcWordA (bw.getD j []))) (SuzMcK.Y k j) ∧
      P (invCand 1782 (conjInvA (cpA k) (mcWordA (bw.getD j [])))) (SuzMcK.YI k j))
    (pd : ∀ i < 16, P (mcWordA (dw.getD i [])) (SuzMcK.D k i))
    (hM1 : Nat.beq (SuzMcK.M k 1) SuzMcK.T1 = true)
    (hchk : ∀ j < nk, SuzMcK.chkM k j = true)
    (hscan : allN 3456 (SuzMcK.kwK SuzMcKW k nk) = true) :
    mcBoundOK k = true := by
  unfold mcBoundOK
  dsimp only
  rw [hb, hd]
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨decide_eq_true h0, ?_⟩, ?_⟩, ?_⟩
  · rw [eqA_P (pm 1 hn1).1 pT1]
    exact hM1
  · rw [List.all_map]
    refine all_of_get [] fun j hj => ?_
    rw [hbl] at hj
    obtain ⟨p1, p2, p3⟩ := pm j hj
    have h := hchk j hj
    unfold SuzMcK.chkM SuzMcK.cmK at h
    simp only [Function.comp_apply]
    rw [commA_P p1 pP1, normR0_P p2 p3, commA_P (conj_P (pE hk) (pEI hk) p2) pT1,
      commA_P (conj_P pS pSI p1) pT1]
    unfold SuzMcK.nR0K
    simp only [Bool.and_eq_true] at h ⊢
    exact ⟨⟨⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2⟩, h.1.2⟩, h.2⟩
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro i hi
    have h := allN_spec hscan i hi
    unfold SuzMcK.kwK at h
    simp only [strictB_eq] at h
    generalize SuzMcKW (Nat.add (Nat.mul 1728 k) i) = w at h
    rw [SuzRKF.kEls_get hi]
    cases hw : Nat.beq (Nat.mod w 2) 1
    · simp only [hw] at h
      obtain ⟨hj, h⟩ := (bAnd_iff _ _).1 h
      obtain ⟨hx, h⟩ := (bAnd_iff _ _).1 h
      have hj' : Nat.mod (Nat.div w 2) 8 < nk := Nat.le_of_ble_eq_true hj
      have hx' : Nat.div w 16 < 1782 := Nat.le_of_ble_eq_true hx
      have p1 := (pm _ hj').1
      have hf := comm_false (SuzRKZF.canT hi) p1.2 hx' h
      rw [← p1.1] at hf
      exact or_of_all (List.mem_map_of_mem (getD_mem (i := Nat.mod (Nat.div w 2) 8) []
        (by omega))) hf _
    · simp only [hw] at h
      obtain ⟨hd16, h⟩ := (bAnd_iff _ _).1 h
      have hd' : Nat.div w 2 < 16 := Nat.le_of_ble_eq_true hd16
      have e := Nat.eq_of_beq_eq_true h
      have hq : eqA 1782 (unpack 1782 11 (SuzRKT i)) (mcWordA (dw.getD (Nat.div w 2) [])) =
          true := by
        rw [(pd _ hd').1, e]
        exact SuzRKF.eqA_self _
      exact or_of_any (List.mem_map_of_mem (getD_mem (i := Nat.div w 2) [] (by omega))) hq _

theorem chk_of {k nk : Nat} (ha : allBlk 0 (SuzMcK.chkM k) 3 = true)
    (hb : allBlk 3 (SuzMcK.chkM k) (nk - 3) = true) (hnk : 3 ≤ nk) :
    ∀ j < nk, SuzMcK.chkM k j = true := by
  intro j hj
  rcases (by omega : j < 3 ∨ 3 ≤ j) with h | h
  · exact blk ha (by omega) (by omega)
  · exact blk hb h (by omega)

theorem pinM_all {bw : List (List Nat)} {k nk : Nat} (hk : k = 0 ∨ k = 2)
    (hc : ∀ w ∈ bw, ∀ c ∈ w, c < 16) (hl : bw.length = nk) (hnk : 3 ≤ nk)
    (ha : allBlk 0 (SuzMcK.pinM bw k) 3 = true) (hb : allBlk 3 (SuzMcK.pinM bw k) (nk - 3) = true) :
    ∀ j < nk, P (mcWordA (bw.getD j [])) (SuzMcK.M k j) ∧
      P (conjInvA (cpA k) (mcWordA (bw.getD j []))) (SuzMcK.Y k j) ∧
      P (invCand 1782 (conjInvA (cpA k) (mcWordA (bw.getD j [])))) (SuzMcK.YI k j) := by
  intro j hj
  refine pinM_of hk hc (by omega) ?_
  rcases (by omega : j < 3 ∨ 3 ≤ j) with h | h
  · exact blk ha (by omega) (by omega)
  · exact blk hb h (by omega)

theorem bound0 : mcBoundOK 0 = true := by
  have hm := SuzMcK.kM1
  rw [Bool.and_eq_true] at hm
  exact bound_of (nk := 5) (Or.inl rfl) boundW_eq0 deltaW_eq0 rfl rfl rfl (by norm_num)
    (pinM_all (Or.inl rfl) codesB0 rfl (by norm_num) SuzMcK.kM0a SuzMcK.kM0b) pD0 hm.1
    (chk_of SuzMcK.kB0a SuzMcK.kB0b (by norm_num)) SuzMcK.kScan0

theorem bound2 : mcBoundOK 2 = true := by
  have hm := SuzMcK.kM1
  rw [Bool.and_eq_true] at hm
  exact bound_of (nk := 6) (Or.inr rfl) boundW_eq2 deltaW_eq2 rfl rfl rfl (by norm_num)
    (pinM_all (Or.inr rfl) codesB2 rfl (by norm_num) SuzMcK.kM2a SuzMcK.kM2b) pD2 hm.2
    (chk_of SuzMcK.kB2a SuzMcK.kB2b (by norm_num)) SuzMcK.kScan2

theorem vc_all : ∀ p < 520, SuzMcK.vcK p = true := by
  intro p hp
  have hs : ∀ s < 26, allBlk (20 * s) SuzMcK.vcK 20 = true := by
    intro s hs
    interval_cases s
    exacts [SuzMcK.kVC0, SuzMcK.kVC1, SuzMcK.kVC2, SuzMcK.kVC3, SuzMcK.kVC4, SuzMcK.kVC5,
      SuzMcK.kVC6, SuzMcK.kVC7, SuzMcK.kVC8, SuzMcK.kVC9, SuzMcK.kVC10, SuzMcK.kVC11,
      SuzMcK.kVC12, SuzMcK.kVC13, SuzMcK.kVC14, SuzMcK.kVC15, SuzMcK.kVC16, SuzMcK.kVC17,
      SuzMcK.kVC18, SuzMcK.kVC19, SuzMcK.kVC20, SuzMcK.kVC21, SuzMcK.kVC22, SuzMcK.kVC23,
      SuzMcK.kVC24, SuzMcK.kVC25]
  exact blk (hs (p / 20) (by omega)) (by omega) (by omega)

theorem v0_ok {v : Nat} (hv : v < 512) :
    (!commA C1Model.v0Enum.tabs[v]! w1A || commA C1Model.v0Enum.tabs[v]! (mcWordA xW)) = true := by
  have hP := SuzC1EV.pVk hv
  have h := allN_spec SuzMcK.kV v hv
  unfold SuzMcK.vwK at h
  simp only [strictB_eq] at h
  generalize SuzMcVW v = w at h
  cases hw : Nat.beq (Nat.mod w 2) 1
  · simp only [hw] at h
    obtain ⟨hp, h⟩ := (bAnd_iff _ _).1 h
    have hp' : Nat.div w 2 < SuzMcN 0 := Nat.le_of_ble_eq_true hp
    have hN : SuzMcN 0 ≤ 520 := Nat.le_of_ble_eq_true SuzMcK.kVN
    have hc := vc_all _ (by omega : Nat.div w 2 < 520)
    unfold SuzMcK.vcK at hc
    simp only [hp, Nat.eq_of_beq_eq_true h] at hc
    unfold SuzMcK.cmK at hc
    rw [commA_P hP pX]
    exact or_true_of hc _
  · simp only [hw] at h
    obtain ⟨hx, h⟩ := (bAnd_iff _ _).1 h
    have hx' : Nat.div w 2 < 1782 := Nat.le_of_ble_eq_true hx
    have hf := comm_false (SuzC1EV.canV hv) pW1.2 hx' h
    rw [← hP.1, ← pW1.1] at hf
    simp only [hf, Bool.not_false, Bool.true_or]

theorem bad_of (k n : Nat) (hk : k = 0 ∨ k = 2) {u : Array Nat} {U : Nat} (hu : P u U)
    (pd : P (mcWordA ((deltaW k).getD n [])) (SuzMcK.D k n))
    (h : (Nat.beq (pc (pc SuzMcK.SI (pc (pc (SuzMcK.C k) (pc SuzMcK.X (SuzMcK.CI k))) SuzMcK.S))
        (pc (SuzMcK.D k n) (pc (SuzMcK.CP k) (pc SuzMcK.X (SuzMcK.CPI k))))) U &&
      SuzMcK.cmK (pc (SuzMcK.C k) (pc SuzMcK.X (SuzMcK.CI k))) SuzMcK.P1 &&
      SuzMcK.cmK (pc SuzMcK.SI (pc (pc (SuzMcK.C k) (pc SuzMcK.X (SuzMcK.CI k))) SuzMcK.S))
        SuzMcK.T1) = true) :
    eqA 1782 (compA 1782 (conjInvA sA (conjA (cA k) (mcWordA xW)))
        (compA 1782 (mcWordA ((deltaW k).getD n [])) (conjA (cpA k) (mcWordA xW)))) u = true ∧
      commA (conjA (cA k) (mcWordA xW)) p1A = true ∧
      commA (conjInvA sA (conjA (cA k) (mcWordA xW))) t1A = true := by
  have pa := conj_P (pC hk) (pCI hk) pX
  have pb := conj_P (pCP hk) (pCPI hk) pX
  have pa' := conjInv_P pS pSI pa
  rw [eqA_P (p_comp pa' (p_comp pd pb)) hu, commA_P pa pP1, commA_P pa' pT1]
  unfold SuzMcK.cmK at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem badD (k n u : Nat) (h : SuzMcK.badK k n u = true) :
    (Nat.beq (pc (pc SuzMcK.SI (pc (pc (SuzMcK.C k) (pc SuzMcK.X (SuzMcK.CI k))) SuzMcK.S))
        (pc (SuzMcK.D k n) (pc (SuzMcK.CP k) (pc SuzMcK.X (SuzMcK.CPI k)))))
        (nIf(Nat.beq u 0, Idn, pc SuzMcK.T1 SuzMcK.P1)) &&
      SuzMcK.cmK (pc (SuzMcK.C k) (pc SuzMcK.X (SuzMcK.CI k))) SuzMcK.P1 &&
      SuzMcK.cmK (pc SuzMcK.SI (pc (pc (SuzMcK.C k) (pc SuzMcK.X (SuzMcK.CI k))) SuzMcK.S))
        SuzMcK.T1) = true := by
  unfold SuzMcK.badK at h
  simp only [strictB_eq] at h
  exact h

theorem remark : mcRemarkOK = true := by
  have hr := SuzMcK.kRem
  unfold SuzMcK.cmK at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨⟨r1, r2⟩, r3⟩, r4⟩ := hr
  have b0 := SuzMcK.kBad0
  have b1 := SuzMcK.kBad1
  rw [Bool.and_eq_true] at b0 b1
  obtain ⟨e1, e2, e3⟩ := bad_of 0 15 (Or.inl rfl) pidn_P (pD0 15 (by norm_num)) (badD 0 15 0 b0.1)
  obtain ⟨f1, f2, f3⟩ := bad_of 2 7 (Or.inr rfl) pidn_P (pD2 7 (by norm_num)) (badD 2 7 0 b0.2)
  have g1 := (bad_of 0 8 (Or.inl rfl) pWA (pD0 8 (by norm_num)) (badD 0 8 1 b1.1)).1
  have h1 := (bad_of 2 8 (Or.inr rfl) pWA (pD2 8 (by norm_num)) (badD 2 8 1 b1.2)).1
  have q1 : commA (mcWordA xW) w0Arr = true := by
    rw [commA_P pX pW0]
    exact r1
  have q2 : commA (mcWordA xW) w1A = true := by
    rw [commA_P pX pW1]
    exact r2
  have q3 : eqA 1782 (conjA (mcWordA xW) tauA) (compA 1782 tauA t1A) = true := by
    rw [eqA_P (conj_P pX pXI pTau) (p_comp pTau pT1)]
    exact r3
  have q4 : eqA 1782 (compA 1782 (mcWordA xW) (mcWordA xW)) (idA 1782) = true := by
    rw [eqA_P (p_comp pX pX) pidn_P]
    exact r4
  have q5 : C1Model.v0Enum.tabs.all (fun v => !commA v w1A || commA v (mcWordA xW)) = true := by
    rw [Array.all_eq_true]
    intro v hv
    have e := getElem!_pos C1Model.v0Enum.tabs v hv
    rw [← e]
    exact v0_ok (by rwa [SuzC1EV.v0_size] at hv)
  have hb : badPairs = [(15, 7, 0), (8, 8, 1)] := rfl
  unfold mcRemarkOK
  dsimp only
  rw [hb]
  simp only [List.all_cons, List.all_nil, Bool.and_true, ↓reduceIte, Nat.one_ne_zero, q1, q2, q3,
    q4, q5, e1, e2, e3, f1, f2, f3, g1, h1]

end CertificateChecks.KernelSpor.SuzMcF

end
