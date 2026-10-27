module

public import Certificates.Kernel.Sporadic.OddCore.SuzTwC
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.Spor.PrimSound
public import CFSG.Certificates.Kernel.Spor.Loops
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelSpor.SuzTwCF

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.LevelTwoData
open CFSG.Sporadic.SuzRecog.ModelGroupsCheck CFSG.Sporadic.SuzRecog.B0TwistData
open CFSG.Sporadic.SuzRecog.B0TwistCheck
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore

@[expose] noncomputable def letK (G GI : Nat → Nat) (c : Nat) : Nat :=
  nIf(Nat.beq (Nat.mod c 2) 0, G (Nat.div c 2), GI (Nat.div c 2))

@[expose] noncomputable def wordK (G GI : Nat → Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn 1782 11)
    (fun c _ ih => pcomp 1782 11 (mask 11) (letK G GI c) ih) w

@[expose] noncomputable def relsOKK (G GI : Nat → Nat) (ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => bAnd(Nat.beq (wordK G GI w) (pidn 1782 11), ih)) ws

@[expose] noncomputable def gT (i : Nat) : Nat := nIf(Nat.beq i 5, SuzTwG 7, SuzTwG i)

@[expose] noncomputable def gTI (i : Nat) : Nat := nIf(Nat.beq i 5, SuzTwGI 7, SuzTwGI i)

theorem gBind : bAnd(Nat.beq (SuzTwG 0) (SuzTwH1.F 0), bAnd(Nat.beq (SuzTwG 1) (SuzTwH2.F 0),
    bAnd(Nat.beq (SuzTwG 2) (SuzTwRho.F 0), bAnd(Nat.beq (SuzTwG 3) (SuzTwA.F 0),
    bAnd(Nat.beq (SuzTwG 4) (SuzTwB.F 0), bAnd(Nat.beq (SuzTwG 5) (SuzTwTau.F 0),
    bAnd(Nat.beq (SuzTwG 6) (SuzTwW0.F 0),
      Nat.beq (SuzTwG 7) (pcomp 1782 11 (mask 11) (SuzTwG 5) (SuzTP 1))))))))) = true := by
  quickRfl

theorem gCan : allN 8 (fun i => bAnd(canonK 1782 11 (mask 11) (1782 * 11) (SuzTwG i),
    canonK 1782 11 (mask 11) (1782 * 11) (SuzTwGI i))) = true := by
  quickRfl

theorem gInv : allN 8 (fun i => invEqK 1782 11 (mask 11) (1782 * 11) (SuzTwG i) (SuzTwGI i)) =
    true := by
  quickRfl

theorem canP : canonK 1782 11 (mask 11) (1782 * 11) (pidn 1782 11) = true := by quickRfl

theorem mem : bAnd(OddCore.msift (SuzTwG 0), bAnd(OddCore.msift (SuzTwG 1),
    bAnd(OddCore.msift (SuzTwG 3), bAnd(OddCore.msift (SuzTwG 4), OddCore.msift (SuzTwG 5))))) =
    true := by
  quickRfl

theorem kC : relsOKK SuzTwG SuzTwGI relsC = true := by quickRfl

theorem kN : relsOKK SuzTwG SuzTwGI relsN = true := by quickRfl

theorem kT : relsOKK gT gTI (relsT ++ [relX]) = true := by quickRfl

theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

@[expose] def P (a : Array Nat) (A : Nat) : Prop :=
  a = unpack 1782 11 A ∧ canonK 1782 11 (mask 11) (1782 * 11) A = true

theorem p_comp {a b : Array Nat} {A B : Nat} (ha : P a A) (hb : P b B) :
    P (compA 1782 a b) (pcomp 1782 11 (mask 11) A B) := by
  rw [ha.1, hb.1]
  exact ⟨compA_unpack ha.2 hb.2, canonK_pcomp ha.2 hb.2⟩

theorem eqA_P {a b : Array Nat} {A B : Nat} (ha : P a A) (hb : P b B) :
    eqA 1782 a b = Nat.beq A B := by
  rw [ha.1, hb.1]
  exact eqA_unpack ha.2 hb.2

theorem commA_P {a b : Array Nat} {A B : Nat} (ha : P a A) (hb : P b B) :
    commA a b = Nat.beq (pcomp 1782 11 (mask 11) A B) (pcomp 1782 11 (mask 11) B A) := by
  unfold commA
  exact eqA_P (p_comp ha hb) (p_comp hb ha)

theorem gC {i : Nat} (hi : i < 8) : canonK 1782 11 (mask 11) (1782 * 11) (SuzTwG i) = true :=
  ((bAnd_iff _ _).1 (allN_spec gCan i hi)).1

theorem gIC {i : Nat} (hi : i < 8) : canonK 1782 11 (mask 11) (1782 * 11) (SuzTwGI i) = true :=
  ((bAnd_iff _ _).1 (allN_spec gCan i hi)).2

theorem p_inv {a : Array Nat} {i : Nat} (hi : i < 8) (ha : a = unpack 1782 11 (SuzTwG i)) :
    P (invCand 1782 a) (SuzTwGI i) ∧ isInvA 1782 a (invCand 1782 a) = true := by
  have h := invEqK_sound (allN_spec gInv i hi)
  rw [ha, h.1]
  exact ⟨⟨rfl, gIC hi⟩, h.2⟩

theorem p_conj {g a : Array Nat} {i : Nat} {A : Nat} (hi : i < 8) (hg : P g (SuzTwG i))
    (ha : P a A) :
    P (conjA g a) (pcomp 1782 11 (mask 11) (SuzTwG i)
      (pcomp 1782 11 (mask 11) A (SuzTwGI i))) := by
  unfold conjA
  exact p_comp hg (p_comp ha (p_inv hi hg.1).1)

theorem pidn_P : P (idA 1782) (pidn 1782 11) := ⟨(idK_sound (by quickRfl)).symm, canP⟩

theorem hex_eq {cs : List Char} {s : String} {F : Nat → Nat} (hs : s = String.ofList cs)
    (h : CFSG.KC.Misc.HexFlat.hexFlat cs 3 1782 11 1 F = true) :
    hexTable 3 1782 0 s = unpack 1782 11 (F 0) := by
  have h' := CFSG.KC.Misc.HexFlat.hexTable_sound h 0 (by norm_num)
  rw [Nat.mul_zero, ← hs] at h'
  exact h'

theorem gB {i : Nat} {F : Nat → Nat} (hi : i < 8)
    (hF : Nat.beq (SuzTwG i) (F 0) = true) {a : Array Nat} (ha : a = unpack 1782 11 (F 0)) :
    P a (SuzTwG i) := by
  rw [ha, ← Nat.eq_of_beq_eq_true hF]
  exact ⟨rfl, gC hi⟩

theorem binds : Nat.beq (SuzTwG 0) (SuzTwH1.F 0) = true ∧ Nat.beq (SuzTwG 1) (SuzTwH2.F 0) = true ∧
    Nat.beq (SuzTwG 2) (SuzTwRho.F 0) = true ∧ Nat.beq (SuzTwG 3) (SuzTwA.F 0) = true ∧
    Nat.beq (SuzTwG 4) (SuzTwB.F 0) = true ∧ Nat.beq (SuzTwG 5) (SuzTwTau.F 0) = true ∧
    Nat.beq (SuzTwG 6) (SuzTwW0.F 0) = true ∧
    Nat.beq (SuzTwG 7) (pcomp 1782 11 (mask 11) (SuzTwG 5) (SuzTP 1)) = true := by
  simpa only [bAnd_iff] using gBind

theorem pH1 : P h1Arr (SuzTwG 0) := gB (by norm_num) binds.1 (hex_eq SuzTwH1.eq SuzTwH1.all)
theorem pH2 : P h2Arr (SuzTwG 1) := gB (by norm_num) binds.2.1 (hex_eq SuzTwH2.eq SuzTwH2.all)
theorem pRho : P rhoArr (SuzTwG 2) :=
  gB (by norm_num) binds.2.2.1 (hex_eq SuzTwRho.eq SuzTwRho.all)
theorem pA : P aArr (SuzTwG 3) := gB (by norm_num) binds.2.2.2.1 (hex_eq SuzTwA.eq SuzTwA.all)
theorem pB : P bArr (SuzTwG 4) := gB (by norm_num) binds.2.2.2.2.1 (hex_eq SuzTwB.eq SuzTwB.all)
theorem pTau : P tauArr (SuzTwG 5) :=
  gB (by norm_num) binds.2.2.2.2.2.1 (hex_eq SuzTwTau.eq SuzTwTau.all)
theorem pW0 : P w0Arr (SuzTwG 6) :=
  gB (by norm_num) binds.2.2.2.2.2.2.1 (hex_eq SuzTwW0.eq SuzTwW0.all)

theorem pT1 : P t1A (SuzTP 1) :=
  ⟨(rep_facts (i := 1) (by norm_num)).1, (rep_facts (i := 1) (by norm_num)).2.1⟩

theorem pTT : P (compA 1782 tauArr t1A) (SuzTwG 7) := by
  rw [Nat.eq_of_beq_eq_true binds.2.2.2.2.2.2.2]
  exact p_comp pTau pT1

theorem pW1 : P w1A (pcomp 1782 11 (mask 11) (SuzTwG 2)
    (pcomp 1782 11 (mask 11) (SuzTwG 6) (SuzTwGI 2))) := by
  unfold w1A
  exact p_conj (by norm_num) pRho pW0

theorem pW2 : P w2A (pcomp 1782 11 (mask 11) (SuzTwG 6) (pcomp 1782 11 (mask 11) (SuzTwG 2)
    (pcomp 1782 11 (mask 11) (SuzTwG 6) (SuzTwGI 2)))) := by
  unfold w2A
  exact p_comp pW0 pW1

theorem gens_P : ∀ i < 7, P twGens[i]! (SuzTwG i) := by
  intro i hi
  interval_cases i <;>
    simp only [twGens, List.getElem!_toArray, List.getElem!_cons_zero, List.getElem!_cons_succ]
  exacts [pH1, pH2, pRho, pA, pB, pTau, pW0]

theorem gensT_P : ∀ i < 7, P twGensT[i]! (gT i) := by
  intro i hi
  interval_cases i <;>
    simp only [twGensT, List.getElem!_toArray, List.getElem!_cons_zero,
      List.getElem!_cons_succ]
  exacts [pH1, pH2, pRho, pA, pB, pTT, pW0]

theorem gensI_P : ∀ i < 7, P (invCand 1782 twGens[i]!) (SuzTwGI i) :=
  fun i hi => (p_inv (by omega) (gens_P i hi).1).1

theorem gensTI_P : ∀ i < 7, P (invCand 1782 twGensT[i]!) (gTI i) := by
  intro i hi
  by_cases h5 : i = 5
  · subst h5
    simp only [twGensT, List.getElem!_toArray, List.getElem!_cons_zero, List.getElem!_cons_succ]
    exact (p_inv (i := 7) (by norm_num) pTT.1).1
  · have e : gT i = SuzTwG i := by
      unfold gT
      rw [beq_false h5]
    have e' : gTI i = SuzTwGI i := by
      unfold gTI
      rw [beq_false h5]
    have hg := gensT_P i hi
    rw [e] at hg
    rw [e']
    exact (p_inv (by omega) hg.1).1

theorem word_P {S : Array (Array Nat)} {G GI : Nat → Nat} (hS : ∀ i < 7, P S[i]! (G i))
    (hSI : ∀ i < 7, P (invCand 1782 S[i]!) (GI i)) :
    ∀ w : List Nat, (∀ c ∈ w, c < 14) → P (twWordA S w) (wordK G GI w) := by
  intro w
  induction w with
  | nil => intro _; exact pidn_P
  | cons c w ih =>
    intro hw
    have hc := hw c List.mem_cons_self
    have hl : P (twCodeA S c) (letK G GI c) := by
      unfold twCodeA letK
      rcases Nat.mod_two_eq_zero_or_one c with h | h
      · have hb : Nat.beq (Nat.mod c 2) 0 = true := by
          change Nat.beq (c % 2) 0 = true
          rw [h]
          rfl
        simp only [h, ↓reduceIte]
        rw [hb]
        exact hS (c / 2) (by omega)
      · have hb : Nat.beq (Nat.mod c 2) 0 = false := by
          change Nat.beq (c % 2) 0 = false
          rw [h]
          rfl
        simp only [h, Nat.one_ne_zero, ↓reduceIte]
        rw [hb]
        exact hSI (c / 2) (by omega)
    exact p_comp hl (ih fun y hy => hw y (List.mem_cons_of_mem _ hy))

theorem all_eq {S : Array (Array Nat)} {G GI : Nat → Nat} (hS : ∀ i < 7, P S[i]! (G i))
    (hSI : ∀ i < 7, P (invCand 1782 S[i]!) (GI i)) :
    ∀ ws : List (List Nat), (∀ w ∈ ws, ∀ c ∈ w, c < 14) →
      ws.all (fun w => eqA 1782 (twWordA S w) (idA 1782)) = relsOKK G GI ws := by
  intro ws
  induction ws with
  | nil => intro _; rfl
  | cons w ws ih =>
    intro hw
    rw [List.all_cons, eqA_P (word_P hS hSI w (hw w List.mem_cons_self)) pidn_P,
      ih fun v hv => hw v (List.mem_cons_of_mem _ hv)]
    rfl

theorem relsOKK_append (G GI : Nat → Nat) (a b : List (List Nat)) :
    relsOKK G GI (a ++ b) = (relsOKK G GI a && relsOKK G GI b) := by
  induction a with
  | nil => rfl
  | cons w a ih =>
    change bAnd(Nat.beq (wordK G GI w) (pidn 1782 11), relsOKK G GI (a ++ b)) =
      (bAnd(Nat.beq (wordK G GI w) (pidn 1782 11), relsOKK G GI a) && relsOKK G GI b)
    rw [ih]
    cases Nat.beq (wordK G GI w) (pidn 1782 11) <;> rfl

theorem perms : twPermsOK = true := by
  unfold twPermsOK CFSG.Sporadic.SuzRecog.ModelGroupsCheck.permOK
  rw [(p_inv (by norm_num) pH1.1).2, (p_inv (by norm_num) pH2.1).2, (p_inv (by norm_num) pA.1).2,
    (p_inv (by norm_num) pB.1).2, (p_inv (by norm_num) pTau.1).2]
  rfl

theorem members : twMembersOK = true := by
  have hm := mem
  simp only [bAnd_iff] at hm
  unfold twMembersOK
  rw [inM_eq pH1.1 pH1.2, inM_eq pH2.1 pH2.2, inM_eq pA.1 pA.2, inM_eq pB.1 pB.2,
    inM_eq pTau.1 pTau.2, hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2]
  rfl

theorem comm : twCommOK = true := by
  unfold twCommOK
  rw [commA_P pH1 pRho, commA_P pH1 pT1, commA_P pH2 pRho, commA_P pH2 pT1, commA_P pA pRho,
    commA_P pA pW0, commA_P pA pW1, commA_P pB pRho, commA_P pB pW0, commA_P pB pW1,
    commA_P pTau pT1]
  quickRfl

theorem rhoPow_P : P (twRhoPowA 0) (pidn 1782 11) ∧
    P (twRhoPowA 1) (pcomp 1782 11 (mask 11) (SuzTwG 2) (pidn 1782 11)) ∧
    P (twRhoPowA 2) (pcomp 1782 11 (mask 11) (SuzTwG 2)
      (pcomp 1782 11 (mask 11) (SuzTwG 2) (pidn 1782 11))) :=
  ⟨pidn_P, p_comp pRho pidn_P, p_comp pRho (p_comp pRho pidn_P)⟩

theorem tau : twTauOK = true := by
  unfold twTauOK normR0 inR0 twEvenAt
  rw [eqA_P (p_conj (by norm_num) pTau pW0) pW0, eqA_P (p_conj (by norm_num) pTau pW0) pW1,
    eqA_P (p_conj (by norm_num) pTau pW0) pW2, eqA_P (p_conj (by norm_num) pTau pW1) pW0,
    eqA_P (p_conj (by norm_num) pTau pW1) pW1, eqA_P (p_conj (by norm_num) pTau pW1) pW2,
    eqA_P (p_conj (by norm_num) pTau pRho) (p_inv (by norm_num) pRho.1).1,
    commA_P (p_comp pTau rhoPow_P.1) pW0, commA_P (p_comp pTau rhoPow_P.1) pW1,
    commA_P (p_comp pTau rhoPow_P.2.1) pW0, commA_P (p_comp pTau rhoPow_P.2.1) pW1,
    commA_P (p_comp pTau rhoPow_P.2.2) pW0, commA_P (p_comp pTau rhoPow_P.2.2) pW1]
  quickRfl

theorem rels : twRelsOK = true := by
  unfold twRelsOK
  rw [all_eq gens_P gensI_P _ (by decide), all_eq gensT_P gensTI_P _ (by decide),
    relsOKK_append, kC, kN, kT]
  rfl

end CertificateChecks.KernelSpor.SuzTwCF

end
