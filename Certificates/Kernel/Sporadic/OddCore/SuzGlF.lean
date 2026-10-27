module

public import Certificates.Kernel.Sporadic.OddCore.SuzGlE
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzGl

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.PEnum
open CFSG.Sporadic.SuzRecog.B0Gluing CFSG.Sporadic.SuzRecog.B0GluingData
open CFSG.Sporadic.SuzRecog.C1Model CFSG.PSL3Four.Native
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.SuzTwCF
  CertificateChecks.KernelSpor.SuzMGF CertificateChecks.KernelSpor.SuzC1BF
  CertificateChecks.KernelSpor.SuzC1EG CertificateChecks.KernelSpor.SuzC1EF
  CertificateChecks.KernelSpor.SuzC1EV

local notation "pc" => pcomp 1782 11 (mask 11)
local notation "pgk" => pg 11 (mask 11)
local notation "g7" => pg 7 (mask 7)
local notation "g6" => pg 6 (mask 6)
local notation "qc" => pcomp 42 6 (mask 6)
local notation "qn" => canonK 42 6 (mask 6) (42 * 6)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)
local notation "ie" => invEqK 1782 11 (mask 11) (1782 * 11)
local notation "T" => SuzC1ET.T
local notation "Iq" => pidn 42 6
local notation "Id" => pidn 1782 11

theorem kRes : allN 64 (fun k => bAnd(qn (SuzGlR k),
    allN 42 fun i => Nat.beq (resK (T k) i) (g6 (SuzGlR k) i))) = true := by quickRfl

theorem kRInj : allN 64 (fun a => allN 64 fun b =>
    Bool.or (Nat.beq a b) (Bool.not (Nat.beq (SuzGlR a) (SuzGlR b)))) = true := by quickRfl

theorem kThT : allN 36 (fun i => bAnd(Nat.beq (SuzGlT i) (wq SuzC1BG (thetaWords.getD i [])),
    bAnd(qn (SuzGlT i), bAnd(invEqK 42 6 (mask 6) (42 * 6) (SuzGlT i) (SuzGlTI i),
      bAnd(qn (SuzGlTI i), Nat.beq (qc (SuzGlTI i) (SuzGlT i)) Iq))))) = true := by quickRfl

theorem kTh : allN 36 (fun i => allN 64 fun k => strictB (g7 (SuzGlP i) k) fun j =>
    bAnd(Nat.blt j 64, Nat.beq (qc (qc (SuzGlT i) (SuzGlR k)) (SuzGlTI i)) (SuzGlR j))) = true := by
  quickRfl

theorem kThI : allN 36 (fun i => allN 64 fun k =>
    Nat.beq (((List.range 64).find? fun x => thK i x == k).getD 0) (g7 (SuzGlPI i) k)) = true := by
  quickRfl

theorem kThPQ : allN 36 (fun i => allN 64 fun k =>
    bAnd(Nat.blt (thIK i k) 64, Nat.beq (thK i (thIK i k)) k)) = true := by quickRfl

theorem kN : (Nat.beq (SuzGlN 0) (wK tzK (witJ1.getD 0 [])) &&
    Nat.beq (SuzGlN 1) (wK tzK (witJ2.getD 0 [])) && Nat.beq (SuzGlN 2) (wK tzK (witJ1.getD 1 [])) &&
    Nat.beq (SuzGlN 3) (wK tzK (witJ2.getD 1 [])) &&
    allN 4 fun l => bAnd(ie (SuzGlN l) (SuzGlNI l), bAnd(cn (SuzGlNI l),
      Nat.beq (pc (SuzGlNI l) (SuzGlN l)) Id))) = true := by quickRfl

theorem kW : allN 2 (fun X => bAnd(Nat.beq (SuzGlW X) (decK (witC.getD X ([], 0))),
    bAnd(ie (SuzGlW X) (SuzGlWI X), bAnd(cn (SuzGlWI X), Nat.beq (pc (SuzGlWI X) (SuzGlW X)) Id))))
    = true := by quickRfl

theorem kRad : allN 2 (fun X => bAnd(Nat.beq (radPosK X).size 16,
    allN 16 fun i => Nat.blt (radK X i) 64)) = true := by quickRfl

theorem kFixW : allN 1782 (fun i => Bool.not (Bool.xor (Nat.beq (pgk (SuzTwG 6) i) i)
    (Nat.beq (pgk (SuzC1BT 11) i) i))) = true := by quickRfl

theorem negTh : Bool.not (allN 36 fun i => allN 64 fun k => strictB (g7 (SuzGlP i) k) fun j =>
    bAnd(Nat.blt j 64, Nat.beq (qc (qc (SuzGlT i) (SuzGlR k)) (SuzGlTI i))
      (if i = 7 then Nat.xor (SuzGlR j) 1 else SuzGlR j))) = true := by quickRfl

theorem allN42 {f : Nat → Bool} (h : allN 42 f = true) : ∀ i < 42, f i = true := allN_spec h

theorem resQ {X R : Nat} (h : allN 42 (fun i => Nat.beq (resK X i) (pg 6 (mask 6) R i)) = true)
    (hc : qn R = true) : Q (resTab (unpack 1782 11 X)) R := by
  refine ⟨?_, hc⟩
  apply Array.ext
  · simp [resTab, unpack]
  · intro i h1 _
    have hi : i < 42 := by simpa [resTab] using h1
    have hb := allN_spec kLab i hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    simp only [resTab, Array.getElem_ofFn, Fin.getElem!_fin]
    rw [← getElem!_pos (unpack 42 6 R) i (by rw [CFSG.KS.PEnum.unpack_size]; exact hi),
      unpack_getElem! hi, labArr_get, unpack_getElem! hb.1.1, labInv_get]
    exact Nat.eq_of_beq_eq_true (allN_spec h i hi)

theorem rtabs_size : rtabs.size = 64 := by simp [rtabs, ttabs_size']

theorem qR {k : Nat} (hk : k < 64) : Q rtabs[k]! (SuzGlR k) := by
  have h := (bAnd_iff _ _).1 (allN_spec kRes k hk)
  rw [show rtabs[k]! = resTab ttabs[k]! from map_get _ (by rw [ttabs_size']; exact hk),
    (pTT hk).1]
  exact resQ h.2 h.1

theorem thetaWords_lt' {i : Nat} (hi : i < 36) : ∀ k ∈ thetaWords.getD i [], k < gTabs.size := by
  interval_cases i <;> decide

theorem qTh {i : Nat} (hi : i < 36) : Q (thetaTab i) (SuzGlT i) := by
  have h := (bAnd_iff _ _).1 (allN_spec kThT i hi)
  have hq := wordQ (fun k hk => qG (by simpa [gTabs] using hk)) _ (thetaWords_lt' hi)
  rw [← Nat.eq_of_beq_eq_true h.1] at hq
  exact hq

theorem qThI {i : Nat} (hi : i < 36) : Q (thetaInvTab i) (SuzGlTI i) := by
  have h := (bAnd_iff _ _).1 (allN_spec kThT i hi)
  have h2 := (bAnd_iff _ _).1 h.2
  have h3 := (bAnd_iff _ _).1 h2.2
  have h4 := (bAnd_iff _ _).1 h3.2
  refine ⟨?_, h4.1⟩
  unfold thetaInvTab
  rw [(qTh hi).1]
  exact (invEqK_sound h3.1).1

theorem rtabs_inj : ∀ a < rtabs.size, ∀ b < rtabs.size, rtabs[a]! = rtabs[b]! → a = b := by
  intro a ha b hb e
  rw [rtabs_size] at ha hb
  rw [(qR ha).1, (qR hb).1] at e
  have h := allN_spec (allN_spec kRInj a ha) b hb
  have hbeq : Nat.beq (SuzGlR a) (SuzGlR b) = true := by
    rw [← CFSG.KS.PEnum.beq_unpack (qR ha).2 (qR hb).2, e]
    exact beq_self_eq_true _
  rw [hbeq] at h
  simpa using h

theorem th_eq (i k : Nat) : (thetaPerms[i]!)[k]! = thK i k := by
  unfold thetaPerms thK
  by_cases hi : i < 36
  · rw [ofFn_get' _ hi, blt_t hi]
    unfold thetaPerm
    by_cases hk : k < 64
    · rw [ofFn_get' _ hk, blt_t hk]
      have h := allN_spec (allN_spec kTh i hi) k hk
      rw [strictB_app'] at h
      obtain ⟨hj, he⟩ := (bAnd_iff _ _).1 h
      have hj' : g7 (SuzGlP i) k < 64 := Eq.mp Nat.blt_eq hj
      have hc : conjTab 42 (thetaTab i) (thetaInvTab i) rtabs[k]! = rtabs[g7 (SuzGlP i) k]! := by
        unfold conjTab
        rw [(qc' (qc' (qTh hi) (qR hk)) (qThI hi)).1, (qR hj').1, Nat.eq_of_beq_eq_true he]
      unfold posOf rIdx
      rw [hc]
      have := (CFSG.KS.BfsReplay.indexOf_spec rtabs_inj).1 _ (by rw [rtabs_size]; exact hj')
      exact this
    · rw [ofFn_neg' _ hk, blt_f hk]
      rfl
  · rw [ofFn_neg' _ hi, blt_f hi]
    rfl

theorem thI_eq (i k : Nat) : (thetaInvPerms[i]!)[k]! = thIK i k := by
  unfold thetaInvPerms thIK
  by_cases hi : i < 36
  · rw [map_get _ (by simp [thetaPerms]; exact hi), blt_t hi]
    unfold invPerm
    by_cases hk : k < 64
    · rw [ofFn_get' _ hk, blt_t hk]
      simp only [th_eq]
      exact Nat.eq_of_beq_eq_true (allN_spec (allN_spec kThI i hi) k hk)
    · rw [ofFn_neg' _ hk, blt_f hk]
      rfl
  · rw [getElem!_neg (thetaPerms.map invPerm) i (by simp [thetaPerms]; omega), blt_f hi]
    rfl

theorem nTabs_get {l : Nat} (hl : l < 4) : nTabs[l]! =
    jTab ([witJ1.getD 0 [], witJ2.getD 0 [], witJ1.getD 1 [], witJ2.getD 1 []].getD l []) := by
  interval_cases l <;> rfl

theorem pN {l : Nat} (hl : l < 4) : P nTabs[l]! (SuzGlN l) := by
  have h := kN
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, -⟩ := h
  rw [nTabs_get hl]
  unfold jTab
  have hw : ∀ w : List Nat, (∀ k ∈ w, k < 2) →
      P (wordTab 1782 #[CFSG.ComponentClassification.AS81.SuzB0.tTab,
        CFSG.Sporadic.SuzRecog.C1Model.zT] w) (wK tzK w) := fun w hw =>
    wP pTZ w (by simpa using hw)
  interval_cases l
  · exact p_eq (hw _ (by decide)) h0
  · exact p_eq (hw _ (by decide)) h1
  · exact p_eq (hw _ (by decide)) h2
  · exact p_eq (hw _ (by decide)) h3

theorem pNI {l : Nat} (hl : l < 4) : P nInvs[l]! (SuzGlNI l) := by
  have h := kN
  simp only [Bool.and_eq_true] at h
  have h' := (bAnd_iff _ _).1 (allN_spec h.2 l hl)
  rw [show nInvs[l]! = invTab 1782 nTabs[l]! from map_get _ (by simp [nTabs]; omega)]
  exact (p_invR (pN hl) h'.1 ((bAnd_iff _ _).1 h'.2).1).1

theorem witC_ok {X : Nat} (hX : X < 2) : (∀ k ∈ (witC.getD X ([], 0)).1, k < 10) ∧
    (witC.getD X ([], 0)).2 < 128 := by
  interval_cases X <;> decide

theorem pW {X : Nat} (hX : X < 2) : P cTabsW[X]! (SuzGlW X) := by
  have h := (bAnd_iff _ _).1 (allN_spec kW X hX)
  have e : cTabsW[X]! = decTab (witC.getD X ([], 0)) := by interval_cases X <;> rfl
  rw [e]
  exact p_eq (pDec (witC_ok hX).1 (witC_ok hX).2) h.1

theorem pWI {X : Nat} (hX : X < 2) : P cInvsW[X]! (SuzGlWI X) := by
  have h := (bAnd_iff _ _).1 (allN_spec kW X hX)
  have h2 := (bAnd_iff _ _).1 h.2
  rw [show cInvsW[X]! = invTab 1782 cTabsW[X]! from map_get _ (by simp [cTabsW]; omega)]
  exact (p_invR (pW hX) h2.1 ((bAnd_iff _ _).1 h2.2).1).1

theorem radPos_eq (X : Nat) : radPos X = radPosK X := by
  unfold radPos radPosK
  simp only [cmP_eq, gP_eq, oneI_eq]

theorem rads_eq : rads = #[radPosK 0, radPosK 1] := by
  unfold rads
  rw [radPos_eq, radPos_eq]

theorem rads_get {X : Nat} (hX : X < 2) : rads[X]! = radPosK X := by
  rw [rads_eq]
  interval_cases X <;> rfl

theorem radK_lt {X i : Nat} (hX : X < 2) (hi : i < 16) : radK X i < 64 :=
  Eq.mp Nat.blt_eq (allN_spec ((bAnd_iff _ _).1 (allN_spec kRad X hX)).2 i hi)

end CertificateChecks.KernelSpor.SuzGl

end
