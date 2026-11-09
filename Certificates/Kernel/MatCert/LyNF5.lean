module

public import Certificates.Kernel.MatCert.LyNF
public import Certificates.Kernel.SporSch.Ly.SevA
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.LyFiveInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMC.LyNF5

open CFSG.KC.OpsMN CFSG.KC.OpsK CFSG.KC.Ord CFSG.KD.OrdLy CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native CFSG.AGLEmbedding.R3
open CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.LyBS
open CertificateChecks.KernelSporSch.LySv
open CertificateChecks.KernelMC.LyNF (OL src)
open CFSG.KS.SporSch.LyM (wordR letterR)

local notation "mulL" => mulR 5 12 1332 111 8 L H CM RM

@[expose] def isStepT (t : Nat) : Op → Bool
  | .mul i j k => i == t && k == t && j != t
  | .pow _ _ _ => false

@[expose] def isChainT (t : Nat) : List Op → Bool
  | .pow 1 _ k :: tl => k == t && tl.all (isStepT t)
  | _ => false

@[expose] def rho (l : Int) : Nat :=
  if l = 1 ∨ l = -1 then 0 else if l = 2 then 1 else if l = -2 then 4
  else if 0 < l then 2 * l.natAbs - 1 else 2 * l.natAbs

@[expose] def pre3 : List Op := lyFiveProg.take 3

@[expose] def D0 : List Op := lyFiveProg.drop 3
@[expose] def s5 : List Op := D0.take 76
@[expose] def D1 : List Op := D0.drop 76
@[expose] def p6 : List Op := D1.take 1
@[expose] def D2 : List Op := D1.drop 1
@[expose] def s7 : List Op := D2.take 104
@[expose] def D3 : List Op := D2.drop 104
@[expose] def p8 : List Op := D3.take 1
@[expose] def D4 : List Op := D3.drop 1
@[expose] def s9 : List Op := D4.take 127
@[expose] def D5 : List Op := D4.drop 127
@[expose] def p10 : List Op := D5.take 1
@[expose] def D6 : List Op := D5.drop 1
@[expose] def s11 : List Op := D6.take 140
@[expose] def D7 : List Op := D6.drop 140
@[expose] def p12 : List Op := D7.take 1
@[expose] def D8 : List Op := D7.drop 1
@[expose] def s13 : List Op := D8.take 152

@[expose] def rest5 : List Op := D8.drop 152

theorem prog_eq5 : lyFiveProg = pre3 ++ (s5 ++ (p6 ++ (s7 ++ (p8 ++ (s9 ++ (p10 ++ (s11 ++
    (p12 ++ (s13 ++ rest5))))))))) := by
  unfold pre3 s5 p6 s7 p8 s9 p10 s11 p12 s13 rest5 D8 D7 D6 D5 D4 D3 D2 D1 D0
  simp only [List.take_append_drop]

theorem pows_eq : p6 = [.pow 30 5 6] ∧ p8 = [.pow 20 7 8] ∧ p10 = [.pow 7 9 10] ∧
    p12 = [.pow 2 11 12] := ⟨rfl, rfl, rfl, rfl⟩

theorem chains_ok5 : (isChainT 5 s5 && isChainT 7 s7 && isChainT 9 s9 && isChainT 11 s11 &&
    isChainT 13 s13) = true := by decide

theorem maps_ok : s5.map src = SW2.map rho ∧ s7.map src = SW3.map rho ∧
    s9.map src = SW4.map rho ∧ s11.map src = SW5.map rho ∧ s13.map src = SW6.map rho := by
  decide

@[expose] noncomputable def S0 : List Nat := pre3.foldl (stepL OL) (initN OL A B lyFiveN)

@[expose] noncomputable def U1 : List Nat := (S0.set 5 (AF 2)).set 6 (AI 2)
@[expose] noncomputable def U2 : List Nat := (U1.set 7 (AF 3)).set 8 (AI 3)
@[expose] noncomputable def U3 : List Nat := (U2.set 9 (AF 4)).set 10 (AI 4)
@[expose] noncomputable def U4 : List Nat := (U3.set 11 (AF 5)).set 12 (AI 5)

@[expose] noncomputable def init5 : List Nat := U4.set 13 (AF 6)

@[expose] noncomputable def lettersIn (R : List Nat) (j : Nat) (W : List Int) : Bool :=
  W.all (fun l => Nat.beq (getN R (rho l)) (letterR (AFx j) (AIx j) l)) &&
    Nat.beq (mulL ONE (letterR (AFx j) (AIx j) (W.headD 0))) (letterR (AFx j) (AIx j) (W.headD 0))

theorem lt2 : lettersIn S0 2 SW2 = true := by quickRfl
theorem lt3 : lettersIn U1 3 SW3 = true := by quickRfl
theorem lt4 : lettersIn U2 4 SW4 = true := by quickRfl
theorem lt5 : lettersIn U3 5 SW5 = true := by quickRfl
theorem lt6 : lettersIn U4 6 SW6 = true := by quickRfl

theorem pw2 : Nat.beq (OL.pow (AF 2) 30) (AI 2) = true := by quickRfl
theorem pw3 : Nat.beq (OL.pow (AF 3) 20) (AI 3) = true := by quickRfl
theorem pw4 : Nat.beq (OL.pow (AF 4) 7) (AI 4) = true := by quickRfl
theorem pw5 : Nat.beq (OL.pow (AF 5) 2) (AI 5) = true := by quickRfl

theorem and_of {a b : Bool} (h : Bool.rec (motive := fun _ => Bool) false b a = true) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all

theorem chain_foldT {t : Nat} : ∀ (xs : List Op) (R : List Nat) (X : Nat),
    t < R.length → xs.all (isStepT t) = true →
    xs.foldl (stepL OL) (R.set t X) = R.set t ((xs.map (fun op => getN R (src op))).foldl mulL X)
  | [], _, _, _, _ => rfl
  | op :: xs, R, X, ht, h => by
    rw [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases op with
    | mul i j k =>
      simp only [isStepT, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h1
      obtain ⟨⟨hi, hk⟩, hj⟩ := h1
      subst hi hk
      rw [List.foldl_cons, LyNF.step_eq ht (Ne.symm hj), chain_foldT xs R _ ht h2]
      rfl
    | pow e i k => simp [isStepT] at h1

theorem chainW {t : Nat} {s : List Op} (hs : isChainT t s = true) (R : List Nat)
    (ht : t < R.length) {W : List Int} (hW : s.map src = W.map rho) {j : Nat}
    (hl : lettersIn R j W = true) :
    s.foldl (stepL OL) R = R.set t (wordR 5 12 1332 111 8 L H CM RM (AFx j) (AIx j) ONE W) := by
  unfold lettersIn at hl
  rw [Bool.and_eq_true, List.all_eq_true] at hl
  obtain ⟨hl, h1⟩ := hl
  match s, hs, W, hW with
  | .pow 1 i k :: tl, hs, w0 :: W', hW =>
    rw [List.headD_cons] at h1
    simp only [isChainT, Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨rfl, htl⟩ := hs
    simp only [List.map_cons, List.cons.injEq] at hW
    obtain ⟨hi, hm⟩ := hW
    have e0 : stepL OL R (.pow 1 i k) = R.set k (getN R i) := by
      change R.set k (OL.pow (getN R i) 1) = _
      rw [LyNF.pow_one']
    have g0 : getN R i = letterR (AFx j) (AIx j) w0 := by
      rw [src] at hi
      rw [hi]
      exact Nat.eq_of_beq_eq_true (hl w0 (by simp))
    rw [List.foldl_cons, e0, chain_foldT tl R _ ht htl, CFSG.KS.SporSch.LyM.wordR_cons,
      Nat.eq_of_beq_eq_true h1, LyNF.wordR_fold, g0]
    congr 2
    have hc : (fun op => getN R (src op)) = getN R ∘ src := rfl
    rw [hc, ← List.map_map, hm, List.map_map]
    exact List.map_congr_left fun l hl' => Nat.eq_of_beq_eq_true (hl l (by simp [hl']))
  | [], hs, _, _ => simp [isChainT] at hs
  | .mul _ _ _ :: _, hs, _, _ => simp [isChainT] at hs
  | .pow 0 _ _ :: _, hs, _, _ => simp [isChainT] at hs
  | .pow (_ + 2) _ _ :: _, hs, _, _ => simp [isChainT] at hs
  | .pow 1 _ _ :: _, _, [], hW => simp at hW

theorem wordK {K : Nat → Nat} {m j : Nat} {W : List Int}
    (hall : ∀ k < m, Nat.beq (wordR 5 12 1332 111 8 L H CM RM (AFx j) (AIx j) (K k)
      (List.take 16 (List.drop (Nat.mul k 16) W))) (K (Nat.succ k)) = true)
    (hk : (Nat.beq (K 0) ONE && Nat.beq (K m) (AF j) && Nat.ble W.length (Nat.mul m 16)) = true) :
    wordR 5 12 1332 111 8 L H CM RM (AFx j) (AIx j) ONE W = AF j := by
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨h0, hm⟩, hl⟩ := hk
  rw [← Nat.eq_of_beq_eq_true h0, LyNF.chunks hall (Nat.le_of_ble_eq_true hl),
    Nat.eq_of_beq_eq_true hm]

theorem kw2 : (Nat.beq (K2 0) ONE && Nat.beq (K2 K2.m) (AF 2) &&
    Nat.ble SW2.length (Nat.mul K2.m 16)) = true := by quickRfl
theorem kw3 : (Nat.beq (K3 0) ONE && Nat.beq (K3 K3.m) (AF 3) &&
    Nat.ble SW3.length (Nat.mul K3.m 16)) = true := by quickRfl
theorem kw4 : (Nat.beq (K4 0) ONE && Nat.beq (K4 K4.m) (AF 4) &&
    Nat.ble SW4.length (Nat.mul K4.m 16)) = true := by quickRfl
theorem kw5 : (Nat.beq (K5 0) ONE && Nat.beq (K5 K5.m) (AF 5) &&
    Nat.ble SW5.length (Nat.mul K5.m 16)) = true := by quickRfl
theorem kw6 : (Nat.beq (K6 0) ONE && Nat.beq (K6 K6.m) (AF 6) &&
    Nat.ble SW6.length (Nat.mul K6.m 16)) = true := by quickRfl

theorem word2 : wordR 5 12 1332 111 8 L H CM RM (AFx 2) (AIx 2) ONE SW2 = AF 2 := wordK K2.all kw2
theorem word3 : wordR 5 12 1332 111 8 L H CM RM (AFx 3) (AIx 3) ONE SW3 = AF 3 := wordK K3.all kw3
theorem word4 : wordR 5 12 1332 111 8 L H CM RM (AFx 4) (AIx 4) ONE SW4 = AF 4 := wordK K4.all kw4
theorem word5 : wordR 5 12 1332 111 8 L H CM RM (AFx 5) (AIx 5) ONE SW5 = AF 5 := wordK K5.all kw5
theorem word6 : wordR 5 12 1332 111 8 L H CM RM (AFx 6) (AIx 6) ONE SW6 = AF 6 := wordK K6.all kw6

theorem len0 : S0.length = 28 := by
  unfold S0
  rw [length_run, length_initN]
  rfl

theorem pow_step {R : List Nat} {t t' e X Y : Nat} (ht : t < R.length)
    (h : Nat.beq (OL.pow X e) Y = true) :
    [Op.pow e t t'].foldl (stepL OL) (R.set t X) = (R.set t X).set t' Y := by
  change (R.set t X).set t' (OL.pow (getN (R.set t X) t) e) = _
  rw [getN_set_eq ht, Nat.eq_of_beq_eq_true h]

theorem mid_eq5 : s13.foldl (stepL OL) (p12.foldl (stepL OL) (s11.foldl (stepL OL)
    (p10.foldl (stepL OL) (s9.foldl (stepL OL) (p8.foldl (stepL OL) (s7.foldl (stepL OL)
    (p6.foldl (stepL OL) (s5.foldl (stepL OL) S0)))))))) = init5 := by
  have hc := chains_ok5
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨c5, c7⟩, c9⟩, c11⟩, c13⟩ := hc
  obtain ⟨m5, m7, m9, m11, m13⟩ := maps_ok
  obtain ⟨e6, e8, e10, e12⟩ := pows_eq
  have l1 : U1.length = 28 := by simp [U1, len0]
  have l2 : U2.length = 28 := by simp [U2, l1]
  have l3 : U3.length = 28 := by simp [U3, l2]
  have l4 : U4.length = 28 := by simp [U4, l3]
  have a1 : p6.foldl (stepL OL) (s5.foldl (stepL OL) S0) = U1 := by
    rw [chainW c5 S0 (by rw [len0]; norm_num) m5 lt2, word2, e6]
    exact pow_step (by rw [len0]; norm_num) pw2
  have a2 : p8.foldl (stepL OL) (s7.foldl (stepL OL) U1) = U2 := by
    rw [chainW c7 U1 (by rw [l1]; norm_num) m7 lt3, word3, e8]
    exact pow_step (by rw [l1]; norm_num) pw3
  have a3 : p10.foldl (stepL OL) (s9.foldl (stepL OL) U2) = U3 := by
    rw [chainW c9 U2 (by rw [l2]; norm_num) m9 lt4, word4, e10]
    exact pow_step (by rw [l2]; norm_num) pw4
  have a4 : p12.foldl (stepL OL) (s11.foldl (stepL OL) U3) = U4 := by
    rw [chainW c11 U3 (by rw [l3]; norm_num) m11 lt5, word5, e12]
    exact pow_step (by rw [l3]; norm_num) pw5
  rw [a1, a2, a3, a4, chainW c13 U4 (by rw [l4]; norm_num) m13 lt6, word6]
  rfl

theorem regsN_eq_rest5 (k : List Nat → Bool) :
    regsN OL A B lyFiveN lyFiveProg k = runN OL rest5 init5 k := by
  rw [regsN_eq, prog_eq5]
  simp only [List.foldl_append]
  rw [runN_eq]
  change k (rest5.foldl (stepL OL) (s13.foldl (stepL OL) (p12.foldl (stepL OL)
    (s11.foldl (stepL OL) (p10.foldl (stepL OL) (s9.foldl (stepL OL) (p8.foldl (stepL OL)
    (s7.foldl (stepL OL) (p6.foldl (stepL OL) (s5.foldl (stepL OL) S0)))))))))) = _
  rw [mid_eq5]

end CertificateChecks.KernelMC.LyNF5

end
