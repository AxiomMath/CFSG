module

public import Certificates.Kernel.Misc.KGroups.U33Defs
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.LocalQTPermSound
public import CFSG.GH74.KGroups.U33Inputs
public import Certificates.Data.Kernel.Misc.KGrp

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMisc.U33K

open CFSG.KC.Ord CFSG.KC.Misc.KG CFSG.KC.LQT.P

noncomputable def upCommT (n x y : Nat) : Bool :=
  allN n fun i => Nat.beq (img x (img y i)) (img y (img x i))

noncomputable def upSqT (n c : Nat) : Bool := allN n fun i => Nat.beq (img c (img c i)) i

noncomputable def upOrd2T (n c : Nat) : Bool := andB (notB (isOne n c)) (upSqT n c)

theorem upImgLt (s j : Nat) : img s j < 32 := by
  rw [img_eq]
  exact Nat.mod_lt _ (by norm_num)

theorem upBeqOfFn {n : Nat} {f g : Nat → Nat} (hf : ∀ i < n, f i < 32) (hg : ∀ i < n, g i < 32) :
    Nat.beq (ofFn n f) (ofFn n g) = allN n fun i => Nat.beq (f i) (g i) := by
  refine Bool.eq_iff_iff.2 ?_
  rw [CFSG.KC.LQT.P.beq_iff, allN_iff, ofFn_eq, ofFn_eq]
  constructor
  · intro h i hi
    rw [CFSG.KC.LQT.P.beq_iff, ← E_digit hf hi, ← E_digit hg hi, h]
  · exact fun h => E_congr fun i hi => CFSG.KC.LQT.P.beq_iff.1 (h i hi)

theorem upComm_eq (n x y : Nat) : comm n x y = upCommT n x y :=
  upBeqOfFn (fun _ _ => upImgLt _ _) (fun _ _ => upImgLt _ _)

theorem upIsOneMul (n a b : Nat) (hn : n ≤ 32) :
    isOne n (mul n a b) = allN n fun i => Nat.beq (img a (img b i)) i :=
  upBeqOfFn (fun _ _ => upImgLt _ _) (fun _ hi => lt_of_lt_of_le hi hn)

theorem upOrdTwo (n c : Nat) (hn : n ≤ 32) : ordK n c 2 = upOrd2T n c := by
  change letB c (fun a => andB (notB (isOne n a)) (isOne n (mul n a c))) = _
  rw [letB_eq, upIsOneMul n c c hn]
  rfl

theorem upH28 : (28 : Nat) ≤ 32 := by norm_num

noncomputable def upGuard (n j v : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) v (Nat.blt j n)

noncomputable def upIterM (n c k : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun acc => acc) (fun _ ih acc => ih (mul n acc c)) k

noncomputable def upPImg (n c k acc : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun j => img acc j)
    (fun _ ih j => upGuard n j (ih (img c j))) k

noncomputable def upPowT (n c k acc : Nat) : Bool :=
  allN n fun i => Nat.beq (upPImg n c k acc (img c i)) i

theorem upImgOfFn {n : Nat} {g : Nat → Nat} (h : ∀ i < n, g i < 32) (j : Nat) :
    img (ofFn n g) j = upGuard n j (g j) := by
  rw [img_eq, ofFn_eq, upGuard]
  by_cases hj : j < n
  · rw [E_digit h hj, (blt_iff (a := j) (b := n)).2 hj]
  · have hb : Nat.blt j n = false := Bool.eq_false_iff.2 fun e => hj (blt_iff.1 e)
    have hl : E g n < 32 ^ j :=
      lt_of_lt_of_le (E_lt h) (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.div_eq_of_lt hl, hb]

theorem upImgMul (n s t j : Nat) : img (mul n s t) j = upGuard n j (img s (img t j)) :=
  upImgOfFn (fun _ _ => upImgLt _ _) j

theorem upIterM_succ (n c k acc : Nat) :
    upIterM n c (k + 1) acc = mul n (upIterM n c k acc) c := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih => exact ih (mul n acc c)

theorem upImgIter (n c k acc j : Nat) : img (upIterM n c k acc) j = upPImg n c k acc j := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    rw [upIterM_succ, upImgMul, ih]
    rfl

theorem upOrdGo_one (n c k : Nat) :
    ∀ acc, ordGo n c k acc = true → isOne n (upIterM n c k acc) = true := by
  induction k with
  | zero => exact fun _ h => h
  | succ k ih =>
    intro acc h
    change letB acc (fun a => andB (notB (isOne n a)) (ordGo n c k (mul n a c))) = true at h
    rw [letB_eq] at h
    cases hb : notB (isOne n acc)
    · rw [hb] at h
      exact absurd h Bool.false_ne_true
    · rw [hb] at h
      exact ih _ h

theorem upOrdGo_eq (n c k acc : Nat) (hn : n ≤ 32) :
    ordGo n c (k + 1) acc = andB (upPowT n c k acc) (ordGo n c (k + 1) acc) := by
  cases h : ordGo n c (k + 1) acc
  · cases upPowT n c k acc <;> rfl
  · have h1 := upOrdGo_one n c (k + 1) acc h
    rw [upIterM_succ, upIsOneMul n _ _ hn] at h1
    simp only [upImgIter] at h1
    have h2 : upPowT n c k acc = true := h1
    rw [h2]
    rfl

theorem upOrdK (n c k : Nat) (hn : n ≤ 32) :
    ordK n c (k + 2) = andB (upPowT n c k c) (ordK n c (k + 2)) :=
  upOrdGo_eq n c k c hn

noncomputable def upFibT (n : Nat) (E : Nat → Nat) (a k : Nat) : Bool :=
  letB (E k) fun y => andB (upPowT n y 5 y) (letB (evalWK n a y [false, true]) fun w =>
    andB (upPowT n w 4 w) (andB (ordK n y 7) (andB (ordK n w 6) true)))

theorem upFib_eq (n : Nat) (E : Nat → Nat) (a : Nat) (hn : n ≤ 32) :
    fibAt n E a 7 CFSG.GH74.KGroups.U33.wsU = upFibT n E a := by
  funext k
  rw [fibAt, upFibT, letB_eq, letB_eq, letB_eq]
  have h7 : ordK n (E k) 7 = andB (upPowT n (E k) 5 (E k)) (ordK n (E k) 7) := upOrdK n (E k) 5 hn
  have h6 : ordK n (evalWK n a (E k) [false, true]) 6 = andB (upPowT n
      (evalWK n a (E k) [false, true]) 4 (evalWK n a (E k) [false, true]))
      (ordK n (evalWK n a (E k) [false, true]) 6) := upOrdK n _ 4 hn
  have hp : pairK n a (E k) CFSG.GH74.KGroups.U33.wsU =
      andB (ordK n (evalWK n a (E k) [false, true]) 6) true := rfl
  rw [hp]
  revert h7 h6
  generalize ordK n (E k) 7 = A
  generalize ordK n (evalWK n a (E k) [false, true]) 6 = B
  generalize upPowT n (E k) 5 (E k) = P
  generalize upPowT n (evalWK n a (E k) [false, true]) 4 (evalWK n a (E k) [false, true]) = Q
  cases A <;> cases B <;> cases P <;> cases Q <;> simp [andB]

end CertificateChecks.KernelMisc.U33K

public section

namespace CertificateChecks.KernelMisc.U33K

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.M22 CFSG.KC.Misc.KG CFSG.KC.LQT
open CFSG.KC.LQT.P CFSG.GH74.KGroups.U33

theorem treeP0 : allR 0 1512 (treeAt (mul 28) (one 28) AG 2 EP PAP) = true := by quickRfl
theorem treeP1 : allR 1512 1512 (treeAt (mul 28) (one 28) AG 2 EP PAP) = true := by quickRfl
theorem treeP2 : allR 3024 1512 (treeAt (mul 28) (one 28) AG 2 EP PAP) = true := by quickRfl
theorem treeP3 : allR 4536 1512 (treeAt (mul 28) (one 28) AG 2 EP PAP) = true := by quickRfl
theorem sortPB : allN 6048 (sortAt 6048 EP SGP) = true := by quickRfl
theorem closedP0 : allR 0 1512 (closedAt (mul 28) AG 2 6048 EP CTP) = true := by quickRfl
theorem closedP1 : allR 1512 1512 (closedAt (mul 28) AG 2 6048 EP CTP) = true := by quickRfl
theorem closedP2 : allR 3024 1512 (closedAt (mul 28) AG 2 6048 EP CTP) = true := by quickRfl
theorem closedP3 : allR 4536 1512 (closedAt (mul 28) AG 2 6048 EP CTP) = true := by quickRfl

theorem memB : andB (inP (UG 0)) (andB (inP (UG 1)) (andB (inP (P.conj 28 (AG 2) (UG 0)))
    (inP (P.conj 28 (AG 2) (UG 1))))) = true := by quickRfl
theorem wordB : allN 2 (fun j => andB (lettersK 2 (WAB j))
    (Nat.beq (wordK 28 UG 2 (WAB j)) (AG j))) = true := by quickRfl
theorem c2PB : Nat.beq (cntN 6048 fun k => ordK 28 (EP k) 2) 63 = true := by
  simp only [upOrdTwo _ _ upH28]
  quickRfl
theorem fibPB : Nat.beq (cntN 6048 (fibAt 28 EP (UG 0) 7 wsU)) 192 = true := by
  rw [upFib_eq _ _ _ upH28]
  quickRfl
theorem cPuB : Nat.beq (cntN 6048 fun k => comm 28 (EP k) (UG 0)) 96 = true := by
  simp only [upComm_eq]
  quickRfl
theorem cPtB : Nat.beq (cntN 6048 fun k => comm 28 (EP k) (RG 0)) 24 = true := by
  simp only [upComm_eq]
  quickRfl

end CertificateChecks.KernelMisc.U33K

end
