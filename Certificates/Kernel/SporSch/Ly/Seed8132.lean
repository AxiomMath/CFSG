
module

public import Certificates.Kernel.SporSch.Ly.SeedData
public import Certificates.Kernel.SporSch.Ly.BS18009
public import CFSG.Certificates.Kernel.LyOmega.SoundB4
public import CFSG.Certificates.Kernel.SporSch.LySevMat
public import CFSG.Certificates.Kernel.PackSetSound
public import Certificates.Kernel.SporSch.Ly.NeId

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.LySd

open CFSG.KC.Enum CFSG.KS CFSG.KC.Ord CFSG.KS.SporSch.LyM CFSG.KD.OrdLy CFSG.KC.LySeed
open CFSG.RankThree.Native CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CertificateChecks.KernelSporSch.LyBS CertificateChecks.KernelSporSch.LyBSF

local notation "U" X:max => unpackL 111 12 1332 X

set_option exponentiation.threshold 2000 in
theorem laneE_eq (X i : Nat) {j : Nat} (hj : j < 111) :
    laneE X i j = X / 2 ^ (1332 * i + 12 * j) % 2 ^ 12 := by
  unfold laneE laneR
  change ((X >>> (1332 * i)) &&& (1 <<< 1332 - 1)) >>> (12 * j) &&& (2 ^ 12 - 1) = _
  rw [Nat.one_shiftLeft, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have e : (2 : Nat) ^ 1332 = 2 ^ (12 * j) * 2 ^ (1332 - 12 * j) := by
    rw [← pow_add]; congr 1; omega
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega)),
    Nat.div_div_eq_div_mul, ← pow_add]

theorem U_get {X i j : Nat} (hi : i < 111) (hj : j < 111) : ((U X)[i]!)[j]! = laneE X i j := by
  rw [unpackL_get hi hj, laneE_eq X i hj]

theorem entK_spec {X : Nat} {f : Nat → Nat → Nat} (h : entK X f = true) {i j : Nat} (hi : i < 111)
    (hj : j < 111) : ((U X)[i]!)[j]! = f i j := by
  rw [U_get hi hj]
  exact Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec (CFSG.KC.Pack.allN_spec h i hi) j hj)

theorem U_ext {X Y : Array (Array Nat)} (hX : X.size = 111 ∧ ∀ i < 111, X[i]!.size = 111)
    (hY : Y.size = 111 ∧ ∀ i < 111, Y[i]!.size = 111)
    (h : ∀ i < 111, ∀ j < 111, (X[i]!)[j]! = (Y[i]!)[j]!) : X = Y := by
  apply Array.ext (by rw [hX.1, hY.1])
  intro i h1 h2
  have hi : i < 111 := by rw [hX.1] at h1; exact h1
  rw [← getElem!_pos X i h1, ← getElem!_pos Y i h2]
  apply Array.ext (by rw [hX.2 i hi, hY.2 i hi])
  intro j g1 g2
  have hj : j < 111 := by rw [hX.2 i hi] at g1; exact g1
  rw [← getElem!_pos _ j g1, ← getElem!_pos _ j g2]
  exact h i hi j hj

theorem U_size (X : Nat) : (U X).size = 111 ∧ ∀ i < 111, (U X)[i]!.size = 111 := by
  refine ⟨by simp [unpackL], fun i hi => ?_⟩
  unfold unpackL
  rw [ofFn_get! _ hi]
  simp

theorem transM_U {X : Nat} (h' : symK X = true) : transM (U X) = U X := by
  have h : entK X (fun i j => laneE X j i) = true := h'
  apply U_ext ⟨by simp [transM], fun i hi => by unfold transM; rw [ofFn_get! _ hi]; simp⟩ (U_size X)
  intro i hi j hj
  unfold transM
  rw [ofFn_get! _ hi, ofFn_get! _ hj]
  simp only
  rw [U_get hj hi, entK_spec h hi hj]

theorem nl_filter : ∀ {cs : List Char}, noNl cs = true → cs.filter (· ≠ '\n') = cs
  | [], _ => rfl
  | c :: cs, h => by
    obtain ⟨h1, h2⟩ := LyBSF.andOf h
    have hc : c ≠ '\n' := fun e => by
      rw [e] at h1
      exact absurd h1 (by decide)
    rw [List.filter_cons_of_pos (by simpa using hc), nl_filter h2]

theorem formF_eq : formF = U D.F := by
  obtain ⟨hlen, hd⟩ := CFSG.KS.LyOm.SB4.digLanesK_sound (by norm_num) fdig
  rw [nl_filter fnl] at hlen hd
  apply U_ext ⟨by simp [formF, matOfDigits], fun i hi => by
    unfold formF matOfDigits; rw [ofFn_get! _ hi]; simp⟩ (U_size D.F)
  intro i hi j hj
  unfold formF matOfDigits digitsOf
  simp only
  rw [ofFn_get! _ hi, ofFn_get! _ hj, LyFD.eq, String.toList_ofList, unpackL_get hi hj]
  have ht : 111 * i + j < 12321 := by omega
  rw [getElem!_pos _ _ (by simpa [hlen] using ht), Array.getElem_map, List.getElem_toArray,
    ← List.getD_eq_getElem _ '0' (by rw [hlen]; exact ht), hd _ ht]
  have e1 : (111 * i + j) / 111 = i := by omega
  have e2 : (111 * i + j) % 111 = j := by omega
  rw [e1, e2, Char.toNat_ofNat]
  have hv : (48 + D.F / 2 ^ (1332 * i + 12 * j) % 2 ^ 12).isValidChar := by
    left
    have := Nat.mod_lt (D.F / 2 ^ (1332 * i + 12 * j)) (show 0 < 2 ^ 12 by norm_num)
    omega
  rw [if_pos hv]
  simp

theorem keyDigit_encode (Dg : Nat → Nat) {p : Nat} (hp : p < 828) :
    keyDigit (encodeDigits Dg) p = Dg p % 5 := by
  unfold keyDigit encodeDigits code3
  have hq : p / 3 < 276 := by omega
  rw [ByteArray.get!, getElem!_pos _ (p / 3) (by simpa using hq)]
  simp only [Array.getElem_ofFn]
  rw [UInt8.toNat_ofNat']
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 3 ∧ p = 3 * q + r :=
    ⟨p / 3, p % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod p 3).symm⟩
  have e1 : (3 * q + r) / 3 = q := by omega
  have e2 : (3 * q + r) % 3 = r := by omega
  rw [e1, e2]
  have hlt : Dg (3 * q) % 5 + 5 * (Dg (3 * q + 1) % 5) + 25 * (Dg (3 * q + 2) % 5) < 256 := by
    omega
  rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hlt (by norm_num))]
  interval_cases r <;> simp <;> omega

theorem rootDigit_get {p : Nat} (hp : p < 826) : rootDigitArr[p]! % 5 = rdig p := by
  unfold rootDigitArr digitsOf rdig
  have hl : LyRD.chars.length = 826 := Nat.eq_of_beq_eq_true rlen
  rw [LyRD.eq, String.toList_ofList, getElem!_pos _ p (by simpa [hl] using hp), Array.getElem_map,
    List.getElem_toArray, ← List.getD_eq_getElem _ '0' (by rw [hl]; exact hp)]
  rfl

theorem rootKey_digit {p : Nat} (hp : p < 826) : keyDigit rootKey p = rdig p := by
  unfold rootKey
  rw [keyDigit_encode _ (by omega), if_pos hp, rootDigit_get hp]

theorem mulM_get (A B : Array (Array Nat)) {i k : Nat} (hi : i < 111) (hk : k < 111) :
    ((mulM 5 111 A B)[i]!)[k]! = (∑ j ∈ Finset.range 111, (A[i]!)[j]! * (B[j]!)[k]!) % 5 :=
  CFSG.KS.SporSch.LySvM.mulM_ent A B hi hk

theorem sum_pad (g : Nat → Nat) (h : ∀ j, 7 ≤ j → j < 111 → g j = 0) :
    ∑ j ∈ Finset.range 111, g j = ∑ j ∈ Finset.range 7, g j := by
  rw [← Finset.sum_range_add_sum_Ico _ (by norm_num : 7 ≤ 111)]
  rw [Finset.sum_eq_zero (fun j hj => h j (Finset.mem_Ico.1 hj).1 (Finset.mem_Ico.1 hj).2), add_zero]

theorem pl_get {j a : Nat} (hj : j < 111) (ha : a < 111) :
    ((U D.PL)[j]!)[a]! = if a < 7 then keyDigit rootKey (111 * a + j) else 0 := by
  rw [entK_spec pent hj ha]
  by_cases h : a < 7
  · have hb : Nat.blt a 7 = true := Nat.blt_eq.mpr h
    rw [if_pos h, rootKey_digit (by omega)]
    simp only [hb]
    rfl
  · have hb : Nat.blt a 7 = false := Bool.eq_false_iff.mpr fun e => h (Nat.blt_eq.mp e)
    rw [if_neg h]
    simp only [hb]

theorem cl_get {a b : Nat} (ha : a < 111) (hb : b < 111) :
    ((U D.CL)[a]!)[b]! = if a < 7 ∧ b < 7 then keyDigit rootKey (777 + 7 * a + b) else 0 := by
  rw [entK_spec cent ha hb]
  by_cases h : a < 7 ∧ b < 7
  · have h1 : Nat.blt a 7 = true := Nat.blt_eq.mpr h.1
    have h2 : Nat.blt b 7 = true := Nat.blt_eq.mpr h.2
    rw [if_pos h, rootKey_digit (by omega)]
    simp only [h1, h2]
    rfl
  · rw [if_neg h]
    by_cases h1 : a < 7
    · have g1 : Nat.blt a 7 = true := Nat.blt_eq.mpr h1
      have g2 : Nat.blt b 7 = false := Bool.eq_false_iff.mpr fun e => h ⟨h1, Nat.blt_eq.mp e⟩
      simp only [g1, g2]
    · have g1 : Nat.blt a 7 = false := Bool.eq_false_iff.mpr fun e => h1 (Nat.blt_eq.mp e)
      simp only [g1]

theorem plt_get {a j : Nat} (ha : a < 111) (hj : j < 111) : ((U D.PLT)[a]!)[j]! = ((U D.PL)[j]!)[a]! := by
  rw [entK_spec ptr ha hj, U_get hj ha]

theorem fold7 (g : Nat → Nat) : Nat.fold 7 (fun a _ acc => acc + g a) 0 = ∑ a ∈ Finset.range 7, g a :=
  CFSG.KS.SporSch.LyM.fold_sum 7 g

theorem mulM_size (A B : Array (Array Nat)) :
    (mulM 5 111 A B).size = 111 ∧ ∀ i < 111, (mulM 5 111 A B)[i]!.size = 111 := by
  refine ⟨by simp [mulM], fun i hi => ?_⟩
  unfold mulM
  rw [ofFn_get! _ hi]
  simp

theorem keyTensor_size (K : ByteArray) :
    (keyTensor K).size = 111 ∧ ∀ i < 111, (keyTensor K)[i]!.size = 111 := by
  refine ⟨by simp [keyTensor], fun i hi => ?_⟩
  unfold keyTensor
  dsimp only
  rw [ofFn_get! _ hi]
  simp

theorem keyTensor_get (K : ByteArray) {i j : Nat} (hi : i < 111) (hj : j < 111) :
    ((keyTensor K)[i]!)[j]! = (∑ b ∈ Finset.range 7, ((∑ a ∈ Finset.range 7,
      keyDigit K (111 * a + i) * keyDigit K (777 + 7 * a + b)) % 5) * keyDigit K (111 * b + j)) % 5 := by
  unfold keyTensor
  dsimp only
  rw [ofFn_get! _ hi, ofFn_get! _ hj]
  dsimp only
  rw [fold7]
  refine congrArg (· % 5) (Finset.sum_congr rfl fun b hb => ?_)
  have hb7 := Finset.mem_range.1 hb
  rw [ofFn_get! _ hi, ofFn_get! _ hb7, ofFn_get! _ hj, ofFn_get! _ hb7]
  dsimp only
  rw [fold7]
  refine congrArg (fun x => x % 5 * keyDigit K (111 * b + j)) (Finset.sum_congr rfl fun a ha => ?_)
  have ha7 := Finset.mem_range.1 ha
  rw [ofFn_get! _ hi, ofFn_get! _ ha7, ofFn_get! _ ha7, ofFn_get! _ hb7]

theorem tensor_gen (K : ByteArray) {P C PT : Array (Array Nat)}
    (hP : ∀ j < 111, ∀ a < 111, (P[j]!)[a]! = if a < 7 then keyDigit K (111 * a + j) else 0)
    (hC : ∀ a < 111, ∀ b < 111, (C[a]!)[b]! = if a < 7 ∧ b < 7 then keyDigit K (777 + 7 * a + b) else 0)
    (hT : ∀ a < 111, ∀ j < 111, (PT[a]!)[j]! = (P[j]!)[a]!) :
    keyTensor K = mulM 5 111 (mulM 5 111 P C) PT := by
  apply U_ext (keyTensor_size K) (mulM_size _ _)
  intro i hi j hj
  rw [keyTensor_get K hi hj, mulM_get _ _ hi hj, sum_pad _ (fun b hb hb' => by
    rw [hT b hb' j hj, hP j hj b hb', if_neg (by omega), Nat.mul_zero])]
  refine congrArg (· % 5) (Finset.sum_congr rfl fun b hb => ?_)
  have hb7 := Finset.mem_range.1 hb
  rw [hT b (by omega) j hj, hP j hj b (by omega), if_pos hb7, mulM_get _ _ hi (by omega),
    sum_pad _ (fun a ha ha' => by rw [hP i hi a ha', if_neg (by omega), Nat.zero_mul])]
  refine congrArg (fun x => x % 5 * keyDigit K (111 * b + j)) (Finset.sum_congr rfl fun a ha => ?_)
  have ha7 := Finset.mem_range.1 ha
  rw [hP i hi a (by omega), hC a (by omega) b (by omega), if_pos ha7, if_pos ⟨ha7, hb7⟩]

theorem tensor_eq : keyTensor rootKey = mulM 5 111 (mulM 5 111 (U D.PL) (U D.CL)) (U D.PLT) :=
  tensor_gen rootKey (fun j hj a ha => pl_get hj ha) (fun a ha b hb => cl_get ha hb)
    (fun a ha j hj => plt_get ha hj)

theorem lyZeroM_eq : lyZeroM = U 0 := by
  have hz : lyZeroM.size = 111 ∧ ∀ i < 111, lyZeroM[i]!.size = 111 := by
    refine ⟨by simp [lyZeroM], fun i hi => ?_⟩
    unfold lyZeroM
    rw [getElem!_pos _ i (by simpa using hi)]
    simp
  apply U_ext hz (U_size 0)
  intro i hi j hj
  rw [unpackL_get hi hj]
  unfold lyZeroM
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_replicate,
    getElem!_pos _ j (by simpa using hj), Array.getElem_replicate]
  simp

theorem powB {X : Nat} (hX : vld X = true) (e : Nat) :
    (powM 5 111 (U X) e == idM 111) = Nat.beq (pw X e) ONE :=
  LyNe.powB hX e

theorem powV {X : Nat} (hX : vld X = true) (e : Nat) : powM 5 111 (U X) e = U (pw X e) ∧ vld (pw X e) = true :=
  powM_eq consts (hv hX) e

theorem neId {X : Nat} (hX : vld X = true) : lyNeId (U X) = !Nat.beq X ONE := LyNe.neId hX

theorem vAB : vld AB = true := mulV vA vB
theorem vG : vld G = true := mulV (mulV vA vB4) (mulV vA vB4)
theorem vGi : vld Gi = true := mulV (mulV vB vA) (mulV vB vA)
theorem vXL : vld XL = true := mulV (mulV (mulV vA vGi) vB) vG

theorem matX_eq : matX = U XL := by
  unfold matX matG matGi XL G Gi
  simp only
  have eG : mul (mul A B4) (mul A B4) = G := rfl
  have eGi : mul (mul B A) (mul B A) = Gi := rfl
  rw [b4_eq, matA_eq, matB_eq, mulE vA vB4, mulE (mulV vA vB4) (mulV vA vB4), mulE vB vA,
    mulE (mulV vB vA) (mulV vB vA), eG, eGi, mulE vA vGi, mulE (mulV vA vGi) vB,
    mulE (mulV (mulV vA vGi) vB) vG]

theorem vT : vld (mul (mul D.PL D.CL) D.PLT) = true := mulV (mulV vPL vCL) vPLT
theorem vE : vld EL = true := mulV vT vF

theorem rootKey_S : lyCheckS = true := by
  unfold lyCheckS
  rw [List.all_eq_true]
  intro a ha
  rw [List.all_eq_true]
  intro b hb
  have ha' := List.mem_range.1 ha
  have hb' := List.mem_range.1 hb
  have key : ∀ x y, x < 7 → y < 7 → (keyS rootKey)[7 * x + y]! = laneE D.CL x y := by
    intro x y hx hy
    have h := cl_get (a := x) (b := y) (by omega) (by omega)
    rw [if_pos ⟨hx, hy⟩, U_get (by omega) (by omega)] at h
    rw [CFSG.KS.SporSch.LyK.keyS_get _ (by omega), ← Nat.add_assoc, h]
  have hc : entK D.CL (fun i j => laneE D.CL j i) = true := csym
  have hs := entK_spec hc (i := a) (j := b) (by omega) (by omega)
  rw [U_get (by omega) (by omega)] at hs
  rw [key a b ha' hb', key b a hb' ha', hs]
  exact beq_self_eq_true _

theorem facts : lySeedChecks = true := by
  unfold lySeedChecks lyCheckAB14 lyCheckAB7 lyCheckAB2 lyCheckA lyCheckB lyCheckX lyCheckFsymm
    lyCheckFinv lyCheckE lyAB lyEArr
  have hfi : invM 5 111 (U D.F) = U D.FI := invM_eq Nat.prime_five consts (hv vF) (hv vFI) finv
  have eAB : mul A B = AB := rfl
  have eEL : mul (mul (mul D.PL D.CL) D.PLT) D.F = EL := rfl
  rw [rootKey_S, tensor_eq, formF_eq, matX_eq, matA_eq, matB_eq, mulE vA vB, eAB, transM_U fsym,
    hfi, mulE vF vFI, idE, beqE (mulV vF vFI) vOne, ← idE, powB vAB 14, (powV vAB 7).1,
    (powV vAB 2).1, neId (powV vAB 7).2, neId (powV vAB 2).2, neId vA, neId vB, neId vXL,
    mulE vPL vCL, mulE (mulV vPL vCL) vPLT, mulE vT vF, eEL, mulE vE vE, lyZeroM_eq,
    beqE (mulV vE vE) v0]
  simp only [beq_self_eq_true, ab14, ab7, ab2, nA, nB, nX, finv, e2, Bool.and_self]

end CertificateChecks.KernelSporSch.LySd

end
