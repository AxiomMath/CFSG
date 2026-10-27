module

public import Certificates.Kernel.Sporadic.Fi22.WordKit
public import Certificates.Kernel.Sporadic.Fi22.N2070Final
public import Certificates.Kernel.Misc.Perm.HexCmd
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBLatticeCheck
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoBLatticeCheck
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Perf450108

meta def xyM : Array (Array Nat) :=
  CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB.xyfArr

end CertificateChecks.KernelSpor.Perf450108

#kmisc_packarrs CertificateChecks.KernelSpor.Perf450108.XY45 CertificateChecks.KernelSpor.Perf450108.xyM 6

namespace CertificateChecks.KernelSpor.Perf450108

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin
open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
open CFSG.Sporadic.FischerOddCore CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Fi22TwoB
open CertificateChecks.KernelSpor

theorem wordG_eq {n w kS : Nat} {S : Array (Array Nat)} {PS PSI : Nat → Nat}
    (hS : S.size = kS ∧ ∀ j < kS, S[j]! = unpack n w (PS j))
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hsz : szOK n w = true) {wd : List Int} (hl : lettersK kS wd = true) :
    wordA n S (rawInvs n S) wd = unpack n w (wordK n w (mask w) (pidn n w) PS PSI wd) := by
  refine (wordEqK_sound hS hp ?_).1
  rw [wordEqK]
  simp only [bAnd_iff, hsz, hl, true_and]
  exact Nat.beq_refl _

theorem ofFn_inv {n m : Nat} (S : Array (Array Nat)) (hS : S.size = m) :
    (Array.ofFn (n := m) fun j => invCand n S[j.val]!) = rawInvs n S := by
  apply Array.ext
  · simp [rawInvs, hS]
  · intro i h1 h2
    simp only [Array.getElem_ofFn, rawInvs, Array.getElem_map]
    rw [getElem!_pos S i (by simpa [hS] using h1)]

@[expose] noncomputable def sel (a b j : Nat) : Nat := cond (Nat.beq j 0) a b

@[expose] noncomputable def CG (j : Nat) : Nat := sel (Fi22CentT.L 20) (Fi22CentT.L 21) j
@[expose] noncomputable def CGI (j : Nat) : Nat := sel (Fi22E2065.CI 20) (Fi22E2065.CI 21) j

@[expose] noncomputable def WC (wd : List Int) : Nat := wordK 3510 12 (mask 12) (pidn 3510 12) CG CGI wd

@[expose] noncomputable def UK (a b : List Int) : Nat :=
  Fi22X.c (Fi22X.c (WC a) (WC b)) (Fi22X.c (Fi22X.inv (WC a)) (Fi22X.inv (WC b)))

@[expose] noncomputable def perfK : Bool :=
  allN 2 (fun j => bAnd(permOK 3510 12 (mask 12) (3510 * 12) (CG j) (CGI j), Fi22X.cn (CG j))) &&
  allN 4 (fun s => Fi22X.cn (WC (commA.getD s [])) && Fi22X.cn (WC (commB.getD s [])) &&
    permOK 3510 12 (mask 12) (3510 * 12) (WC (commA.getD s [])) (Fi22X.inv (WC (commA.getD s []))) &&
    permOK 3510 12 (mask 12) (3510 * 12) (WC (commB.getD s [])) (Fi22X.inv (WC (commB.getD s []))) &&
    Fi22X.cn (Fi22X.inv (WC (commA.getD s []))) && Fi22X.cn (Fi22X.inv (WC (commB.getD s [])))) &&
  Nat.beq (Fi22X.c (UK (commA.getD 0 []) (commB.getD 0 [])) (UK (commA.getD 1 []) (commB.getD 1 [])))
    (CG 0) &&
  Nat.beq (Fi22X.c (UK (commA.getD 2 []) (commB.getD 2 [])) (UK (commA.getD 3 []) (commB.getD 3 [])))
    (CG 1)

theorem perfOK : perfK = true := by quickRfl

theorem lettersAB : (commA.all (lettersK 2) && commB.all (lettersK 2)) = true := by quickRfl

@[expose] def S0 : Array (Array Nat) := Array.ofFn (n := 2) fun j => genArr (j.val + 1)
@[expose] def Si0 : Array (Array Nat) := Array.ofFn (n := 2) fun j => invCand 3510 S0[j.val]!
@[expose] def a0 : Array (Array Nat) :=
  Array.ofFn (n := 4) fun s => wordA 3510 S0 Si0 (commA.getD s.val [])
@[expose] def b0 : Array (Array Nat) :=
  Array.ofFn (n := 4) fun s => wordA 3510 S0 Si0 (commB.getD s.val [])
@[expose] def ai0 : Array (Array Nat) := Array.ofFn (n := 4) fun s => invCand 3510 a0[s.val]!
@[expose] def bi0 : Array (Array Nat) := Array.ofFn (n := 4) fun s => invCand 3510 b0[s.val]!
@[expose] def u0 : Array (Array Nat) := Array.ofFn (n := 4) fun s =>
  compA 3510 (compA 3510 a0[s.val]! b0[s.val]!) (compA 3510 ai0[s.val]! bi0[s.val]!)

theorem perf_unfold : checkPerf () =
    (commA.length == 4 && commB.length == 4 && commA.all (lettersOK 2) && commB.all (lettersOK 2) &&
      allLt 2 (fun j => isInvA 3510 S0[j]! Si0[j]!) &&
      allLt 4 (fun s => isInvA 3510 a0[s]! ai0[s]! && isInvA 3510 b0[s]! bi0[s]!) &&
      eqA 3510 (compA 3510 u0[0]! u0[1]!) S0[0]! && eqA 3510 (compA 3510 u0[2]! u0[3]!) S0[1]!) :=
  rfl

theorem get_ofFn {α : Type} [Inhabited α] {m : Nat} (f : Fin m → α) {i : Nat} (hi : i < m) :
    (Array.ofFn f)[i]! = f ⟨i, hi⟩ := by
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem S0_bind : S0.size = 2 ∧ ∀ j < 2, S0[j]! = unpack 3510 12 (CG j) := by
  refine ⟨by simp [S0], fun j hj => ?_⟩
  rw [S0, get_ofFn _ hj]
  interval_cases j
  · exact N2070.cent_eq (by simp [cLine])
  · exact N2070.cent_eq (by simp [cLine])

theorem perf_parts : allN 2 (fun j => bAnd(permOK 3510 12 (mask 12) (3510 * 12) (CG j) (CGI j),
      Fi22X.cn (CG j))) = true ∧
    (∀ s < 4, Fi22X.cn (WC (commA.getD s [])) = true ∧ Fi22X.cn (WC (commB.getD s [])) = true ∧
      permOK 3510 12 (mask 12) (3510 * 12) (WC (commA.getD s [])) (Fi22X.inv (WC (commA.getD s [])))
        = true ∧
      permOK 3510 12 (mask 12) (3510 * 12) (WC (commB.getD s [])) (Fi22X.inv (WC (commB.getD s [])))
        = true ∧
      Fi22X.cn (Fi22X.inv (WC (commA.getD s []))) = true ∧
      Fi22X.cn (Fi22X.inv (WC (commB.getD s []))) = true) ∧
    Nat.beq (Fi22X.c (UK (commA.getD 0 []) (commB.getD 0 [])) (UK (commA.getD 1 []) (commB.getD 1 [])))
      (CG 0) = true ∧
    Nat.beq (Fi22X.c (UK (commA.getD 2 []) (commB.getD 2 [])) (UK (commA.getD 3 []) (commB.getD 3 [])))
      (CG 1) = true := by
  have h := perfOK
  unfold perfK at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun s hs => ?_, h3, h4⟩
  have := allN_spec h2 s hs
  simp only [Bool.and_eq_true, and_assoc] at this
  exact this

theorem permCG : allN 2 (fun j => permOK 3510 12 (mask 12) (3510 * 12) (CG j) (CGI j)) = true :=
  allN_of_forall fun j hj => ((bAnd_iff _ _).1 (allN_spec perf_parts.1 j hj)).1

theorem cnCG {j : Nat} (hj : j < 2) : Fi22X.cn (CG j) = true :=
  ((bAnd_iff _ _).1 (allN_spec perf_parts.1 j hj)).2

theorem Si0_eq : Si0 = rawInvs 3510 S0 := ofFn_inv S0 S0_bind.1

theorem word_eq {wd : List Int} (hl : lettersK 2 wd = true) :
    wordA 3510 S0 Si0 wd = unpack 3510 12 (WC wd) := by
  rw [Si0_eq]
  exact wordG_eq S0_bind permCG Fi22W.szOK' hl

theorem lettersA {s : Nat} (hs : s < 4) : lettersK 2 (commA.getD s []) = true := by
  have h := lettersAB
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  interval_cases s <;> exact h.1 _ (by simp [commA])

theorem lettersB {s : Nat} (hs : s < 4) : lettersK 2 (commB.getD s []) = true := by
  have h := lettersAB
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  interval_cases s <;> exact h.2 _ (by simp [commB])

theorem a0_get {s : Nat} (hs : s < 4) : a0[s]! = unpack 3510 12 (WC (commA.getD s [])) := by
  rw [a0, get_ofFn _ hs]
  exact word_eq (lettersA hs)

theorem b0_get {s : Nat} (hs : s < 4) : b0[s]! = unpack 3510 12 (WC (commB.getD s [])) := by
  rw [b0, get_ofFn _ hs]
  exact word_eq (lettersB hs)

theorem ai0_get {s : Nat} (hs : s < 4) :
    ai0[s]! = unpack 3510 12 (Fi22X.inv (WC (commA.getD s []))) := by
  rw [ai0, get_ofFn _ hs]
  change invCand 3510 a0[s]! = _
  rw [a0_get hs]
  exact (invEqK_sound (perf_parts.2.1 s hs).2.2.1).1

theorem bi0_get {s : Nat} (hs : s < 4) :
    bi0[s]! = unpack 3510 12 (Fi22X.inv (WC (commB.getD s []))) := by
  rw [bi0, get_ofFn _ hs]
  change invCand 3510 b0[s]! = _
  rw [b0_get hs]
  exact (invEqK_sound (perf_parts.2.1 s hs).2.2.2.1).1

theorem u0_get {s : Nat} (hs : s < 4) :
    u0[s]! = unpack 3510 12 (UK (commA.getD s []) (commB.getD s [])) ∧
      Fi22X.cn (UK (commA.getD s []) (commB.getD s [])) = true := by
  obtain ⟨ca, cb, -, -, cai, cbi⟩ := perf_parts.2.1 s hs
  rw [u0, get_ofFn _ hs]
  change compA 3510 (compA 3510 a0[s]! b0[s]!) (compA 3510 ai0[s]! bi0[s]!) = _ ∧ _
  rw [a0_get hs, b0_get hs, ai0_get hs, bi0_get hs, Fi22X.comp_eq ca cb, Fi22X.comp_eq cai cbi,
    Fi22X.comp_eq (Fi22X.cn_c ca cb) (Fi22X.cn_c cai cbi)]
  exact ⟨rfl, Fi22X.cn_c (Fi22X.cn_c ca cb) (Fi22X.cn_c cai cbi)⟩

theorem perf : checkPerf () = true := by
  rw [perf_unfold]
  have hl : (commA.length == 4 && commB.length == 4 && commA.all (lettersOK 2) &&
      commB.all (lettersOK 2)) = true := by decide +kernel
  simp only [Bool.and_eq_true] at hl ⊢
  obtain ⟨u0', cu0⟩ := u0_get (s := 0) (by norm_num)
  obtain ⟨u1', cu1⟩ := u0_get (s := 1) (by norm_num)
  obtain ⟨u2', cu2⟩ := u0_get (s := 2) (by norm_num)
  obtain ⟨u3', cu3⟩ := u0_get (s := 3) (by norm_num)
  refine ⟨⟨⟨⟨hl, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    rw [Si0_eq]
    have e : (rawInvs 3510 S0)[j]! = invCand 3510 S0[j]! := by
      rw [getElem!_pos _ j (by simp [rawInvs, S0_bind.1]; omega),
        getElem!_pos S0 j (by rw [S0_bind.1]; omega)]
      simp [rawInvs]
    rw [e]
    exact Fi22E2067.isInv_of (S0_bind.2 j hj) (allN_spec permCG j hj)
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro s hs
    rw [Bool.and_eq_true]
    obtain ⟨-, -, pa, pb, -, -⟩ := perf_parts.2.1 s hs
    refine ⟨?_, ?_⟩
    · rw [ai0_get hs, ← (invEqK_sound pa).1, ← a0_get hs]
      exact Fi22E2067.isInv_of (a0_get hs) pa
    · rw [bi0_get hs, ← (invEqK_sound pb).1, ← b0_get hs]
      exact Fi22E2067.isInv_of (b0_get hs) pb
  · rw [u0', u1', S0_bind.2 0 (by norm_num), Fi22X.comp_eq cu0 cu1]
    exact Fi22X.eqA_of (Fi22X.cn_c cu0 cu1) (cnCG (by norm_num)) perf_parts.2.2.1
  · rw [u2', u3', S0_bind.2 1 (by norm_num), Fi22X.comp_eq cu2 cu3]
    exact Fi22X.eqA_of (Fi22X.cn_c cu2 cu3) (cnCG (by norm_num)) perf_parts.2.2.2

@[expose] noncomputable def cn45 (p : Nat) : Bool := canonK 45 6 (mask 6) (45 * 6) p
@[expose] noncomputable def inv45 (p : Nat) : Nat := pinvS 45 6 (mask 6) p
@[expose] noncomputable def XYI (j : Nat) : Nat := inv45 (XY45 j)
@[expose] noncomputable def TK (k : Nat) : Nat :=
  wordK 45 6 (mask 6) (pidn 45 6) XY45 XYI (tauWords.getD k [])
@[expose] noncomputable def T2 (j : Nat) : Nat := TK (j + 1)
@[expose] noncomputable def T2I (j : Nat) : Nat := inv45 (T2 j)

@[expose] noncomputable def rhoK : Bool :=
  szOK 45 6 && allN 3 (fun j => permOK 45 6 (mask 6) (45 * 6) (XY45 j) (XYI j)) &&
  allN 2 (fun j => permOK 45 6 (mask 6) (45 * 6) (T2 j) (T2I j) && cn45 (T2 j) && cn45 (XY45 j)) &&
  allN 2 (fun j => Nat.beq (wordK 45 6 (mask 6) (pidn 45 6) XY45 XYI (rhoXY.getD j [])) (T2 j)) &&
  allN 2 (fun j => Nat.beq (wordK 45 6 (mask 6) (pidn 45 6) T2 T2I (rhoTau.getD j [])) (XY45 j)) &&
  tauWords.all (lettersK 3) && rhoXY.all (lettersK 2) && rhoTau.all (lettersK 2)

theorem rhoOK : rhoK = true := by quickRfl

theorem rho_parts : szOK 45 6 = true ∧
    allN 3 (fun j => permOK 45 6 (mask 6) (45 * 6) (XY45 j) (XYI j)) = true ∧
    (∀ j < 2, permOK 45 6 (mask 6) (45 * 6) (T2 j) (T2I j) = true ∧ cn45 (T2 j) = true ∧
      cn45 (XY45 j) = true) ∧
    (∀ j < 2, Nat.beq (wordK 45 6 (mask 6) (pidn 45 6) XY45 XYI (rhoXY.getD j [])) (T2 j) = true) ∧
    (∀ j < 2, Nat.beq (wordK 45 6 (mask 6) (pidn 45 6) T2 T2I (rhoTau.getD j [])) (XY45 j) = true) ∧
    (∀ x ∈ tauWords, lettersK 3 x = true) ∧ (∀ x ∈ rhoXY, lettersK 2 x = true) ∧
    (∀ x ∈ rhoTau, lettersK 2 x = true) := by
  have h := rhoOK
  unfold rhoK at h
  simp only [Bool.and_eq_true, and_assoc, List.all_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, fun j hj => ?_, fun j hj => allN_spec h4 j hj, fun j hj => allN_spec h5 j hj,
    h6, h7, h8⟩
  have := allN_spec h3 j hj
  simp only [Bool.and_eq_true, and_assoc] at this
  exact this

theorem xy_eq : ∀ j < 3, xyfArr[j]! = unpack 45 6 (XY45 j) := by
  intro j hj
  interval_cases j <;> decide +kernel

theorem xyf_bind : xyfArr.size = 3 ∧ ∀ j < 3, xyfArr[j]! = unpack 45 6 (XY45 j) :=
  ⟨rfl, xy_eq⟩

theorem tau_get {k : Nat} (hk : k < 10) : (tauArrs ())[k]! = unpack 45 6 (TK k) := by
  unfold tauArrs
  rw [get_ofFn _ hk]
  have hl : lettersK 3 (tauWords.getD k []) = true := by
    interval_cases k <;> exact rho_parts.2.2.2.2.2.1 _ (by simp [tauWords])
  exact wordG_eq xyf_bind rho_parts.2.1 rho_parts.1 hl

theorem X_bind : (Array.ofFn (n := 2) fun j => xyfArr[j.val]!).size = 2 ∧
    ∀ j < 2, (Array.ofFn (n := 2) fun j => xyfArr[j.val]!)[j]! = unpack 45 6 (XY45 j) := by
  refine ⟨by simp, fun j hj => ?_⟩
  rw [get_ofFn _ hj]
  exact xy_eq j (by omega)

theorem T_bind : (Array.ofFn (n := 2) fun j => (tauArrs ())[j.val + 1]!).size = 2 ∧
    ∀ j < 2, (Array.ofFn (n := 2) fun j => (tauArrs ())[j.val + 1]!)[j]! = unpack 45 6 (T2 j) := by
  refine ⟨by simp, fun j hj => ?_⟩
  rw [get_ofFn _ hj]
  exact tau_get (by omega)

theorem permX2 : allN 2 (fun j => permOK 45 6 (mask 6) (45 * 6) (XY45 j) (XYI j)) = true :=
  allN_of_forall fun j hj => allN_spec rho_parts.2.1 j (by omega)

theorem permT2 : allN 2 (fun j => permOK 45 6 (mask 6) (45 * 6) (T2 j) (T2I j)) = true :=
  allN_of_forall fun j hj => (rho_parts.2.2.1 j hj).1

theorem rho_unfold : checkRho () =
    (rhoXY.length == 2 && rhoTau.length == 2 && rhoXY.all (lettersOK 2) && rhoTau.all (lettersOK 2) &&
      allLt 2 (fun j => isInvA 45 (Array.ofFn (n := 2) fun j => xyfArr[j.val]!)[j]!
        (Array.ofFn (n := 2) fun j => invCand 45 (Array.ofFn (n := 2) fun j => xyfArr[j.val]!)[j.val]!)[j]!) &&
      allLt 2 (fun j => isInvA 45 (Array.ofFn (n := 2) fun j => (tauArrs ())[j.val + 1]!)[j]!
        (Array.ofFn (n := 2) fun j =>
          invCand 45 (Array.ofFn (n := 2) fun j => (tauArrs ())[j.val + 1]!)[j.val]!)[j]!) &&
      allLt 2 (fun j => eqA 45 (wordA 45 (Array.ofFn (n := 2) fun j => xyfArr[j.val]!)
        (Array.ofFn (n := 2) fun j => invCand 45 (Array.ofFn (n := 2) fun j => xyfArr[j.val]!)[j.val]!)
        (rhoXY.getD j [])) (Array.ofFn (n := 2) fun j => (tauArrs ())[j.val + 1]!)[j]!) &&
      allLt 2 (fun j => eqA 45 (wordA 45 (Array.ofFn (n := 2) fun j => (tauArrs ())[j.val + 1]!)
        (Array.ofFn (n := 2) fun j =>
          invCand 45 (Array.ofFn (n := 2) fun j => (tauArrs ())[j.val + 1]!)[j.val]!)
        (rhoTau.getD j [])) (Array.ofFn (n := 2) fun j => xyfArr[j.val]!)[j]!)) :=
  rfl

theorem rho : checkRho () = true := by
  rw [rho_unfold, ofFn_inv _ X_bind.1, ofFn_inv _ T_bind.1]
  have hl : (rhoXY.length == 2 && rhoTau.length == 2 && rhoXY.all (lettersOK 2) &&
      rhoTau.all (lettersOK 2)) = true := by decide +kernel
  have inv_get : ∀ (S : Array (Array Nat)) (j : Nat), j < S.size →
      (rawInvs 45 S)[j]! = invCand 45 S[j]! := by
    intro S j hj
    rw [getElem!_pos _ j (by simpa [rawInvs] using hj), getElem!_pos S j hj]
    simp [rawInvs]
  simp only [Bool.and_eq_true] at hl ⊢
  refine ⟨⟨⟨⟨hl, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    rw [inv_get _ j (by rw [X_bind.1]; exact hj)]
    exact Fi22E2067.isInv_of (X_bind.2 j hj) (allN_spec permX2 j hj)
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    rw [inv_get _ j (by rw [T_bind.1]; exact hj)]
    exact Fi22E2067.isInv_of (T_bind.2 j hj) (allN_spec permT2 j hj)
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    have hl' : lettersK 2 (rhoXY.getD j []) = true := by
      interval_cases j <;> exact rho_parts.2.2.2.2.2.2.1 _ (by simp [rhoXY])
    rw [wordG_eq X_bind permX2 rho_parts.1 hl', T_bind.2 j hj,
      eqA_unpack ?_ (rho_parts.2.2.1 j hj).2.1]
    · exact rho_parts.2.2.2.1 j hj
    · rw [Nat.eq_of_beq_eq_true (rho_parts.2.2.2.1 j hj)]
      exact (rho_parts.2.2.1 j hj).2.1
  · rw [CFSG.Monster.B.Co2.allLt_iff]
    intro j hj
    have hl' : lettersK 2 (rhoTau.getD j []) = true := by
      interval_cases j <;> exact rho_parts.2.2.2.2.2.2.2 _ (by simp [rhoTau])
    rw [wordG_eq T_bind permT2 rho_parts.1 hl', X_bind.2 j hj,
      eqA_unpack ?_ (rho_parts.2.2.1 j hj).2.2]
    · exact rho_parts.2.2.2.2.1 j hj
    · rw [Nat.eq_of_beq_eq_true (rho_parts.2.2.2.2.1 j hj)]
      exact (rho_parts.2.2.1 j hj).2.2

end CertificateChecks.KernelSpor.Perf450108

end
