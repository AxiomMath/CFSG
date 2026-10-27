
module

public import Certificates.Kernel.Sporadic.L2.Defs
public import Certificates.Kernel.Sporadic.Q3A.Glue
public import CFSG.Certificates.Kernel.Spor.FpBfsSound
public import CFSG.Sporadic.SuzRecog.LevelTwoDefsBase
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3B0Model
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import Certificates.Certificate15088Base

public section

namespace CertificateChecks.KernelSpor.L2G

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.FpBfs
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwo CFSG.Sporadic.SuzRecog.LevelTwoData
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.L2K
open CertificateChecks.KernelSpor.SuzTwCF (P p_comp eqA_P pidn_P)

local notation "pgk" => pg 11 (mask 11)
local notation "pgv" => pg 12 (mask 12)
local notation "pc" => pcomp 1782 11 (mask 11)
local notation "cn" => canonK 1782 11 (mask 11) (1782 * 11)

theorem sB (y : Nat) (k : Nat → Bool) : strictB y k = k y := by cases y <;> rfl

theorem band (a b : Bool) : bAnd(a, b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem bif_true {c t e : Bool} : bIf(c, t, e) = true ↔ (c = true → t = true) ∧ (c = false → e = true) := by
  cases c <;> simp

theorem nbeq {a b : Nat} : Nat.beq a b = true ↔ a = b := ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem nblt {a b : Nat} : Nat.blt a b = true ↔ a < b := by rw [Nat.blt_eq]

theorem nble {a b : Nat} : Nat.ble a b = true ↔ a ≤ b := by rw [Nat.ble_eq]

theorem nblt_f {a b : Nat} (h : ¬ a < b) : Nat.blt a b = false :=
  Bool.eq_false_iff.2 fun e => h (nblt.1 e)

theorem nble_f {a b : Nat} (h : ¬ a ≤ b) : Nat.ble a b = false :=
  Bool.eq_false_iff.2 fun e => h (nble.1 e)

theorem allN_get {n : Nat} {f : Nat → Bool} (h : allN n f = true) {i : Nat} (hi : i < n) :
    f i = true := CFSG.KS.allN_spec h i hi

theorem allBlk_get {b len : Nat} {f : Nat → Bool} (h : allBlk b f len = true) {i : Nat}
    (h1 : b ≤ i) (h2 : i < b + len) : f i = true := by
  have := CFSG.KS.allBlk_spec h (i - b) (by omega)
  have e : Nat.add b (i - b) = i := by
    change b + (i - b) = i
    omega
  rwa [e] at this

theorem slices {f : Nat → Bool} {len k n : Nat} (hlen : 0 < len) (hn : n ≤ len * k)
    (h : ∀ s < k, allBlk (Nat.mul len s) f len = true) : ∀ i < n, f i = true := by
  intro i hi
  have hs : i / len < k := by
    rw [Nat.div_lt_iff_lt_mul hlen]
    rw [Nat.mul_comm] at hn
    omega
  exact allBlk_get (h (i / len) hs) (by change len * (i / len) ≤ i; exact Nat.mul_div_le i len)
    (by change i < len * (i / len) + len; have := Nat.lt_mul_div_succ i hlen; rw [Nat.mul_succ] at this; omega)

theorem hexE {cs : List Char} {s : String} {d n w N : Nat} {F : Nat → Nat}
    (hs : s = String.ofList cs) (h : CFSG.KC.Misc.HexFlat.hexFlat cs d n w N F = true)
    {j e : Nat} (hj : j < N) (he : e < n) :
    hexAt s.toUTF8 (d * (n * j + e)) d = pg w (mask w) (F j) e := by
  have h1 := CFSG.KC.Misc.HexFlat.hexTable_sound h j hj
  rw [← hs] at h1
  have h2 := congrArg (fun a : Array Nat => a[e]!) h1
  rw [Q3AG.hexTable_get he, CFSG.KC.HeFixK.unpack_getElem! he] at h2
  exact h2

theorem hexTable_at {s : String} {d n k0 i : Nat} (hi : i < n) :
    (hexTable d n k0 s)[i]! = hexAt s.toUTF8 (d * (k0 + i)) d := Q3AG.hexTable_get hi

theorem aPar_get {i : Nat} (hi : i < 2835) : aPar[i]! = aParK i := by
  unfold aPar
  rw [hexTable_at hi, show 0 + i = 2835 * 0 + i by omega]
  exact hexE L2TA.eq L2TA.all (by norm_num) hi

theorem aLab_get {i : Nat} (hi : i < 2835) : aLab[i]! = aLabK i := by
  unfold aLab
  rw [hexTable_at hi, show 2835 + i = 2835 * 1 + i by omega]
  exact hexE L2TA.eq L2TA.all (by norm_num) hi

theorem wPar_get {j : Nat} (hj : j < 162) : wPar[j]! = wParK j := by
  unfold wPar
  rw [hexTable_at hj, show 0 + j = 162 * 0 + j by omega]
  exact hexE L2TW.eq L2TW.all (by norm_num) hj

theorem wLab_get {j : Nat} (hj : j < 162) : wLab[j]! = wLabK j := by
  unfold wLab
  rw [hexTable_at hj, show 162 + j = 162 * 1 + j by omega]
  exact hexE L2TW.eq L2TW.all (by norm_num) hj

theorem getElem!_map_g {α β : Type} [Inhabited α] [Inhabited β] {L : Array α} (f : α → β)
    {i : Nat} (hi : i < L.size) : (L.map f)[i]! = f L[i]! := by
  rw [getElem!_pos (L.map f) i (by simpa using hi), Array.getElem_map, getElem!_pos L i hi]

theorem getElem!_map_range {α : Type} [Inhabited α] {f : Nat → α} {n i : Nat} (hi : i < n) :
    ((Array.range n).map f)[i]! = f i := by
  rw [getElem!_map_g f (by simpa using hi)]
  simp [Array.getElem!_eq_getD, hi]

theorem gens_get {s : Nat} (hs : s < 2) : gens[s]! = CFSG.Sporadic.SuzRecog.Q3A.Check.xA s := by
  interval_cases s
  · simp [gens, CFSG.Sporadic.SuzRecog.Q3A.Check.xA, CFSG.Sporadic.SuzRecog.Q3A.Check.x1]
  · simp [gens, CFSG.Sporadic.SuzRecog.Q3A.Check.xA, CFSG.Sporadic.SuzRecog.Q3A.Check.x2]

theorem pG {s : Nat} (hs : s < 2) : P gens[s]! (XG s) := by
  rw [gens_get hs]
  exact Q3AG.pX hs

theorem pGI {s : Nat} (hs : s < 2) : P gensInv[s]! (XGI s) := by
  rw [gensInv_get hs, gens_get hs]
  exact (Q3AG.pXI hs).1

theorem pRho : P rhoArr RHO := SuzTwCF.pRho

theorem pRhoI : P rhoInv RHOI := Q3AG.pRhoI.1

theorem pT1 : P t1Arr T1 :=
  ⟨SuzInv.run_eq1 (k := 0) (by norm_num), CertificateChecks.KernelSpor.SuzWK.canT⟩

theorem pW0 : P w0Arr W0 := SuzTwCF.pW0

theorem p_conj {g gi a : Array Nat} {G GI A : Nat} (hg : P g G) (hgi : P gi GI) (ha : P a A) :
    P (conjA g gi a) (pc G (pc A GI)) := p_comp hg (p_comp ha hgi)

theorem p_of_eq {a : Array Nat} {A B : Nat} (ha : P a A) (h : B = A) : P a B := h ▸ ha

theorem aAt_eq (i : Nat) : aAt i =
    if 0 < i ∧ aPar[i]! < i then conjA gens[aLab[i]!]! gensInv[aLab[i]!]! (aAt aPar[i]!)
    else t1Arr := by
  rw [aAt]
  split_ifs <;> rfl

theorem aPts_get {i : Nat} (hi : i < 2835) : aPts[i]! = aAt i :=
  getElem!_map_range hi

theorem aPts_size : aPts.size = 2835 := by simp [aPts]

theorem aVt_parts {i : Nat} (h : aVt i = true) :
    (i = 0 → L2A 0 = T1) ∧ (0 < i → aParK i < i ∧ aLabK i < 2 ∧
      L2A i = pc (XG (aLabK i)) (pc (L2A (aParK i)) (XGI (aLabK i)))) ∧
    cn (L2A i) = true ∧ invEqK 1782 11 (mask 11) (1782 * 11) (L2A i) (L2A i) = true := by
  unfold aVt aStep at h
  rw [band, band, sB, sB] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun h0 => ?_, fun hp => ?_, h2, h3⟩
  · subst h0
    simpa [Nat.beq_refl, nbeq] using h1
  · have hz : Nat.beq i 0 = false := by
      cases i
      · omega
      · rfl
    rw [hz] at h1
    simp only [band, nblt, nbeq] at h1
    exact ⟨h1.1, h1.2.1, h1.2.2⟩

theorem pA (hv : ∀ i < 2835, aVt i = true) {i : Nat} (hi : i < 2835) : P aPts[i]! (L2A i) := by
  rw [aPts_get hi]
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    obtain ⟨h0, hstep, hc, -⟩ := aVt_parts (hv i hi)
    rw [aAt_eq]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp only [lt_irrefl, false_and, ↓reduceIte]
      exact p_of_eq pT1 (h0 rfl)
    · obtain ⟨hp, hl, he⟩ := hstep hpos
      rw [aPar_get hi, aLab_get hi]
      rw [if_pos ⟨hpos, hp⟩]
      exact p_of_eq (p_conj (pG hl) (pGI hl) (ih _ hp (by omega))) he

theorem wAt_eq (j : Nat) : wAt j =
    if 0 < j ∧ wPar[j]! < j then conjA gens[wLab[j]!]! gensInv[wLab[j]!]! (wAt wPar[j]!)
    else w0Arr := by
  rw [wAt]
  split_ifs <;> rfl

theorem wPts_get {j : Nat} (hj : j < 162) : wPts[j]! = wAt j :=
  getElem!_map_range hj

theorem wPts_size : wPts.size = 162 := by simp [wPts]

theorem tVt_parts {j : Nat} (h : tVt j = true) :
    (j = 0 → TK 0 0 = W0) ∧ (0 < j → wParK j < j ∧ wLabK j < 2 ∧
      TK j 0 = pc (XG (wLabK j)) (pc (TK (wParK j) 0) (XGI (wLabK j)))) ∧
    TK j 1 = pc RHO (pc (TK j 0) RHOI) ∧ TK j 2 = pc RHO (pc (TK j 1) RHOI) ∧
    (∀ k < 3, cn (TK j k) = true) ∧
    invEqK 1782 11 (mask 11) (1782 * 11) (TK j 0) (TK j 0) = true ∧ TK j 0 ≠ TK j 1 := by
  unfold tVt wStep at h
  simp only [band, sB, nbeq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun h0 => ?_, fun hp => ?_, h2, h3, fun k hk => allN_get h4 hk, h5, ?_⟩
  · subst h0
    simpa [Nat.beq_refl, nbeq] using h1
  · have hz : Nat.beq j 0 = false := by
      cases j
      · omega
      · rfl
    rw [hz] at h1
    simp only [band, nblt, nbeq] at h1
    exact ⟨h1.1, h1.2.1, h1.2.2⟩
  · intro he
    rw [he, Nat.beq_refl] at h6
    exact Bool.false_ne_true h6

theorem pW (hw : ∀ j < 162, tVt j = true) {j : Nat} (hj : j < 162) : P wPts[j]! (TK j 0) := by
  rw [wPts_get hj]
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    obtain ⟨h0, hstep, -, -, hc, -, -⟩ := tVt_parts (hw j hj)
    rw [wAt_eq]
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp only [lt_irrefl, false_and, ↓reduceIte]
      exact p_of_eq pW0 (h0 rfl)
    · obtain ⟨hp, hl, he⟩ := hstep hpos
      rw [wPar_get hj, wLab_get hj]
      rw [if_pos ⟨hpos, hp⟩]
      exact p_of_eq (p_conj (pG hl) (pGI hl) (ih _ hp (by omega))) he

theorem trip_eq {j : Nat} (hj : j < 162) : trip j = tripOf wPts[j]! := by
  unfold trip trips
  exact getElem!_map_g _ (by rw [wPts_size]; exact hj)

theorem tripOf_get0 (w : Array Nat) : (tripOf w)[0]! = w := by simp [tripOf]

theorem tripOf_get1 (w : Array Nat) : (tripOf w)[1]! = conjA rhoArr rhoInv w := by
  simp [tripOf, rhoConj]

theorem tripOf_get2 (w : Array Nat) :
    (tripOf w)[2]! = conjA rhoArr rhoInv (conjA rhoArr rhoInv w) := by
  simp [tripOf, rhoConj]

theorem pT (hw : ∀ j < 162, tVt j = true) {j k : Nat} (hj : j < 162) (hk : k < 3) :
    P (trip j)[k]! (TK j k) := by
  obtain ⟨-, -, h1, h2, -, -, -⟩ := tVt_parts (hw j hj)
  have h0 := pW hw hj
  rw [trip_eq hj]
  interval_cases k
  · rw [tripOf_get0]
    exact h0
  · rw [tripOf_get1]
    exact p_of_eq (p_conj pRho pRhoI h0) h1
  · rw [tripOf_get2]
    exact p_of_eq (p_conj pRho pRhoI (p_conj pRho pRhoI h0)) (by rw [h2, h1])

end CertificateChecks.KernelSpor.L2G

end
