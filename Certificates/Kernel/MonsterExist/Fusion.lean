module

public import CFSG.Monster.Existence.Census.CosetOneFusionInputs
public import Certificates.Kernel.MonsterExist.FusionWords
public import Certificates.Kernel.MonsterExist.FusionTab
public import CFSG.Monster.B.TwoA.Census.CosetEnumCheckInputs
public import CFSG.Monster.Existence.Census.FusionGensInputs
public import CFSG.Certificates.Kernel.WordRelK.PackHom
public import CFSG.Monster.AxisCount.DenseWord
public import CFSG.Monster.B.Rep4371.Conj

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CertificateChecks.MonsterExist.Fusion

open CFSG.Monster.Existence.Census CFSG.Monster.B.TwoA.Census CFSG.Monster.B CFSG.Monster.B.Rep4371
  CFSG.Monster.Visible CFSG.Monster.AxisCount CFSG.Monster.Spin CFSG.KC.WordRelK

@[expose] def imgsA : Array Model.Pauli := #[(false, 1, 60), (false, 2, 60), (false, 59, 3),
  (false, 55, 3), (false, 47, 3), (false, 31, 3), (true, 64, 128), (true, 128, 64),
  (true, 256, 512), (true, 512, 256), (false, 1024, 0), (false, 2048, 0), (false, 60, 61),
  (false, 60, 62), (false, 3, 56), (false, 3, 52), (false, 3, 44), (false, 3, 28), (false, 0, 64),
  (false, 0, 128), (false, 0, 256), (false, 0, 512), (false, 0, 1024), (false, 0, 2048)]

theorem imgs_one : imgs 1 = imgsA := by decide +kernel

@[expose] def walkA (w : List ℕ) (n : ℕ) : ℕ :=
  w.foldl (fun x k => Native.CosetEnum.act imgsA k x) n

@[expose] def walkOK (w : List ℕ) (r n : ℕ) : Bool := w.all (· < 24) && walkA w r == n

theorem exists_walk_of_walkOK {w : List ℕ} {r n : ℕ} (h : walkOK w r n = true) :
    ∃ w : List ℕ, w.all (· < 24) = true ∧ walkEnc w r = n := by
  rw [walkOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨w, h.1, by rw [walkEnc, imgs_one]; exact h.2⟩

@[expose] noncomputable def fusRowOK (j : ℕ) : Bool :=
  betaOf (fusGen j) (true, 0, 0) == (true, 0, 0) &&
    allBelow 24 fun k => unpackP (entryAt (rowAt FusT.n0 j) k) == betaOf (fusGen j) (basisP k)

@[expose] noncomputable def fusRowsOK : Bool := allBelow 11 fusRowOK

@[expose] noncomputable def fusFT (j n : ℕ) : ℕ :=
  Native.CosetEnum.enc (Model.Pauli.mul (unpackP (applyRow (rowAt FusT.n0 j) n)) (fusShift j))

theorem toSC_mul_of_conjQ {P : Pvis} {f : Model.Pauli → Model.Pauli}
    (hP : ∀ y, conjQ P (pauliQ y) = pauliQ (f y)) (x y : Model.Pauli) :
    toSC (f (x.mul y)) = toSC (f x) * toSC (f y) := by
  have hψ : ∀ y, ((spinEquiv.trans (conjQ P)).trans spinEquiv.symm) (toSC y) = toSC (f y) :=
    fun y => by
      change spinEquiv.symm (conjQ P (pauliQ y)) = _
      rw [hP]
      exact spinEquiv.symm_apply_apply _
  rw [← hψ (x.mul y), ← hψ x, ← hψ y, toSC_mul, map_mul]

theorem toSC_betaOf_mul {g : Native.Gen} (hg : g.validB = true) (x y : Model.Pauli) :
    toSC (betaOf g (x.mul y)) = toSC (betaOf g x) * toSC (betaOf g y) := by
  cases g with
  | rho q => exact toSC_mul_of_conjQ (conjQ_rhoPair_toQ q) x y
  | perm arr => exact toSC_mul_of_conjQ (conjQ_perm_toQ (permOf arr) (permOf_spec hg)) x y
  | sign a => exact toSC_mul_of_conjQ (conjQ_sign_toQ a) x y
  | xi => exact toSC_mul_of_conjQ conjQ_xi_toQ x y
  | tau => exact toSC_mul x y

theorem unpackP_sign_part {y : ℕ} (hy : y < 2 ^ 25) :
    unpackP (y / 16777216 * 16777216) = ((unpackP y).1, 0, 0) := by
  have h : y / 16777216 < 2 := by omega
  have hs : (unpackP y).1 = Nat.beq (y / 16777216 % 2) 1 := rfl
  rw [hs]
  generalize y / 16777216 = t at h
  interval_cases t <;> rfl

theorem toSC_applyRow_fus {j : ℕ} (hr : fusRowOK j = true) (hv : (fusGen j).validB = true)
    {y : ℕ} (hy : y < 2 ^ 25) :
    toSC (unpackP (applyRow (rowAt FusT.n0 j) y)) = toSC (betaOf (fusGen j) (unpackP y)) := by
  have hφ := toSC_betaOf_mul hv
  have hT : (betaOf (fusGen j) (true, 0, 0) == (true, 0, 0)) = true ∧
      allBelow 24 (fun k => unpackP (entryAt (rowAt FusT.n0 j) k) ==
        betaOf (fusGen j) (basisP k)) = true := by
    simpa only [fusRowOK, Bool.and_eq_true] using hr
  have hz : betaOf (fusGen j) (true, 0, 0) = (true, 0, 0) := beq_iff_eq.1 hT.1
  have he := allBelow_true hT.2
  have hs : toSC (unpackP (y / 16777216 * 16777216)) =
      toSC (betaOf (fusGen j) ((unpackP y).1, 0, 0)) := by
    rw [unpackP_sign_part hy]
    cases (unpackP y).1
    · exact (hom_one toSC toSC_mul).trans
        (hom_one (fun x => toSC (betaOf (fusGen j) x)) hφ).symm
    · rw [hz]
  have hl : ((List.range 24).map fun k =>
        if (y % 16777216).testBit k then
          toSC (unpackP (rowAt FusT.n0 j / 2 ^ (25 * k) % 33554432)) else 1) =
      (List.range 24).map fun k =>
        if (y % 16777216).testBit k then toSC (betaOf (fusGen j) (basisP k)) else 1 := by
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    have hek := beq_iff_eq.1 (he k hk)
    rw [entryAt, Nat.shiftRight_eq_div_pow] at hek
    cases (y % 16777216).testBit k
    · simp only [Bool.false_eq_true, ↓reduceIte]
    · simp only [↓reduceIte, hek]
  have hd := hom_unpackP_decomp (fun x => toSC (betaOf (fusGen j) x)) hφ y
  rw [applyRow_eq, applyN_spec toSC toSC_mul, hs, hl]
  exact hd.symm

theorem cosetEnc_lt (x : Model.Pauli) : Native.CosetEnum.enc x < 2 ^ 25 := by
  rcases x with ⟨s, a, d⟩
  have ha : a % 2 ^ 12 < 4096 := Nat.mod_lt a (by norm_num)
  have hd : d % 2 ^ 12 < 4096 := Nat.mod_lt d (by norm_num)
  have e : Native.CosetEnum.enc (s, a, d) =
      a % 2 ^ 12 + 4096 * (d % 2 ^ 12) + (if s then 16777216 else 0) := rfl
  rw [e]
  change _ < 33554432
  split <;> omega

theorem enc_mul_congr {x x' : Model.Pauli} (c : Model.Pauli) (h : toSC x = toSC x') :
    Native.CosetEnum.enc (x.mul c) = Native.CosetEnum.enc (x'.mul c) := by
  have h0 : pauliQ (x.mul c) = pauliQ (x'.mul c) :=
    congrArg spinEquiv (by rw [toSC_mul, toSC_mul, h])
  have h1 : qOfEnc (Native.CosetEnum.enc (x.mul c)) = qOfEnc (Native.CosetEnum.enc (x'.mul c)) := by
    rw [qOfEnc_enc, qOfEnc_enc]
    exact h0
  exact qOfEnc_injective (cosetEnc_lt _) (cosetEnc_lt _) h1

theorem unpackP_eq_pauliDec (n : ℕ) : unpackP n = pauliDec n := by
  unfold unpackP pauliDec
  rw [beq_div_mod]
  rfl

theorem fusFT_eq (hr : fusRowsOK = true) (hv : ∀ j < 11, (fusGen j).validB = true) {j : ℕ}
    (hj : j < 11) {n : ℕ} (hn : n < 2 ^ 25) : fusFT j n = fusF (fusGen j) (fusShift j) n := by
  have h := toSC_applyRow_fus (allBelow_true hr j hj) (hv j hj) hn
  rw [unpackP_eq_pauliDec n] at h
  exact enc_mul_congr _ h

@[expose] noncomputable def fixOK : Bool :=
  Nat.blt (classEnc 0) 33554432 && Nat.blt (classEnc 4) 33554432 &&
  (List.range 11).all fun j =>
    walkOK (fixWords.getD j ([], [])).1 (classEnc 0) (fusFT j (classEnc 0)) &&
      walkOK (fixWords.getD j ([], [])).2 (classEnc 4) (fusFT j (classEnc 4))

@[expose] noncomputable def tgtOK (j : ℕ) : Bool :=
  (List.range 137).all fun k => decide (fusTarget j k < 137) && Nat.blt (classEnc k) 33554432 &&
    walkOK ((tgtWords.getD j []).getD k []) (classEnc (fusTarget j k)) (fusFT j (classEnc k))

theorem fix_of_fixOK (hr : fusRowsOK = true) (hv : ∀ j < 11, (fusGen j).validB = true)
    (h : fixOK = true) : ∀ j < 11,
    (∃ w : List ℕ, w.all (· < 24) = true ∧
      walkEnc w (classEnc 0) = fusF (fusGen j) (fusShift j) (classEnc 0)) ∧
    (∃ w : List ℕ, w.all (· < 24) = true ∧
      walkEnc w (classEnc 4) = fusF (fusGen j) (fusShift j) (classEnc 4)) := by
  intro j hj
  rw [fixOK, Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h
  obtain ⟨⟨h0, h4⟩, h⟩ := h
  have h1 := List.all_eq_true.1 h j (List.mem_range.2 hj)
  rw [Bool.and_eq_true] at h1
  rw [← fusFT_eq hr hv hj (lt_of_lt_of_eq h0 (by norm_num)),
    ← fusFT_eq hr hv hj (lt_of_lt_of_eq h4 (by norm_num))]
  exact ⟨exists_walk_of_walkOK h1.1, exists_walk_of_walkOK h1.2⟩

theorem tgt_of_tgtOK (hr : fusRowsOK = true) (hv : ∀ j < 11, (fusGen j).validB = true) {j : ℕ}
    (hj : j < 11) (h : tgtOK j = true) : ∀ k < 137, fusTarget j k < 137 ∧
    ∃ w : List ℕ, w.all (· < 24) = true ∧
      walkEnc w (classEnc (fusTarget j k)) = fusF (fusGen j) (fusShift j) (classEnc k) := by
  intro k hk
  have h1 := List.all_eq_true.1 h k (List.mem_range.2 hk)
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, Nat.blt_eq] at h1
  obtain ⟨⟨h1, h2⟩, h3⟩ := h1
  rw [← fusFT_eq hr hv hj (lt_of_lt_of_eq h2 (by norm_num))]
  exact ⟨h1, exists_walk_of_walkOK h3⟩

end CertificateChecks.MonsterExist.Fusion
