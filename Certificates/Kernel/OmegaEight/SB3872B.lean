module

public import Certificates.Kernel.OmegaEight.SB3872
public import Certificates.Kernel.OmegaEight.SB3872FData
public import Certificates.Kernel.OmegaEight.SB3872BData
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSAut

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3872

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
open KFacts

@[expose] def fL (k i : ℕ) : List (List ℕ) := (fLit.getD k []).getD i []

@[expose] def fStep (k i : ℕ) (acc : List (List ℕ)) : List (List ℕ) :=
  acc.flatMap fun ds => ((sAutData.R k i).filter fun d =>
    sAutData.relOK sMul sInv k i (ds ++ [d])).map fun d => ds ++ [d]

@[expose] def bkLhs (k i j : ℕ) (ds : List ℕ) : ℕ :=
  if j < i then cconj sMul sInv (sAutData.ys sMul k ds i) (sAutData.ys sMul k ds j)
  else sMul (sAutData.ys sMul k ds i) (sAutData.ys sMul k ds i)

@[expose] def bkRhs (k i j : ℕ) (ds : List ℕ) : ℕ :=
  sMul (wprodN sMul i (sAutData.ys sMul k ds) (sAutData.relE i j))
    (sAutData.K.lin (sAutData.Pk k (sAutData.relA i j)))

theorem bkRelOK_eq (k i : ℕ) (ds : List ℕ) : sAutData.relOK sMul sInv k i ds =
    (List.range (i + 1)).all fun j => bkLhs k i j ds == bkRhs k i j ds := rfl

@[expose] def bkQ (k i j d : ℕ) : ℕ :=
  if j < i then
    sMul (sInv (cconj sMul sInv (sMul (sAutData.h k i) (sAutData.K.lin 0))
      (sMul (sAutData.h k j) (sAutData.K.lin 0))))
      (cconj sMul sInv (sMul (sAutData.h k i) (sAutData.K.lin d))
        (sMul (sAutData.h k j) (sAutData.K.lin 0)))
  else
    sMul (sInv (sMul (sMul (sAutData.h k i) (sAutData.K.lin 0))
      (sMul (sAutData.h k i) (sAutData.K.lin 0))))
      (sMul (sMul (sAutData.h k i) (sAutData.K.lin d)) (sMul (sAutData.h k i) (sAutData.K.lin d)))

@[expose] def bkT (k i j : ℕ) (ds : List ℕ) : ℕ :=
  sMul (sInv (bkLhs k i j (ds ++ [0]))) (bkRhs k i j (ds ++ [0]))

@[expose] def bkNJ (i : ℕ) : ℕ := min (i + 1) 2

@[expose] def bkKey (k i d : ℕ) : List ℕ := (List.range (bkNJ i)).map fun j => bkQ k i j d

@[expose] def bkTgt (k i : ℕ) (ds : List ℕ) : List ℕ :=
  (List.range (bkNJ i)).map fun j => bkT k i j ds

@[expose] def bkTab (k i : ℕ) : List (List ℕ × List ℕ) := (bkLit.getD k []).getD i []

@[expose] def bkBkt (k i : ℕ) (t : List ℕ) : List ℕ :=
  (((bkTab k i).find? fun p => p.1 == t).map Prod.snd).getD []

@[expose] def bkOK (k i : ℕ) : Bool :=
  ((sAutData.R k i).all fun d => (bkBkt k i (bkKey k i d)).contains d) &&
  ((bkTab k i).all fun p => decide (p.2.Pairwise (· < ·)) &&
    p.2.all fun d => decide (d < 512) && ((sCanon[k * 7 + i]!)[d]!).2 == d)

@[expose] def fLOK (k i : ℕ) : Bool :=
  (fL k i).all fun ds => ds.length == i && (List.range i).all fun l => decide (ds.getD l 0 < 512)

@[expose] def fStepB (k i : ℕ) (acc : List (List ℕ)) : List (List ℕ) :=
  acc.flatMap fun ds => ((bkBkt k i (bkTgt k i ds)).filter fun d =>
    sAutData.relOK sMul sInv k i (ds ++ [d])).map fun d => ds ++ [d]

theorem bk_conj_split {H : Type*} [Group H] (a b x z : H)
    (hc : x * (b * z * b⁻¹) = b * z * b⁻¹ * x) :
    a * x * (b * z) * (a * x)⁻¹ =
      a * (b * z) * a⁻¹ * ((a * b * a⁻¹)⁻¹ * (a * x * b * (a * x)⁻¹)) := by
  calc a * x * (b * z) * (a * x)⁻¹ = a * (x * (b * z * b⁻¹)) * b * x⁻¹ * a⁻¹ := by group
    _ = a * (b * z * b⁻¹ * x) * b * x⁻¹ * a⁻¹ := by rw [hc]
    _ = _ := by group

theorem bk_code {H : Type*} [Group H] (Φ : CodeIso H 65536 sMul) {k i j : ℕ} (hk : k < 8)
    (hi : i < 7) (hji : j < i) {z d : ℕ} (hz : z < 512) (hd : d < 512) :
    sMul (sInv (cconj sMul sInv (sMul (sAutData.h k i) (sAutData.K.lin 0))
      (sMul (sAutData.h k j) (sAutData.K.lin 0))))
      (cconj sMul sInv (sMul (sAutData.h k i) (sAutData.K.lin d))
        (sMul (sAutData.h k j) (sAutData.K.lin 0))) =
    sMul (sInv (cconj sMul sInv (sMul (sAutData.h k i) (sAutData.K.lin 0))
      (sMul (sAutData.h k j) (sAutData.K.lin z))))
      (cconj sMul sInv (sMul (sAutData.h k i) (sAutData.K.lin d))
        (sMul (sAutData.h k j) (sAutData.K.lin z))) := by
    have hF := sAutFacts sMul_zero_zero
    have hn : (2 : ℕ) ^ sAutData.K.n = 512 := rfl
    have hq : sAutData.q = 7 := rfl
    obtain ⟨A, hA⟩ : ∃ A, Φ.f A = sAutData.h k i := Φ.surj _ (hF.h_lt k hk i (by omega))
    obtain ⟨B, hB⟩ : ∃ B, Φ.f B = sAutData.h k j := Φ.surj _ (hF.h_lt k hk j (by omega))
    have hl : ∀ v, v < 512 → sAutData.K.lin v = Φ.f (el Φ sAutData.K v) := fun v hv =>
      (hF.kf.f_el Φ (by rw [hn]; exact hv)).symm
    have hmul : ∀ x y : H, sMul (Φ.f x) (Φ.f y) = Φ.f (x * y) := fun x y => (Φ.map_mul x y).symm
    have hinv : ∀ x : H, sInv (Φ.f x) = Φ.f x⁻¹ := fun x =>
      (Φ.f_inv sMul_zero_zero (inv_spec hF.inv_ok (Φ.lt x)).1 (inv_spec hF.inv_ok (Φ.lt x)).2).symm
    have hcj : ∀ x y : H, cconj sMul sInv (Φ.f x) (Φ.f y) = Φ.f (x * y * x⁻¹) := fun x y =>
      (hF.f_conj' Φ x y).symm
    have hlin0 : sAutData.K.lin 0 = Φ.f 1 := by
      rw [hl 0 (by norm_num), hF.el_zero Φ]
    obtain ⟨X, hX, hXm⟩ : ∃ X, sAutData.K.lin d = Φ.f X ∧ Mem Φ sAutData.K X :=
      ⟨_, hl d hd, hF.el_mem Φ (by rw [hn]; exact hd)⟩
    obtain ⟨Z, hZ, hZm⟩ : ∃ Z, sAutData.K.lin z = Φ.f Z ∧ Mem Φ sAutData.K Z :=
      ⟨_, hl _ hz, hF.el_mem Φ (by rw [hn]; exact hz)⟩
    have hc : X * (B * Z * B⁻¹) = B * Z * B⁻¹ * X :=
      hF.kf.mem_comm Φ hXm (AutFacts.mem_conj Φ (D := sAutData) (sChar Φ) hZm B)
    simp only [← hA, ← hB, hlin0, hX, hZ, hmul, hcj, hinv]
    refine congrArg Φ.f ?_
    rw [bk_conj_split A B X Z hc]
    group

theorem bkQ_eq {k i j : ℕ} (hk : k < 8) (hi : i < 7) {ds : List ℕ}
    (hlen : ds.length = i) (hds : ∀ l < i, ds.getD l 0 < 512) {d : ℕ} (hd : d < 512)
    (h : bkLhs k i j (ds ++ [d]) = bkRhs k i j (ds ++ [d])) : bkQ k i j d = bkT k i j ds := by
  have hgi : ∀ e, (ds ++ [e]).getD i 0 = e := fun e => by
    simp [List.getD_eq_getElem?_getD, hlen]
  have hgl : ∀ e l, l < i → (ds ++ [e]).getD l 0 = ds.getD l 0 := fun e l hl => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (hlen ▸ hl : l < ds.length)]
  have hr : bkRhs k i j (ds ++ [d]) = bkRhs k i j (ds ++ [0]) := by
    unfold bkRhs
    rw [wprodN_congr sMul (ys := sAutData.ys sMul k (ds ++ [d])) (zs := sAutData.ys sMul k (ds ++ [0]))
      (fun l hl => by simp only [ys_fun, hgl _ _ hl])]
  have hyi : ∀ e, sAutData.ys sMul k (ds ++ [e]) i = sMul (sAutData.h k i) (sAutData.K.lin e) :=
    fun e => by simp only [ys_fun, hgi]
  unfold bkQ bkT
  rw [← hr, ← h]
  unfold bkLhs
  by_cases hji : j < i
  · simp only [hji, ↓reduceIte, hyi]
    have hyj : ∀ e, sAutData.ys sMul k (ds ++ [e]) j =
        sMul (sAutData.h k j) (sAutData.K.lin (ds.getD j 0)) :=
      fun e => by simp only [ys_fun, hgl _ _ hji]
    simp only [hyj]
    exact bk_code SModel.codeIso hk hi hji (hds j hji) hd
  · simp only [hji, ↓reduceIte, hyi]

theorem relOK_key {k i : ℕ} (hk : k < 8) (hi : i < 7) {ds : List ℕ} (hlen : ds.length = i)
    (hds : ∀ l < i, ds.getD l 0 < 512) {d : ℕ} (hd : d < 512)
    (h : sAutData.relOK sMul sInv k i (ds ++ [d]) = true) : bkKey k i d = bkTgt k i ds := by
  rw [bkRelOK_eq, List.all_eq_true] at h
  unfold bkKey bkTgt
  refine List.map_congr_left fun j hj => ?_
  have hj' : j < bkNJ i := List.mem_range.1 hj
  have hji : j ≤ i := by
    unfold bkNJ at hj'
    omega
  exact bkQ_eq hk hi hlen hds hd (beq_iff_eq.1 (h j (List.mem_range.2 (by omega))))

theorem mem_bkR {k i d : ℕ} :
    d ∈ sAutData.R k i ↔ d < 512 ∧ ((sCanon[k * 7 + i]!)[d]!).2 = d := by
  simp only [sAutData, List.mem_filter, List.mem_range, beq_iff_eq]

theorem bkR_pairwise (k i : ℕ) : (sAutData.R k i).Pairwise (· < ·) := by
  simp only [sAutData]
  exact List.pairwise_lt_range.filter _

theorem bkBkt_spec {k i : ℕ} (hB : bkOK k i = true) (t : List ℕ) :
    (bkBkt k i t).Pairwise (· < ·) ∧ ∀ d ∈ bkBkt k i t, d ∈ sAutData.R k i := by
  unfold bkOK at hB
  rw [Bool.and_eq_true] at hB
  unfold bkBkt
  cases hf : (bkTab k i).find? fun p => p.1 == t with
  | none => simp
  | some p =>
    have hp := List.all_eq_true.1 hB.2 p (List.mem_of_find?_eq_some hf)
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hp
    simp only [Option.map_some, Option.getD_some]
    exact ⟨hp.1, fun d hd => mem_bkR.2 (hp.2 d hd)⟩

theorem fLOK_spec {k i : ℕ} (h : fLOK k i = true) :
    ∀ ds ∈ fL k i, ds.length = i ∧ ∀ l < i, ds.getD l 0 < 512 := by
  intro ds hds
  have h1 := List.all_eq_true.1 h ds hds
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h1
  exact h1

theorem fStep_eqB {k i : ℕ} (hk : k < 8) (hi : i < 7) (hB : bkOK k i = true)
    {acc : List (List ℕ)} (hacc : ∀ ds ∈ acc, ds.length = i ∧ ∀ l < i, ds.getD l 0 < 512) :
    fStep k i acc = fStepB k i acc := by
  unfold fStep fStepB
  refine List.flatMap_congr fun ds hds => congrArg (List.map _) ?_
  obtain ⟨hlen, hlt⟩ := hacc ds hds
  obtain ⟨hs, hsub⟩ := bkBkt_spec hB (bkTgt k i ds)
  rw [bkOK, Bool.and_eq_true] at hB
  have h1 := List.all_eq_true.1 hB.1
  refine List.Pairwise.eq_of_mem_iff ((bkR_pairwise k i).filter _) (hs.filter _) fun d => ?_
  simp only [List.mem_filter]
  constructor
  · rintro ⟨hd, hrel⟩
    refine ⟨?_, hrel⟩
    have hkey := relOK_key hk hi hlen hlt (mem_bkR.1 hd).1 hrel
    have h2 := h1 d hd
    rw [hkey] at h2
    simpa using h2
  · rintro ⟨hd, hrel⟩
    exact ⟨hsub d hd, hrel⟩

theorem fStep_of {k : ℕ} (hk : k < 8) (hB : ∀ i < 7, bkOK k i = true)
    (hL : ∀ i < 7, fLOK k i = true) (hS : ∀ i < 7, fStepB k i (fL k i) = fL k (i + 1)) :
    ∀ i < 7, fStep k i (fL k i) = fL k (i + 1) := fun i hi =>
  (fStep_eqB hk hi (hB i hi) (fLOK_spec (hL i hi))).trans (hS i hi)

end CertificateChecks.KernelO8.SB3872

end
