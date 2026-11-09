module

public import Certificates.Kernel.OmegaEight.SB3884
public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchL2Cent
public import Mathlib.Data.List.Sort

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3884

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871
  CertificateChecks.KernelO8.SB3872 CertificateChecks.KernelO8.SB3873

theorem vRange_hiB : List.range' 65536 65536 =
    ((List.range 8).map fun s => List.range' (65536 + 8192 * s) 8192).flatten := by
  rw [List.range'_eq_map_range, show (65536 : ℕ) = 8192 * 8 from rfl, range_mul_eq_flatMap,
    List.map_flatMap, List.flatMap_def]
  simp only [List.map_add_range']

@[expose] noncomputable def vFK (k m a : ℕ) : ℕ :=
  strictN (Nat.shiftRight a 7) fun g => strictN (sNfRow g) fun r =>
    strictN (Nat.mul 16 (Nat.land a 127)) fun o =>
    strictN fld(r, o, 127) fun e => strictN fld(r, Nat.add o 7, 511) fun p =>
      mulK (WK k m e) (LK k p)

@[expose] noncomputable def vMKh (k m z c : ℕ) : ℕ :=
  strictN (c - 65536) fun a => mulK (mulK a (vFK k m a)) z

theorem vMKh_eq {k m z c : ℕ} (h1 : 65536 ≤ c) (h2 : c < 131072) :
    MK k m z c c = vMKh k m z c := by
  have hc : ¬ c < 65536 := by omega
  have ha : c - 65536 < 65536 := by omega
  unfold vMKh vFK
  simp only [strictN_eq', MK, extMul, ite_eq_right hc, FK, nfEK, nfAK, nfEG, nfAG, nIf_blt, ite_eq_left ha]

@[expose] noncomputable def vMKw (k m c : ℕ) : ℕ :=
  strictN (c - 65536) fun a => mulK a (vFK k m a)

theorem vMKh_eq_w (k m z c : ℕ) : vMKh k m z c = mulK (vMKw k m c) z := by
  unfold vMKh vMKw
  simp only [strictN_eq']

theorem vMKw_lt (k m c : ℕ) : vMKw k m c < 65536 := by
  unfold vMKw
  rw [strictN_eq']
  exact mulK_lt _ _

theorem codeIso_right_cancel {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ}
    (Φ : CodeIso H N mul) {y w z : ℕ} (hy : y < N) (hw : w < N) (hz : z < N)
    (h : mul y z = mul w z) : y = w := by
  have e := Φ.inj (a₁ := Φ.g y * Φ.g z) (a₂ := Φ.g w * Φ.g z)
    (by rw [Φ.map_mul, Φ.map_mul, Φ.f_g hy, Φ.f_g hw, Φ.f_g hz, h])
  rw [← Φ.f_g hy, ← Φ.f_g hw, mul_right_cancel e]

theorem mulK_beq_zero {y w z : ℕ} (hy : y < 65536) (hw : w < 65536) (hz : z < 65536)
    (hwz : mulK w z = 0) : (mulK y z == 0) = (y == w) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  exact ⟨fun h => codeIso_right_cancel ΦK hy hw hz (h.trans hwz.symm), fun h => h ▸ hwz⟩

theorem mulK_24_24 : mulK 24 24 = 0 := by decide +kernel

theorem kInv_of_hiB {k m z : ℕ} {rows : List (List ℕ)} (hlen : rows.length = 16)
    (hlo : (rows.take 8).flatten = sInvListLit)
    (h' : ∀ s < 8, ((List.range' (65536 + 8192 * s) 8192).filter
      fun c => vMKh k m z c == 0 && c != 0) = rows.getD (8 + s) []) :
    kInv (MK k m z) 131072 = rows.flatten := by
  have h : ∀ s < 8, ((List.range' (65536 + 8192 * s) 8192).filter
      fun c => MK k m z c c == 0 && c != 0) = rows.getD (8 + s) [] := by
    intro s hs
    rw [← h' s hs]
    refine List.filter_congr fun c hc => ?_
    have hc' := List.mem_range'_1.1 hc
    rw [vMKh_eq (by omega) (by omega)]
  have hr : List.range 131072 = List.range 65536 ++ List.range' 65536 65536 := by
    rw [List.range'_eq_map_range, ← List.range_add]
  have hl : (List.range 65536).filter (fun c => MK k m z c c == 0 && c != 0) =
      (rows.take 8).flatten := by
    rw [hlo, ← kInv_eq]
    unfold kInv
    refine List.filter_congr fun c hc => ?_
    have hc' : c < 65536 := List.mem_range.1 hc
    simp only [MK, extMul, ite_eq_left hc']
  have hh : (List.range' 65536 65536).filter (fun c => MK k m z c c == 0 && c != 0) =
      (rows.drop 8).flatten := by
    rw [vRange_hiB]
    refine filter_blocks _ _ _ (by simp [hlen]) fun s hs => ?_
    simp only [List.length_map, List.length_range] at hs
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hs, Option.map_some,
      Option.getD_some, h s hs, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_drop]
  unfold kInv
  rw [hr, List.filter_append, hl, hh, ← List.flatten_append, List.take_append_drop]

theorem kInv_of_hiW {k m z w : ℕ} {rows : List (List ℕ)} (hlen : rows.length = 16)
    (hlo : (rows.take 8).flatten = sInvListLit) (hw : w < 65536) (hz : z < 65536)
    (hwz : mulK w z = 0)
    (h' : ∀ s < 8, ((List.range' (65536 + 8192 * s) 8192).filter
      fun c => vMKw k m c == w && c != 0) = rows.getD (8 + s) []) :
    kInv (MK k m z) 131072 = rows.flatten :=
  kInv_of_hiB hlen hlo fun s hs => by
    rw [← h' s hs]
    refine List.filter_congr fun c _ => ?_
    rw [vMKh_eq_w, mulK_beq_zero (vMKw_lt k m c) hw hz hwz]

theorem vRecSum (G : ℕ → ℕ) (k : ℕ) :
    Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (G l) ih2) k =
      ((List.range k).map G).sum := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change G k + Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 => Nat.add (G l) ih2) k = _
    rw [ih, List.range_succ, List.map_append, List.sum_append, List.map_singleton,
      List.sum_singleton, Nat.add_comm]

theorem vSumBelow (m : ℕ) (f : ℕ → ℕ) : ∀ hi, CFSG.KC.Loop.sumBelow m hi f =
    ((List.range (64 * hi)).map fun i => if i < m then f i else 0).sum
  | 0 => rfl
  | h + 1 => by
    have sel : ∀ (b : Bool) (x : ℕ), Bool.rec (motive := fun _ => ℕ) 0 x b =
        if b = true then x else 0 := by
      intro b x
      cases b <;> rfl
    change Nat.rec (motive := fun _ => ℕ) 0 (fun l ih2 =>
      Nat.add ((fun i => Bool.rec (motive := fun _ => ℕ) 0 (f i) (Nat.blt i m))
        (Nat.add (Nat.shiftLeft h 6) l)) ih2) 64 + CFSG.KC.Loop.sumBelow m h f = _
    rw [vRecSum, vSumBelow m f h, Nat.mul_succ, List.range_add, List.map_append,
      List.sum_append, List.map_map, Nat.add_comm (List.sum (List.map _ (List.range 64)))]
    refine Nat.add_left_cancel_iff.2 (congrArg List.sum (List.map_congr_left fun l _ => ?_))
    have e : Nat.add (Nat.shiftLeft h 6) l = 64 * h + l := by
      change h <<< 6 + l = 64 * h + l
      rw [Nat.shiftLeft_eq]
      omega
    simp only [Function.comp_apply, e, sel, Nat.blt_eq]

theorem vSumBelowCnt (p : ℕ → Bool) {m hi : ℕ} (hm : m = 64 * hi) :
    CFSG.KC.Loop.sumBelow m hi (fun i => nIf(p i, 1, 0)) = ((List.range m).filter p).length := by
  rw [vSumBelow, ← hm]
  have key : ∀ l : List ℕ, (∀ i ∈ l, i < m) →
      (l.map fun i => if i < m then Bool.rec (motive := fun _ => ℕ) 0 1 (p i) else 0).sum =
        (l.filter p).length := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a t ih =>
      intro hl
      rw [List.map_cons, List.sum_cons, ih fun i hi => hl i (List.mem_cons_of_mem _ hi),
        ite_eq_left (hl a List.mem_cons_self), List.filter_cons]
      cases hpa : p a <;> simp [Nat.add_comm]
  exact key _ fun i hi => List.mem_range.1 hi

@[expose] noncomputable def vBlkOK (p : ℕ → Bool) (b : ℕ) (l : List ℕ) : Bool :=
  ((l.zip l.tail).all fun q => decide (q.1 < q.2)) &&
    (l.all fun x => decide (b ≤ x) && decide (x < b + 8192) && p x) &&
    Nat.beq (CFSG.KC.Loop.sumBelow 8192 128 fun i => nIf(p (Nat.add b i), 1, 0)) l.length

theorem filter_of_vBlkOK {p : ℕ → Bool} {b : ℕ} {l : List ℕ} (h : vBlkOK p b l = true) :
    (List.range' b 8192).filter p = l := by
  unfold vBlkOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, Nat.beq_eq] at h
  obtain ⟨⟨hs, hm⟩, hc⟩ := h
  have hc' : ((List.range' b 8192).filter p).length = l.length := by
    rw [← hc, vSumBelowCnt (fun i => p (Nat.add b i)) (by rfl), List.range'_eq_map_range,
      List.filter_map, List.length_map]
    rfl
  have hpw : l.Pairwise (· < ·) := List.isChain_iff_pairwise.1 (chain_of_zip_tail' hs)
  have hpf : ((List.range' b 8192).filter p).Pairwise (· < ·) :=
    (List.pairwise_lt_range' (s := b) (n := 8192)).filter _
  have hsub : l ⊆ (List.range' b 8192).filter p := fun x hx =>
    List.mem_filter.2 ⟨List.mem_range'_1.2 ⟨(hm x hx).1.1, (hm x hx).1.2⟩, (hm x hx).2⟩
  exact ((List.sublist_of_subperm_of_pairwise (r := (· ≤ ·)) (hpw.nodup.subperm hsub)
    (hpw.imp Nat.le_of_lt) (hpf.imp Nat.le_of_lt)).eq_of_length hc'.symm).symm

@[expose] noncomputable def vHit (k m w c : ℕ) : Bool := c != 0 && vMKw k m c == w

theorem kInv_of_hiC {k m z w : ℕ} {rows : List (List ℕ)} (hlen : rows.length = 16)
    (hlo : (rows.take 8).flatten = sInvListLit) (hw : w < 65536) (hz : z < 65536)
    (hwz : mulK w z = 0)
    (h' : ∀ s < 8, vBlkOK (vHit k m w) (65536 + 8192 * s) (rows.getD (8 + s) []) = true) :
    kInv (MK k m z) 131072 = rows.flatten :=
  kInv_of_hiW hlen hlo hw hz hwz fun s hs => by
    rw [← filter_of_vBlkOK (h' s hs)]
    exact List.filter_congr fun c _ => by rw [vHit, Bool.and_comm]

@[expose] noncomputable def vHiP (c dh : ℕ) : ℕ :=
  strictN (Nat.land (Nat.shiftRight c 7) 511) fun g => fld(sMtRow g, Nat.mul 9 dh, 511)

theorem hi_split {L H : ℕ} (hL : L < 128) (hH : H < 512) :
    Nat.land (Nat.shiftRight (Nat.add L (Nat.mul 128 H)) 7) 511 = H := by
  rw [l511, shr_eq]
  change (L + 128 * H) / 128 % 512 = H
  omega

theorem mulK_hi (c d : ℕ) :
    Nat.land (Nat.shiftRight (mulK c d) 7) 511 = vHiP c (Nat.land (Nat.shiftRight d 7) 511) := by
  have h127 : ∀ x, Nat.land x 127 < 2 ^ 7 := fun x => by
    rw [l127]
    exact Nat.mod_lt _ (by norm_num)
  have h511 : ∀ x, Nat.land x 511 < 512 := fun x => by
    rw [l511]
    exact Nat.mod_lt _ (by norm_num)
  unfold mulK sMulG vHiP
  simp only [strictN_eq']
  exact hi_split (Nat.xor_lt_two_pow (h127 _) (h127 _)) (h511 _)

@[expose] noncomputable def vPreW (k m c : ℕ) : ℕ :=
  strictN (c - 65536) fun a => strictN (Nat.shiftRight a 7) fun g => strictN (sNfRow g) fun r =>
    strictN (Nat.mul 16 (Nat.land a 127)) fun o =>
    strictN fld(r, o, 127) fun e => strictN fld(r, Nat.add o 7, 511) fun p =>
      vHiP a (vHiP (WK k m e) (Nat.land (Nat.shiftRight (LK k p) 7) 511))

theorem vPreW_eq (k m c : ℕ) : vPreW k m c = Nat.land (Nat.shiftRight (vMKw k m c) 7) 511 := by
  unfold vPreW vMKw vFK
  simp only [strictN_eq', mulK_hi]

theorem vMKw_pre (k m c w : ℕ) : (vMKw k m c == w) =
    (Nat.beq (vPreW k m c) (Nat.land (Nat.shiftRight w 7) 511) && (vMKw k m c == w)) := by
  by_cases h : vMKw k m c = w
  · rw [vPreW_eq, h, Nat.beq_refl, Bool.true_and]
  · rw [beq_eq_false_iff_ne.2 h, Bool.and_false]

theorem vHiP_eq (c dh : ℕ) :
    vHiP c dh = fld(sMtRow (Nat.land (Nat.shiftRight c 7) 511), Nat.mul 9 dh, 511) :=
  strictN_eq' _ _

theorem vPreW_row {k m g j : ℕ} (hg : g < 512) (hj : j < 128) :
    vPreW k m (Nat.add (Nat.add 65536 (Nat.mul 128 g)) j) =
      fld(sMtRow g, Nat.mul 9 (vHiP (WK k m fld(sNfRow g, Nat.mul 16 j, 127))
        (Nat.land (Nat.shiftRight (LK k fld(sNfRow g, Nat.add (Nat.mul 16 j) 7, 511)) 7) 511)),
        511) := by
  have ha : Nat.add (Nat.add 65536 (Nat.mul 128 g)) j - 65536 = 128 * g + j := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  have h1 : Nat.shiftRight (128 * g + j) 7 = g := by
    rw [shr_eq]
    change (128 * g + j) / 128 = g
    omega
  have h2 : Nat.land (128 * g + j) 127 = j := by
    rw [l127]
    omega
  have h3 : Nat.land g 511 = g := by
    rw [l511]
    omega
  rw [vPreW]
  simp only [strictN_eq', ha, h1, h2]
  rw [vHiP_eq (128 * g + j), h1, h3]

@[expose] noncomputable def vRowCnt (k m w g : ℕ) : ℕ :=
  (fun MR r => Nat.rec (motive := fun _ => ℕ) 0 (fun j ih => Nat.add
    (strictN (Nat.mul 16 j) fun o => strictN fld(r, o, 127) fun e =>
      strictN fld(r, Nat.add o 7, 511) fun p =>
      nIf(Nat.beq fld(MR, Nat.mul 9 (vHiP (WK k m e) (Nat.land (Nat.shiftRight (LK k p) 7) 511)),
          511) (Nat.land (Nat.shiftRight w 7) 511) &&
        (vMKw k m (Nat.add (Nat.add 65536 (Nat.mul 128 g)) j) == w), 1, 0)) ih) 128)
    (sMtRow g) (sNfRow g)

theorem vRowCnt_eq {k m w g : ℕ} (hg : g < 512) :
    vRowCnt k m w g = ((List.range 128).map fun j =>
      nIf(vHit k m w (Nat.add (Nat.add 65536 (Nat.mul 128 g)) j), 1, 0)).sum := by
  unfold vRowCnt
  beta_reduce
  rw [vRecSum]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have hj' := List.mem_range.1 hj
  have hne : (Nat.add (Nat.add 65536 (Nat.mul 128 g)) j != 0) = true := by
    rw [bne_iff_ne]
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  simp only [strictN_eq']
  rw [vHit, hne, Bool.true_and, ← vPreW_row hg hj', ← vMKw_pre]

theorem vRowCnt_hit {k m w g b t : ℕ} (hg : g < 512)
    (hb : Nat.add 65536 (Nat.mul 128 g) = Nat.add b (128 * t)) :
    vRowCnt k m w g =
      ((List.range 128).map fun j => nIf(vHit k m w (Nat.add b (128 * t + j)), 1, 0)).sum := by
  rw [vRowCnt_eq hg]
  refine congrArg List.sum (List.map_congr_left fun j _ => ?_)
  have e : Nat.add (Nat.add 65536 (Nat.mul 128 g)) j = Nat.add b (128 * t + j) := by
    rw [hb]
    simp only [Nat.add_eq]
    omega
  rw [e]

@[expose] noncomputable def vBlkCnt (k m w g0 : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0
    (fun t ih => Nat.add (strictN (Nat.add g0 t) (vRowCnt k m w)) ih) 64

theorem vBlkCnt_gen (R : ℕ → ℕ) (P : ℕ → Bool) (g0 b : ℕ)
    (hR : ∀ t < 64, R (Nat.add g0 t) =
      ((List.range 128).map fun j => nIf(P (Nat.add b (128 * t + j)), 1, 0)).sum) :
    Nat.rec (motive := fun _ => ℕ) 0 (fun t ih => Nat.add (strictN (Nat.add g0 t) R) ih) 64 =
      CFSG.KC.Loop.sumBelow 8192 128 fun i => nIf(P (Nat.add b i), 1, 0) := by
  have e64 : 64 * 128 = 128 * 64 := rfl
  rw [vRecSum, vSumBelow, e64, range_mul_eq_flatMap, List.flatMap_def, List.map_flatten,
    List.sum_flatten, List.map_map, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  simp only [Function.comp_apply, strictN_eq']
  rw [hR t (List.mem_range.1 ht), List.range'_eq_map_range, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have hlt : 128 * t + j < 8192 := by
    have := List.mem_range.1 hj
    have := List.mem_range.1 ht
    omega
  simp only [Function.comp_apply]
  rw [ite_eq_left hlt]

theorem vBlkCnt_eq {k m w s : ℕ} (hs : s < 8) :
    vBlkCnt k m w (64 * s) = CFSG.KC.Loop.sumBelow 8192 128
      fun i => nIf(vHit k m w (Nat.add (65536 + 8192 * s) i), 1, 0) := by
  unfold vBlkCnt
  refine vBlkCnt_gen (vRowCnt k m w) (vHit k m w) (64 * s) (65536 + 8192 * s) fun t ht => ?_
  refine vRowCnt_hit ?_ ?_
  · simp only [Nat.add_eq]
    omega
  · simp only [Nat.add_eq, Nat.mul_eq]
    omega

@[expose] noncomputable def vBlkOKR (k m w s : ℕ) (l : List ℕ) : Bool :=
  ((l.zip l.tail).all fun q => decide (q.1 < q.2)) &&
    (l.all fun x => decide (65536 + 8192 * s ≤ x) && decide (x < 65536 + 8192 * s + 8192) &&
      vHit k m w x) &&
    Nat.beq (vBlkCnt k m w (64 * s)) l.length

theorem vBlkOKR_eq {k m w s : ℕ} (hs : s < 8) (l : List ℕ) :
    vBlkOKR k m w s l = vBlkOK (vHit k m w) (65536 + 8192 * s) l := by
  rw [vBlkOKR, vBlkOK, vBlkCnt_eq hs]

theorem kInv_of_hiR {k m z w : ℕ} {rows : List (List ℕ)} (hlen : rows.length = 16)
    (hlo : (rows.take 8).flatten = sInvListLit) (hw : w < 65536) (hz : z < 65536)
    (hwz : mulK w z = 0) (h' : ∀ s < 8, vBlkOKR k m w s (rows.getD (8 + s) []) = true) :
    kInv (MK k m z) 131072 = rows.flatten :=
  kInv_of_hiC hlen hlo hw hz hwz fun s hs => (vBlkOKR_eq hs _).symm.trans (h' s hs)

end CertificateChecks.KernelO8.SB3884

end
