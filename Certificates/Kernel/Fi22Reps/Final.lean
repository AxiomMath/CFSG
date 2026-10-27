module

public import Certificates.Kernel.Fi22Reps.Words
public import Certificates.Kernel.Fi22Reps.Tabs
public import Certificates.Kernel.Fi22Reps.Lev
public import Certificates.Kernel.Fi22Reps.LevB
public import Certificates.Kernel.Fi22Reps.Scan
public import Certificates.Kernel.Fi22Reps.Sep
public import Certificates.Kernel.Fi22Cls.Final
public import CFSG.Certificates.Kernel.Fi22Reps.Sound
public import CFSG.Sporadic.Fi22.Transpositions
public import CFSG.Certificates.Kernel.Common.ForallTree
import Mathlib

public section

namespace CertificateChecks.KernelFi22Reps

open CFSG.KC.Enum CFSG.KC.Fi22S0 CFSG.KC.Fi22Cls CFSG.KC.Fi22Reps CFSG.KD.Fi22Reps
  CertificateChecks.KernelFi22S0 CertificateChecks.KernelFi22Cls
open CFSG.KD.Fi22S0 (sB_eq bRec_and blt_iff beq_iff RepE rep_reg pk5)
open CFSG.Sporadic.Fi22 (J a b conjPt D mem_D_iff conjPt_inj orb_size)
open CFSG.Sporadic.Th (idx idx_lt idx_of_lt)
open CFSG.HardMathSupport.Foote.E27 (tabElt)
open CFSG.HardMathSupport.Foote.E27.Fi22S0 (gJ regJ regJ_zero regJ_one regJ_two)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three (xRep xRep_def)

#kc_forall_tree ch13621wordAll (fun q => ch13621word q = true) 26
  CertificateChecks.KernelFi22Reps.ch13621word

#kc_forall_tree ch13621xtAll (fun k => ch13621xt k = true) 4 CertificateChecks.KernelFi22Reps.ch13621xt

#kc_forall_tree ch13621parAll (fun k => ch13621par k = true) 4
  CertificateChecks.KernelFi22Reps.ch13621par

#kc_forall_tree ch13621phiAll (fun k => ch13621phi k = true) 4
  CertificateChecks.KernelFi22Reps.ch13621phi

#kc_forall_tree ch13621fixAll (fun k => ch13621fix k = true) 4
  CertificateChecks.KernelFi22Reps.ch13621fix

#kc_forall_tree ch13621levAll (fun q => ch13621lev q = true) 35
  CertificateChecks.KernelFi22Reps.ch13621lev

#kc_forall_tree ch13621levbAll (fun q => ch13621levb q = true) 7
  CertificateChecks.KernelFi22Reps.ch13621levb

#kc_forall_tree ch13621scanAll (fun q => ch13621scan q = true) 7
  CertificateChecks.KernelFi22Reps.ch13621scan

#kc_forall_tree ch13621sepAll (fun q => ch13621sep q = true) 21
  CertificateChecks.KernelFi22Reps.ch13621sep

theorem bcontra {c : Bool} (h1 : c = false) (h2 : c = true) : False := by
  rw [h1] at h2
  exact Bool.false_ne_true h2

theorem regRep : ∀ k < 570, RepE (RF k) (regJ k) :=
  rep_reg (A := CFSG.Sporadic.Fi22.Native.orbEntry 0) (B := CFSG.Sporadic.Fi22.Native.orbEntry 1)
    (fun x hx => CFSG.KD.SporCovBase.Fi22.hA x hx) (fun x hx => CFSG.KD.SporCovBase.Fi22.hB x hx)
    ch131101base_eq regAll opsAll

theorem LTRep : ∀ c, RepE (LT c) (letJ c) := by
  intro c
  rcases c with _ | _ | c
  · have h := regRep 0 (by norm_num)
    rw [regJ_zero] at h
    have e : letJ 0 = a := by simp [letJ]
    rw [e]
    exact h
  · have h := regRep 1 (by norm_num)
    rw [regJ_one] at h
    have e : letJ 1 = b := by simp [letJ]
    rw [e]
    exact h
  · have h := regRep 2 (by norm_num)
    rw [regJ_two] at h
    have e : letJ (c + 2) = b⁻¹ := by simp [letJ]
    rw [e]
    exact h

theorem wordAll : ∀ v < 3510, wordC LT wd v = true := fun v hv =>
  blk_all (b := 135) (m := 26) (by norm_num) (f := wordC LT wd) ch13621wordAll v (by omega)

theorem parFacts {k : ℕ} (hk : k < 4) :
    nd k (dep k) = glob k ∧ 0 < dep k ∧ 0 < nLev k ∧
    (∀ m < nF k, Nat.land (Nat.shiftRight (P k m) 12) 3 = 0) ∧
    (∀ t < 5, bp k t < nP k ∧ ptE (P k (bp k t)) = bsP t) ∧ ln (lv0 k) = nF k ∧
    ∀ i < nLev k, lk (lv0 k + i) = k ∧ (i + 1 < nLev k → ln (lv0 k + i) < ln (lv0 k + i + 1)) ∧
      (¬i + 1 < nLev k → ln (lv0 k + i) < nP k) := by
  have h := ch13621parAll k hk
  unfold ch13621par at h
  simp only [bRec_and, Bool.and_eq_true, blt_iff, beq_iff] at h
  obtain ⟨-, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h2, h3, h4, fun m hm => (beq_iff _ _).1 (CFSG.KS.allN_spec h5 m hm), fun t ht => ?_, h7,
    fun i hi => ?_⟩
  · have h9 := CFSG.KS.allN_spec h6 t ht
    simp only [sB_eq, bRec_and, Bool.and_eq_true, blt_iff, beq_iff] at h9
    exact h9
  · have h9 := CFSG.KS.allN_spec h8 i hi
    simp only [sB_eq, bRec_and, Bool.and_eq_true, blt_iff, beq_iff] at h9
    obtain ⟨h10, -, h11⟩ := h9
    refine ⟨h10, fun hi1 => ?_, fun hi1 => ?_⟩
    · rcases bIf_cases h11 with ⟨-, h12⟩ | ⟨hc, -⟩
      · exact (blt_iff _ _).1 h12
      · exact (bcontra hc ((blt_iff _ _).2 hi1)).elim
    · rcases bIf_cases h11 with ⟨hc, -⟩ | ⟨-, h12⟩
      · exact absurd ((blt_iff _ _).1 hc) hi1
      · exact (blt_iff _ _).1 h12

theorem ln_lt_nP {k : ℕ} (hk : k < 4) : ∀ u < nLev k, ln (lv0 k + u) < nP k := by
  obtain ⟨-, -, -, -, -, -, hlevs⟩ := parFacts hk
  have key : ∀ d u, u + d = nLev k → u < nLev k → ln (lv0 k + u) < nP k := by
    intro d
    induction d with
    | zero => intro u hud hu; omega
    | succ d ih =>
      intro u hud hu
      by_cases h1 : u + 1 < nLev k
      · exact lt_trans ((hlevs u hu).2.1 h1) (ih (u + 1) (by omega) h1)
      · exact (hlevs u hu).2.2 h1
  exact fun u hu => key (nLev k - u) u (by omega) hu

theorem rep_xT {k : ℕ} (hk : k < 4) : RepE (xT k) (xRep k) := by
  obtain ⟨hend, hdep, -⟩ := parFacts hk
  have hxt : ∀ t < dep k, xtC XF gR pp pj (nd k) (xs k) (t + 1) = true :=
    CFSG.KS.allN_spec (ch13621xtAll k hk)
  have h := rep_path gRAll parG hxt (by rw [hend]; exact glob_lt k hk) (dep k - 1) (by omega)
  rw [Nat.sub_add_cancel hdep, hend, ← glob_eq k hk, ← xRep_def] at h
  have e : xT k = XF (xs k + (dep k - 1)) := by
    unfold xT
    congr 1
    change xs k + dep k - 1 = xs k + (dep k - 1)
    omega
  rw [e]
  exact h

theorem lvBound : ∀ k < 4, lv0 k + nLev k ≤ 7 := by decide +kernel

theorem levRows {lv : ℕ} (hlv : lv < 7) :
    ∀ w < 3510, levC LT wd (xT (lk lv)) (P (lk lv)) (cd lv) (cl lv) (cb lv) (ln lv) (ls lv) (f1 lv)
      (f2 lv) w = true := by
  have key : ∀ r < 5, blkC 702 (levC LT wd (xT (lk lv)) (P (lk lv)) (cd lv) (cl lv) (cb lv) (ln lv)
      (ls lv) (f1 lv) (f2 lv)) r = true := by
    intro r hr
    have h := ch13621levAll (5 * lv + r) (by change 5 * lv + r < 35; omega)
    unfold ch13621lev at h
    simp only [sB_eq] at h
    have e1 : Nat.div (5 * lv + r) (nat_lit 5) = lv := by
      change (5 * lv + r) / 5 = lv
      omega
    have e2 : Nat.mod (5 * lv + r) (nat_lit 5) = r := by
      change (5 * lv + r) % 5 = r
      omega
    rw [e1, e2] at h
    exact h
  exact fun w hw => blk_all (b := 702) (m := 5) (by norm_num) key w (by omega)

theorem card_fixG_xRep {k : ℕ} (hk : k < 4) :
    Nat.card (fixG (xRep k) fun _ => False) ≤ ∏ u ∈ Finset.range (nLev k), ls (lv0 k + u) := by
  obtain ⟨-, -, hL0, htag, hbase, hln, hlevs⟩ := parFacts hk
  have hX := rep_xT hk
  have hphi : ∀ m < nP k, phiC LT wd (xT k) (P k) (fun u => ln (lv0 k + u)) (nLev k) m = true :=
    CFSG.KS.allN_spec (ch13621phiAll k hk)
  have hlk : ∀ u < nLev k, lk (lv0 k + u) = k := fun u hu => (hlevs u hu).1
  have hlv : ∀ u < nLev k, lv0 k + u < 7 := fun u hu => by have := lvBound k hk; omega
  refine card_fixG_le (P := P k) (nL := fun u => ln (lv0 k + u)) (s := fun u => ls (lv0 k + u))
    (f1 := fun u => f1 (lv0 k + u)) (f2 := fun u => f2 (lv0 k + u))
    (cd := fun u => cd (lv0 k + u)) (cl := fun u => cl (lv0 k + u)) (cb := fun u => cb (lv0 k + u))
    (L := nLev k) (nP := nP k) (bpos := bp k) LTRep wordAll hX hphi ?_ hL0 ?_ ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Nat.add_zero] at hj
    have h0 := ln_lt_nP hk 0 hL0
    rw [Nat.add_zero] at h0
    rw [hln] at hj h0
    exact phi_tag0 (hphi j (by omega)) (htag j hj)
  · intro u hu
    exact (hlevs u (by omega)).2.1 hu
  · exact ln_lt_nP hk _ (by omega)
  · intro t ht
    obtain ⟨h1, h2⟩ := hbase t ht
    refine ⟨h1, ?_⟩
    rw [h2]
    interval_cases t <;> rfl
  · intro u hu w hw
    have h := levRows (hlv u hu) w hw
    rw [hlk u hu] at h
    exact h
  · intro u hu m hm
    have h := ch13621levbAll (lv0 k + u) (hlv u hu)
    unfold ch13621levb at h
    simp only [sB_eq] at h
    rw [hlk u hu] at h
    exact CFSG.KS.allN_spec h m hm
  · intro u hu p hp
    have h := ch13621scanAll (lv0 k + u) (hlv u hu)
    unfold ch13621scan at h
    simp only [sB_eq] at h
    rw [hlk u hu] at h
    exact CFSG.KS.allN_spec h p hp

theorem prod0 : ∏ u ∈ Finset.range (nLev 0), ls (lv0 0 + u) = 34992 := by decide +kernel

theorem prodK : ∀ k ∈ [1, 2, 3], ∏ u ∈ Finset.range (nLev k), ls (lv0 k + u) = 3 := by
  decide +kernel

theorem fixAll {k : ℕ} (hk : k < 4) : ∀ w < 3510, fixC (xT k) (P k) (fp k) (nF k) w = true :=
  CFSG.KS.allN_spec (ch13621fixAll k hk)

theorem nF0 : nF 0 = 0 := by decide +kernel

theorem smul_val (g : J) {v : ℕ} (hv : v < 3510) : idx 3510 g v = (g • (⟨v, hv⟩ : Fin 3510)).val :=
  idx_of_lt g hv

theorem xRep_zero_smul_ne (v : Fin 3510) : xRep 0 • v ≠ v := by
  intro h
  have hX := rep_xT (k := 0) (by norm_num)
  have h0 := fixAll (k := 0) (by norm_num)
  rw [nF0] at h0
  exact fpf_of hX h0 v.2 (by rw [smul_val _ v.2]; exact congrArg Fin.val h)

theorem card_centralizer_xRep_zero_le :
    Nat.card (Subgroup.centralizer ({xRep 0} : Set J)) ≤ 34992 := by
  have e : Subgroup.centralizer ({xRep 0} : Set J) = fixG (xRep 0) fun _ => False := by
    ext h
    rw [Subgroup.mem_centralizer_singleton_iff, mem_fixG]
    refine ⟨fun hc => ⟨hc, fun v hv hx => absurd ?_ (xRep_zero_smul_ne ⟨v, hv⟩), fun v hv => hv.elim⟩,
      fun hc => hc.1⟩
    exact Fin.ext (by rw [← smul_val _ hv]; exact hx)
  rw [e]
  exact (card_fixG_xRep (by norm_num)).trans_eq prod0

theorem card_centralizer_fix_le {k : ℕ} (hk : k ∈ [1, 2, 3]) :
    Nat.card {g : J // g ∈ Subgroup.centralizer ({xRep k} : Set J) ∧
      ∀ v : Fin 3510, xRep k • v = v → g • v = v} ≤ 3 := by
  have hk4 : k < 4 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  have e : Nat.card {g : J // g ∈ Subgroup.centralizer ({xRep k} : Set J) ∧
      ∀ v : Fin 3510, xRep k • v = v → g • v = v} = Nat.card (fixG (xRep k) fun _ => False) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
    rw [Subgroup.mem_centralizer_singleton_iff, mem_fixG]
    constructor
    · rintro ⟨hc, hf⟩
      refine ⟨hc, fun v hv hx => ?_, fun v hv => hv.elim⟩
      rw [smul_val _ hv] at hx ⊢
      rw [hf ⟨v, hv⟩ (Fin.ext hx)]
    · rintro ⟨hc, hf, -⟩
      refine ⟨hc, fun v hx => Fin.ext ?_⟩
      have := hf v.val v.2 (by rw [smul_val _ v.2]; exact congrArg Fin.val hx)
      rwa [smul_val _ v.2] at this
  rw [e]
  exact (card_fixG_xRep hk4).trans_eq (prodK k hk)

@[expose] noncomputable def sepK (q : Nat) : Nat :=
  nIf(Nat.blt q (nat_lit 3), nat_lit 1, nIf(Nat.blt q (nat_lit 7), nat_lit 2, nat_lit 3))

@[expose] noncomputable def sepR (q : Nat) : Nat :=
  nIf(Nat.blt q (nat_lit 3), q, nIf(Nat.blt q (nat_lit 7), Nat.sub q (nat_lit 3), Nat.sub q (nat_lit 7)))

theorem sepBlocks : ∀ k ∈ [1, 2, 3], ∀ m < nF k, sepC LT wd (P k) (sw k) (nF k) m = true := by
  have hrow : ∀ k : ℕ, (∀ m < nF k, Nat.blt m (nF k) = true →
      sepC LT wd (P k) (sw k) (nF k) m = true) → ∀ m < nF k, sepC LT wd (P k) (sw k) (nF k) m = true :=
    fun k h m hm => h m hm ((blt_iff _ _).2 hm)
  have hb : ∀ k : ℕ, ∀ c : ℕ, nF k = 9 * c → (∀ r < c, blkC 9 (fun m =>
      Bool.rec (motive := fun _ => Bool) false (sepC LT wd (P k) (sw k) (nF k) m) (Nat.blt m (nF k)))
      r = true) → ∀ m < nF k, sepC LT wd (P k) (sw k) (nF k) m = true := by
    intro k c hc h
    refine hrow k fun m hm hb => ?_
    have h1 := blk_all (b := 9) (m := c) (by norm_num) h m (by omega)
    rcases bIf_cases h1 with ⟨-, h2⟩ | ⟨hc', -⟩
    · exact h2
    · exact (bcontra hc' hb).elim
  have hq : ∀ q < 21, blkC 9 (fun m => Bool.rec (motive := fun _ => Bool) false
      (sepC LT wd (P (sepK q)) (sw (sepK q)) (nF (sepK q)) m) (Nat.blt m (nF (sepK q))))
      (sepR q) = true := by
    intro q hq
    have h := ch13621sepAll q hq
    unfold ch13621sep at h
    simp only [sB_eq] at h
    exact h
  have hk1 : ∀ r < 3, sepK r = 1 ∧ sepR r = r := by decide +kernel
  have hk2 : ∀ r < 4, sepK (r + 3) = 2 ∧ sepR (r + 3) = r := by decide +kernel
  have hk3 : ∀ r < 14, sepK (r + 7) = 3 ∧ sepR (r + 7) = r := by decide +kernel
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · refine hb 1 3 (by decide +kernel) fun r hr => ?_
    have h := hq r (by omega)
    rw [(hk1 r hr).1, (hk1 r hr).2] at h
    exact h
  · refine hb 2 4 (by decide +kernel) fun r hr => ?_
    have h := hq (r + 3) (by omega)
    rw [(hk2 r hr).1, (hk2 r hr).2] at h
    exact h
  · refine hb 3 14 (by decide +kernel) fun r hr => ?_
    have h := hq (r + 7) (by omega)
    rw [(hk3 r hr).1, (hk3 r hr).2] at h
    exact h

theorem commute_iff_fix {x : J} {i : ℕ} (hi : i < 3510) :
    conjPt i * x = x * conjPt i ↔ idx 3510 x i = i := by
  have e := conjPt_idx (g := x) hi
  constructor
  · intro h
    have h' : x * conjPt i * x⁻¹ = conjPt i := by rw [← h, mul_inv_cancel_right]
    rw [h'] at e
    exact conjPt_inj (by rw [orb_size]; exact idx_lt _ hi) (by rw [orb_size]; exact hi) e
  · intro h
    rw [h] at e
    calc conjPt i * x = x * conjPt i * x⁻¹ * x := by rw [← e]
      _ = x * conjPt i := by group

theorem sep_xRep {k : ℕ} (hk : k ∈ [1, 2, 3]) :
    ∀ d ∈ D, d * xRep k = xRep k * d → ∀ d' ∈ D, d' * xRep k = xRep k * d' → d ≠ d' →
      d * d' = d' * d → ∃ e ∈ D, e * xRep k = xRep k * e ∧ e * d' = d' * e ∧ e * d ≠ d * e := by
  have hk4 : k < 4 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega
  obtain ⟨-, -, -, htag, -, hln, hlevs⟩ := parFacts hk4
  have hX := rep_xT hk4
  have hphi : ∀ m < nP k, phiC LT wd (xT k) (P k) (fun u => ln (lv0 k + u)) (nLev k) m = true :=
    CFSG.KS.allN_spec (ch13621phiAll k hk4)
  have hFP : nF k < nP k := by
    obtain ⟨-, -, hL0, -⟩ := parFacts hk4
    have h0 := ln_lt_nP hk4 0 hL0
    rw [Nat.add_zero, hln] at h0
    exact h0
  have hPl : ∀ m < nF k, ptE (P k m) < 3510 := fun m hm =>
    (phi_cases (hphi m (by omega))).1
  have hPx : ∀ m < nF k, idx 3510 (xRep k) (ptE (P k m)) = ptE (P k m) := fun m hm => by
    have := phi_tag0 (hphi m (by omega)) (htag m hm)
    rwa [repE_iff.1 hX _ (hPl m hm)] at this
  intro d hd hdx d' hd' hdx' hne hdd'
  obtain ⟨i, hi, rfl⟩ := mem_D_iff.1 hd
  obtain ⟨j, hj, rfl⟩ := mem_D_iff.1 hd'
  have hij : i ≠ j := fun e => hne (by rw [e])
  obtain ⟨e, he, hxe, h1, h2⟩ := sep_of LTRep wordAll hX (fixAll hk4) (sepBlocks k hk) hPl hPx hi hj
    ((commute_iff_fix hi).1 hdx) ((commute_iff_fix hj).1 hdx') hij hdd'
  exact ⟨conjPt e, mem_D_iff.2 ⟨e, he, rfl⟩, (commute_iff_fix he).2 hxe, h1, h2⟩

theorem exists_orderOf_four_comm : ∃ t : J, orderOf t = 4 ∧ t * xRep 0 = xRep 0 * t :=
  ord4_of letRep k0_eq (rep_xT (by norm_num)) ch13621ord_eq

end CertificateChecks.KernelFi22Reps

end
