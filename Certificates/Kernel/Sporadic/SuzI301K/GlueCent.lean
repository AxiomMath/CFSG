module

public import Certificates.Kernel.Sporadic.SuzI301K.GlueValid
public import CFSG.Certificates.Kernel.Spor.PK.Basic

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzI301K

open CFSG.KC.Enum CFSG.KC.LinRep CFSG.KC.LinRepSound CFSG.KC.LinRepCheck CFSG.KC.SuzI301Lin
open CFSG.KC.SuzI301K CFSG.KD.SuzI301 CFSG.PSL3Four.Native CFSG.Sporadic.SuzI301
  CFSG.ComponentClassification.AS81.SuzB0 CFSG.KC.BfsPin CertificateChecks.KernelLC CFSG.KS
  CFSG.KS.Raw

set_option exponentiation.threshold 512

@[expose] def tsum7 (f : Nat → Nat) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun v acc => Nat.add acc (Nat.shiftLeft (f v) (Nat.mul 7 v))) n

theorem tab7_eq (a : Nat) : tab7 a = tsum7 (appW a) 64 := rfl

theorem tsum7_succ (f : Nat → Nat) (n : Nat) : tsum7 f (n + 1) = tsum7 f n + f n * 2 ^ (7 * n) := by
  unfold tsum7
  change Nat.add _ ((f n) <<< (7 * n)) = _
  rw [Nat.shiftLeft_eq]
  rfl

theorem tsum7_lt (f : Nat → Nat) (hf : ∀ v, f v < 128) (n : Nat) : tsum7 f n < 2 ^ (7 * n) := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih =>
    have hp : 2 ^ (7 * (n + 1)) = 128 * 2 ^ (7 * n) := by
      rw [Nat.mul_succ, pow_add]
      ring
    rw [tsum7_succ, hp]
    have := hf n
    nlinarith

theorem tsum7_get (f : Nat → Nat) (hf : ∀ v, f v < 128) (n : Nat) :
    ∀ v < n, tsum7 f n / 2 ^ (7 * v) % 128 = f v := by
  induction n with
  | zero => intro v hv; omega
  | succ n ih =>
    intro v hv
    rw [tsum7_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hlt | rfl
    · have hn : 7 * n = 7 * v + 7 + 7 * (n - v - 1) := by omega
      have hk : f n * 2 ^ (7 * n) = 128 * (f n * 2 ^ (7 * (n - v - 1))) * 2 ^ (7 * v) := by
        rw [hn, pow_add, pow_add]
        ring
      rw [hk, Nat.add_mul_div_right _ _ (by positivity), Nat.add_mul_mod_self_left]
      exact ih v hlt
    · rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt (tsum7_lt f hf v), zero_add,
        Nat.mod_eq_of_lt (hf v)]

theorem tsum7_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ v < n, f v = g v) → tsum7 f n = tsum7 g n
  | 0, _ => rfl
  | n + 1, h => by
    rw [tsum7_succ, tsum7_succ, tsum7_congr (fun v hv => h v (by omega)), h n (by omega)]

theorem tsum7_mod (P : Nat) : ∀ n, tsum7 (fun v => P / 2 ^ (7 * v) % 128) n = P % 2 ^ (7 * n)
  | 0 => by
    rw [Nat.mul_zero, pow_zero, Nat.mod_one]
    rfl
  | n + 1 => by
    have h7 : (2 : Nat) ^ 7 = 128 := by norm_num
    rw [tsum7_succ, tsum7_mod P n, Nat.mul_succ, pow_add, Nat.mod_mul, h7]
    beta_reduce
    ring

theorem appW_lt128 (a v : Nat) : appW a v < 128 := Nat.lt_trans (appW_lt a v) (by norm_num)

theorem f7_eq (t x : Nat) : f7 t x = t / 2 ^ (7 * x) % 128 := by
  have h127 : (127 : Nat) = 2 ^ 7 - 1 := rfl
  unfold f7
  change (t >>> (7 * x)) &&& 127 = _
  rw [h127, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem pg7_eq (t x : Nat) : pg 7 (mask 7) t x = f7 t x := by
  rw [CFSG.KS.PK.pg_eq, f7_eq]

theorem f7_tab7 (a x : Nat) : f7 (tab7 a) x = if x < 64 then appW a x else 0 := by
  rw [f7_eq, tab7_eq]
  split
  · next h => exact tsum7_get (appW a) (appW_lt128 a) 64 x h
  · next h =>
    have hp : 2 ^ (7 * 64) ≤ 2 ^ (7 * x) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (tsum7_lt _ (appW_lt128 a) 64) hp)]

theorem linTab_get' (W y : Nat) : (linTab (col W))[y]! = if y < 64 then appW W y else 0 := by
  split
  · next h => rw [linTab_get _ h, appW_eq_ev]
  · next h =>
    rw [getElem!_neg]
    · rfl
    · simpa [linTab] using h

theorem md_get (W y : Nat) : (linTab (col W))[y]! = f7 (tab7 W) y := by
  rw [linTab_get', f7_tab7]

theorem unpack7_get (t y : Nat) : (unpack 64 7 t)[y]! = if y < 64 then f7 t y else 0 := by
  rw [unpack_getElem!, pg7_eq]

theorem tabs_get {k : Nat} (hk : k < SuzB0M.N) :
    (Array.ofFn (n := SuzB0M.N) fun j => unpack 64 7 (SuzB0M.T j.val))[k]! = unpack 64 7 (SuzB0M.T k) := by
  rw [getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem unpack_ne_lin {P W : Nat} (h : nB (Nat.beq (Nat.land P (mask 448)) (tab7 W)) = true) :
    (unpack 64 7 P == linTab (col W)) = false := by
  cases hb : (unpack 64 7 P == linTab (col W))
  · rfl
  · have he := beq_iff_eq.1 hb
    have hf : ∀ v < 64, P / 2 ^ (7 * v) % 128 = appW W v := fun v hv => by
      have e := congrArg (fun A : Array Nat => A[v]!) he
      simp only [unpack7_get, linTab_get', if_pos hv] at e
      rw [← f7_eq]
      exact e
    have hm : Nat.land P (mask 448) = tab7 W := by
      rw [CFSG.KS.PK.land_mask, tab7_eq, ← tsum7_congr hf]
      exact (tsum7_mod P 64).symm
    rw [hm, Nat.beq_refl] at h
    exact absurd h (by decide)

theorem notIn_facts : (!(matEnum.tabs.any (· == mat64 (sTau ())))) = true := by
  rw [mat64_cw_T, B0Suz.mat_tabs]
  have k := kNotIn
  unfold notInK at k
  rw [strictB_eq', strictB_eq'] at k
  cases hb : (Array.ofFn (n := SuzB0M.N) fun j => unpack 64 7 (SuzB0M.T j.val)).any
      (· == linTab (col (nthN CW 3)))
  · rfl
  · obtain ⟨i, hi, e⟩ := Array.any_eq_true.1 hb
    rw [Array.size_ofFn] at hi
    have e2 := CFSG.KS.allN_spec k i hi
    beta_reduce at e2
    rw [Array.getElem_ofFn] at e
    rw [unpack_ne_lin e2] at e
    exact absurd e (by decide)

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by cases y <;> rfl

theorem cxK_spec {T : Nat → Nat} {MD : Nat} : ∀ (L : List Nat) (k n : Nat), cxK T MD L k n = true →
    k + L.length = n ∧ ∀ i < L.length, cx1 T MD (k + i) (nthN L i) = true
  | [], k, n, h => by
    change Nat.beq k n = true at h
    exact ⟨by simpa using Nat.eq_of_beq_eq_true h, fun i hi => absurd hi (by simp)⟩
  | x :: L, k, n, h => by
    change bAnd(cx1 T MD k x, strictB (Nat.succ k) fun k' => cxK T MD L k' n) = true at h
    obtain ⟨h1, h2⟩ := band h
    rw [strictB_eq'] at h2
    obtain ⟨e, ih⟩ := cxK_spec L (k + 1) n h2
    refine ⟨by simp only [List.length_cons]; omega, fun i hi => ?_⟩
    cases i with
    | zero => exact h1
    | succ i =>
      have hi' : i < L.length := by simp only [List.length_cons] at hi; omega
      have e3 := ih i hi'
      rw [show k + 1 + i = k + (i + 1) by omega] at e3
      exact e3

theorem iter_congr {f g : Nat → Nat} (h : ∀ y < 64, f y = g y) (hg : ∀ y < 64, g y < 64) :
    ∀ m, ∀ x < 64, f^[m] x = g^[m] x
  | 0, _, _ => rfl
  | m + 1, x, hx => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h x hx]
    exact iter_congr h hg m _ (hg x hx)

theorem pg_pm7 (a b : Nat) {x : Nat} (hx : x < 64) :
    pg 7 (mask 7) (pm7 a b) x = pg 7 (mask 7) a (pg 7 (mask 7) b x) :=
  CFSG.KS.PF.pg_pcomp (by norm_num) hx

theorem p12_iter {t : Nat} (hl : ∀ y < 64, pg 7 (mask 7) t y < 64) {x : Nat} (hx : x < 64) :
    pg 7 (mask 7) (p12 t) x = (fun y => pg 7 (mask 7) t y)^[12] x := by
  have h2 : ∀ y < 64, pg 7 (mask 7) (pm7 t t) y = (fun y => pg 7 (mask 7) t y)^[2] y ∧
      pg 7 (mask 7) (pm7 t t) y < 64 := fun y hy => by
    rw [pg_pm7 _ _ hy]
    exact ⟨rfl, hl _ (hl y hy)⟩
  have h4 : ∀ y < 64, pg 7 (mask 7) (pm7 (pm7 t t) (pm7 t t)) y =
      (fun y => pg 7 (mask 7) t y)^[4] y ∧ pg 7 (mask 7) (pm7 (pm7 t t) (pm7 t t)) y < 64 :=
    fun y hy => by
      rw [pg_pm7 _ _ hy]
      obtain ⟨a1, a2⟩ := h2 y hy
      obtain ⟨b1, b2⟩ := h2 _ a2
      refine ⟨?_, b2⟩
      rw [b1, a1, ← Function.iterate_add_apply]
  unfold p12
  rw [strictN_eq', strictN_eq', pg_pm7 _ _ hx, pg_pm7 _ _ hx]
  obtain ⟨a1, a2⟩ := h4 x hx
  obtain ⟨b1, b2⟩ := h4 _ a2
  obtain ⟨c1, -⟩ := h4 _ b2
  rw [c1, b1, a1, ← Function.iterate_add_apply, ← Function.iterate_add_apply]

theorem cx1_cent {T : Nat → Nat} {W k x : Nat} (h : cx1 T (tab7 W) k x = true) :
    (∃ y < 64, (unpack 64 7 (T k))[(linTab (col W))[y]!]! ≠
        (linTab (col W))[(unpack 64 7 (T k))[y]!]!) ∨
      ((∀ y < 64, (unpack 64 7 (T k))[y]! < 64) ∧
        ∀ y < 64, (fun z => (unpack 64 7 (T k))[z]!)^[12] y = y) := by
  unfold cx1 at h
  rw [strictB_eq'] at h
  cases hx : Nat.blt x 64
  · rw [hx] at h
    obtain ⟨hp, h⟩ := band h
    obtain ⟨-, h12⟩ := band h
    have hP := CFSG.KC.Misc.ArrEnum.pp_of_permB (n := 64) (w := 7) (by decide) hp
    have hl : ∀ y < 64, pg 7 (mask 7) (T k) y < 64 := hP.2.1
    have hu : ∀ y < 64, (unpack 64 7 (T k))[y]! = pg 7 (mask 7) (T k) y := fun y hy => by
      rw [unpack_getElem!, if_pos hy]
    right
    refine ⟨fun y hy => by rw [hu y hy]; exact hl y hy, fun y hy => ?_⟩
    rw [iter_congr hu hl 12 y hy, ← p12_iter hl hy, Nat.eq_of_beq_eq_true h12]
    exact CFSG.KS.PF.pg_pidn (by norm_num) (by norm_num) hy
  · rw [hx] at h
    change nB (Nat.beq (f7 (T k) (f7 (tab7 W) x)) (f7 (tab7 W) (f7 (T k) x))) = true at h
    have hx' : x < 64 := Nat.blt_eq.mp hx
    left
    refine ⟨x, hx', fun e => ?_⟩
    rw [nB_eq] at h
    have hne : f7 (T k) (f7 (tab7 W) x) ≠ f7 (tab7 W) (f7 (T k) x) := fun e' => by
      rw [e', Nat.beq_refl] at h
      exact absurd h (by decide)
    apply hne
    have h1 : f7 (tab7 W) x < 64 := by
      rw [f7_tab7, if_pos hx']
      exact appW_lt W x
    rw [md_get, md_get, unpack7_get, unpack7_get, if_pos h1, if_pos hx'] at e
    exact e

theorem centK_spec {T : Nat → Nat} {NM md : Nat} {CX : List Nat} (k : centK T NM md CX = true) :
    CFSG.KC.Misc.ArrEnum.permB 64 7 (tab7 md) = true ∧ cxK T (tab7 md) CX 0 NM = true := by
  unfold centK at k
  rw [strictB_eq'] at k
  exact band k

theorem cent_facts : allBelow matEnum.tabs.size (fun k => !(comm64 matEnum.tabs[k]! (mat64 (sD ()))) ||
    pow12 matEnum.tabs[k]! == idTab 64) = true := by
  rw [mat64_cw_D, B0Suz.mat_tabs]
  obtain ⟨-, k2⟩ := centK_spec kCent
  obtain ⟨hlen, hcx⟩ := cxK_spec CX 0 SuzB0M.N k2
  refine centPow12 fun j hj => ?_
  rw [Array.size_ofFn] at hj
  rw [tabs_get hj]
  have e := hcx j (by omega)
  rw [Nat.zero_add] at e
  exact cx1_cent e

theorem formK_spec {g : Nat → Nat → Nat} {md : Nat} (k : formK g md = true) :
    (allN 64 fun v => bIf(Nat.beq v 0, true, bIf(Nat.beq (appW md v) v, pairK g md v, true))) =
      true ∧ Nat.beq (fixCnt md) 16 = true := by
  unfold formK at k
  exact band k

theorem form_facts : allBelow 64 (fun v => v == 0 || (mat64 (sD ()))[v]! != v ||
    anyBelow 64 fun w => (mat64 (sD ()))[w]! == w &&
      (gammaBit v w + gammaBit w v) % 2 == 1) = true := by
  rw [mat64_cw_D]
  obtain ⟨k1, -⟩ := formK_spec kForm
  refine allBelow_true fun v hv => ?_
  by_cases hv0 : v = 0
  · simp [hv0]
  by_cases hf : (linTab (col (nthN CW 0)))[v]! = v
  · have e := CFSG.KS.allN_spec k1 v hv
    beta_reduce at e
    have hfa : appW (nthN CW 0) v = v := by rw [linTab_get', if_pos hv] at hf; exact hf
    have hb0 : Nat.beq v 0 = false := by
      cases hc : Nat.beq v 0
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hc) hv0
    rw [hb0, hfa, Nat.beq_refl] at e
    change nB (allN 64 fun w => nB (bAnd(Nat.beq (appW (nthN CW 0) w) w,
      Nat.beq (Nat.mod (Nat.add (gammaBit v w) (gammaBit w v)) 2) 1))) = true at e
    rw [nB_eq] at e
    have hex : ∃ w < 64, bAnd(Nat.beq (appW (nthN CW 0) w) w,
        Nat.beq (Nat.mod (Nat.add (gammaBit v w) (gammaBit w v)) 2) 1) = true := by
      by_contra hne
      have ha : (allN 64 fun w => nB (bAnd(Nat.beq (appW (nthN CW 0) w) w,
          Nat.beq (Nat.mod (Nat.add (gammaBit v w) (gammaBit w v)) 2) 1))) = true :=
        CFSG.KS.Raw.Orb.allN_iff.2 fun w hw => by
          rw [nB_eq]
          cases hc : bAnd(Nat.beq (appW (nthN CW 0) w) w,
              Nat.beq (Nat.mod (Nat.add (gammaBit v w) (gammaBit w v)) 2) 1)
          · rfl
          · exact absurd ⟨w, hw, hc⟩ hne
      rw [ha] at e
      exact absurd e (by decide)
    obtain ⟨w, hw, hwb⟩ := hex
    obtain ⟨w1, w2⟩ := band hwb
    have ha : (anyBelow 64 fun w => (linTab (col (nthN CW 0)))[w]! == w &&
        (gammaBit v w + gammaBit w v) % 2 == 1) = true := by
      refine anyBelow_true hw ?_
      rw [linTab_get', if_pos hw, Nat.eq_of_beq_eq_true w1]
      have e2 := Nat.eq_of_beq_eq_true w2
      change (gammaBit v w + gammaBit w v) % 2 = 1 at e2
      simp [e2]
    simp [ha]
  · simp [hf]

theorem count_eq (W : Nat) : ∀ n ≤ 64,
    ((List.range n).filter fun v => (linTab (col W))[v]! == v).length =
      Nat.rec (motive := fun _ => Nat) 0
        (fun v acc => strictN acc fun a => Nat.add a (nIf(Nat.beq (appW W v) v, 1, 0))) n
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.filter_append, List.length_append, count_eq W n (by omega)]
    change _ = strictN _ fun a => Nat.add a (nIf(Nat.beq (appW W n) n, 1, 0))
    rw [strictN_eq']
    have hg : ((linTab (col W))[n]! == n) = Nat.beq (appW W n) n := by
      rw [linTab_get', if_pos (by omega : n < 64)]
      cases hb : Nat.beq (appW W n) n
      · simp only [beq_eq_false_iff_ne]
        exact Nat.ne_of_beq_eq_false hb
      · simp only [beq_iff_eq]
        exact Nat.eq_of_beq_eq_true hb
    rw [List.filter_singleton, hg]
    cases Nat.beq (appW W n) n <;> rfl

theorem count_facts : (countBelow 64 (fun v => (mat64 (sD ()))[v]! == v) == 16) = true := by
  rw [mat64_cw_D]
  obtain ⟨-, k2⟩ := formK_spec kForm
  have e : countBelow 64 (fun v => (linTab (col (nthN CW 0)))[v]! == v) = fixCnt (nthN CW 0) :=
    count_eq _ 64 (le_refl _)
  rw [e, Nat.eq_of_beq_eq_true k2]
  rfl

end CertificateChecks.KernelSpor.SuzI301K

end
