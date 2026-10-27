module

public import Certificates.Kernel.Fi22Twist.SrchNode
public import Certificates.Kernel.Fi22Twist.Cs0
public import Certificates.Kernel.Fi22Twist.Cs2
public import Certificates.Kernel.Fi22Twist.Cs3a
public import Certificates.Kernel.Fi22Twist.Cs3b
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist CFSG.KS CFSG.KS.E27Lie
open CFSG.KS.Fi22Twist CFSG.KC.Fi22Rk CFSG.KC.BfsPin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.KS.Raw
open CFSG.Monster.B.Fischer CertificateChecks.KernelSpor

set_option maxRecDepth 400000

#kc_forall_tree cs0431009All (fun k => ch431009cs0_ k = true) 6
  CertificateChecks.KernelFi22Twist.ch431009cs0_

#kc_forall_tree cs1431009All (fun k => ch431009cs1_ k = true) 21
  CertificateChecks.KernelFi22Twist.ch431009cs1_

#kc_forall_tree cs2431009All (fun k => ch431009cs2_ k = true) 31
  CertificateChecks.KernelFi22Twist.ch431009cs2_

#kc_forall_tree cs3431009All (fun k => ch431009cs3_ k = true) 122
  CertificateChecks.KernelFi22Twist.ch431009cs3_

#kc_forall_tree cs4431009All (fun k => ch431009cs4_ k = true) 11
  CertificateChecks.KernelFi22Twist.ch431009cs4_

#kc_forall_tree lf431009All (fun k => ch431009lf_ k = true) 188
  CertificateChecks.KernelFi22Twist.ch431009lf_

#kc_forall_tree wf431009All (fun k => ch431009wf_ k = true) 12
  CertificateChecks.KernelFi22Twist.ch431009wf_

theorem offK_vals : offK 0 = 0 ∧ offK 1 = 81 ∧ offK 2 = 405 ∧ offK 3 = 891 ∧ offK 4 = 2835 ∧
    offK 5 = 2997 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem addB (lo : ℕ) : ∀ k, Nat.add lo (Nat.mul 16 k) = lo + 16 * k := fun _ => rfl

theorem blk_all {j : ℕ} (hj : j < 5) : ∀ n, offK j ≤ n → n < offK (Nat.succ j) →
    blockK CFSG.KD.Fi22Twist.TF DF CFSG.KD.N3153.M BF HF CFSG.KD.Fi22Twist.KF j n = true := by
  obtain ⟨o0, o1, o2, o3, o4, o5⟩ := offK_vals
  interval_cases j
  · rw [o0, o1]
    exact blk_cover (by norm_num) (addB 0) (fun k hk => cs0431009All k hk) (by norm_num)
  · rw [o1, o2]
    exact blk_cover (by norm_num) (addB 81) (fun k hk => cs1431009All k hk) (by norm_num)
  · rw [o2, o3]
    exact blk_cover (by norm_num) (addB 405) (fun k hk => cs2431009All k hk) (by norm_num)
  · rw [o3, o4]
    exact blk_cover (by norm_num) (addB 891) (fun k hk => cs3431009All k hk) (by norm_num)
  · rw [o4, o5]
    exact blk_cover (by norm_num) (addB 2835) (fun k hk => cs4431009All k hk) (by norm_num)

theorem jOf_eq {j n : ℕ} (hj : j < 5) (h1 : offK j ≤ n) (h2 : n < offK (Nat.succ j)) :
    jOf n = j := by
  obtain ⟨o0, o1, o2, o3, o4, o5⟩ := offK_vals
  unfold jOf
  interval_cases j
  · rw [o1] at h2
    rw [blt_tt h2]
  · rw [o1] at h1
    rw [o2] at h2
    rw [blt_ff (a := n) (b := 81) h1, blt_tt h2]
  · rw [o2] at h1
    rw [o3] at h2
    rw [blt_ff (a := n) (b := 81) (by omega), blt_ff (a := n) (b := 405) h1, blt_tt h2]
  · rw [o3] at h1
    rw [o4] at h2
    rw [blt_ff (a := n) (b := 81) (by omega), blt_ff (a := n) (b := 405) (by omega),
      blt_ff (a := n) (b := 891) h1, blt_tt h2]
  · rw [o4] at h1
    rw [blt_ff (a := n) (b := 81) (by omega), blt_ff (a := n) (b := 405) (by omega),
      blt_ff (a := n) (b := 891) (by omega), blt_ff (a := n) (b := 2835) h1]

theorem lf_all {j : ℕ} (hj : j < 5) (n : ℕ) (h1 : offK j ≤ n) (h2 : n < offK (Nat.succ j)) :
    leafK CFSG.KD.Fi22Twist.TF DF CFSG.KD.N3153.M BF WF XF EF CFSG.KD.Fi22Twist.KF CK j n
      (t12 offC j) (t12 szC j) = true := by
  have hn : n < 2997 := by
    have := offK_vals.2.2.2.2.2
    have hle : offK (Nat.succ j) ≤ offK 5 := by
      obtain ⟨o0, o1, o2, o3, o4, o5⟩ := offK_vals
      interval_cases j <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, o1, o2, o3, o4, o5] <;>
        norm_num
    omega
  have h := blk_cover (f := fun n => strictB (jOf n) fun j =>
      leafK CFSG.KD.Fi22Twist.TF DF CFSG.KD.N3153.M BF WF XF EF CFSG.KD.Fi22Twist.KF CK j n
        (t12 offC j) (t12 szC j)) (lo := 0) (hi := 2997) (w := 16) (nb := 188) (by norm_num)
    (mulB 16) (fun k hk => lf431009All k hk) (by norm_num) n (Nat.zero_le _) hn
  beta_reduce at h
  rw [CFSG.KC.Fi22Twist.strictB_eq, jOf_eq hj h1 h2] at h
  exact h

theorem wf_all : ∀ u < 728, wfK WF OF BF Fi22ChT.F u = true :=
  fun u hu => blk_cover (lo := 0) (hi := 728) (w := 64) (nb := 12) (by norm_num) (mulB 64)
    (fun k hk => wf431009All k hk) (by norm_num) u (Nat.zero_le _) hu


theorem wAp_mem : ∀ {l : List ℕ}, (∀ g ∈ l, g < 19) →
    ∃ w ∈ fi22P, ∀ x < 3510, wAp Fi22ChT.F l x = pt (MonoidHom.id _) w x
  | [], _ => ⟨1, one_mem _, fun x _ => by rw [wAp_nil, pt_one]⟩
  | g :: l, hl => by
    obtain ⟨w, hw, hwx⟩ := wAp_mem (l := l) fun g' hg' => hl g' (List.mem_cons_of_mem _ hg')
    have hg := hl g (List.mem_cons.2 (Or.inl rfl))
    refine ⟨fi22StrongPerm g * w, mul_mem (strong_memP hg) hw, fun x hx => ?_⟩
    rw [wAp_cons, hwx x hx, ap_strong hg (pt_lt _ _ hx), pt_mul]

theorem leafFull_sum {BF WF : ℕ → ℕ} {a : ℕ → ℕ} {k p q : ℕ} (ha : ∀ x, a x < 4096) :
    leafFull BF WF a k p q = a (bp 0) + a (bp 1) * 2 ^ 12 + a (bp 2) * 2 ^ 24 +
      a (fld(BF k, 0, 4095)) * 2 ^ 36 + a (fld(BF k, Nat.mul 12 (Nat.succ p), 4095)) * 2 ^ 48 +
      a (fld(WF (Nat.add 8 k), Nat.mul 12 (Nat.add (Nat.mul 2 p) q), 4095)) * 2 ^ 60 := by
  have h0 := ha (bp 0)
  have h1 := ha (bp 1)
  have h2 := ha (bp 2)
  have h3 := ha (fld(BF k, 0, 4095))
  have h4 := ha (fld(BF k, Nat.mul 12 (Nat.succ p), 4095))
  have h5 := ha (fld(WF (Nat.add 8 k), Nat.mul 12 (Nat.add (Nat.mul 2 p) q), 4095))
  unfold leafFull
  generalize a (bp 0) = a0 at h0 ⊢
  generalize a (bp 1) = a1 at h1 ⊢
  generalize a (bp 2) = a2 at h2 ⊢
  generalize a (fld(BF k, 0, 4095)) = a3 at h3 ⊢
  generalize a (fld(BF k, Nat.mul 12 (Nat.succ p), 4095)) = a4 at h4 ⊢
  generalize a (fld(WF (Nat.add 8 k), Nat.mul 12 (Nat.add (Nat.mul 2 p) q), 4095)) = a5 at h5 ⊢
  change (((a0 ||| a1 <<< 12) ||| a2 <<< 24) ||| (a3 <<< 36 ||| a4 <<< 48)) ||| a5 <<< 60 = _
  rw [Nat.shiftLeft_eq a1 12, Nat.shiftLeft_eq a2 24, Nat.shiftLeft_eq a3 36,
    Nat.shiftLeft_eq a4 48, Nat.shiftLeft_eq a5 60]
  have e1 : a0 ||| a1 * 2 ^ 12 = a0 + a1 * 2 ^ 12 :=
    or_add (by simp only [Nat.reducePow]; omega) (Dvd.intro_left _ rfl)
  have e2 : (a0 + a1 * 2 ^ 12) ||| a2 * 2 ^ 24 = a0 + a1 * 2 ^ 12 + a2 * 2 ^ 24 :=
    or_add (s := 24) (by simp only [Nat.reducePow]; omega) (Dvd.intro_left _ rfl)
  have e3 : a3 * 2 ^ 36 ||| a4 * 2 ^ 48 = a3 * 2 ^ 36 + a4 * 2 ^ 48 :=
    or_add (by simp only [Nat.reducePow]; omega) (Dvd.intro_left _ rfl)
  have e4 : (a0 + a1 * 2 ^ 12 + a2 * 2 ^ 24) ||| (a3 * 2 ^ 36 + a4 * 2 ^ 48) =
      a0 + a1 * 2 ^ 12 + a2 * 2 ^ 24 + (a3 * 2 ^ 36 + a4 * 2 ^ 48) :=
    or_add (s := 36) (by simp only [Nat.reducePow]; omega) (by simp only [Nat.reducePow]; omega)
  have e5 : (a0 + a1 * 2 ^ 12 + a2 * 2 ^ 24 + (a3 * 2 ^ 36 + a4 * 2 ^ 48)) ||| a5 * 2 ^ 60 =
      a0 + a1 * 2 ^ 12 + a2 * 2 ^ 24 + (a3 * 2 ^ 36 + a4 * 2 ^ 48) + a5 * 2 ^ 60 :=
    or_add (s := 60) (by simp only [Nat.reducePow]; omega) (Dvd.intro_left _ rfl)
  rw [e1, e2, e3, e4, e5]
  simp only [Nat.add_assoc]

@[expose] def St (j : ℕ) (g : Equiv.Perm (Fin 3510)) (n d : ℕ) : Prop :=
  n < 212 ∧ fld(LF n, 48, 255) = d ∧ fld(LF n, 56, 255) = j ∧ ∃ α ∈ fi22P,
    (∀ x < 3510, aN (LF n) x = pt (MonoidHom.id _) α x) ∧
    ∀ m < d, pt (MonoidHom.id _) α (bp m) = pt (MonoidHom.id _) g (bp m)

theorem st_root {j : ℕ} (hj : j < 5) (g : Equiv.Perm (Fin 3510)) : St j g j 0 := by
  have h := allBlk_spec0 ch431009rt j hj
  unfold rootK at h
  rw [strictB_eqL] at h
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 h
  have e48 := Nat.eq_of_beq_eq_true h1
  refine ⟨by omega, e48, Nat.eq_of_beq_eq_true h2, 1, one_mem _, fun x _ => ?_,
    fun m hm => absurd hm (Nat.not_lt_zero _)⟩
  unfold aN
  rw [e48, pt_one]
  rfl

theorem st_step {j : ℕ} (hj : j < 5) {g : Equiv.Perm (Fin 3510)} (hgP : g ∈ fi22P)
    (hc : ∀ y ∈ dSub j, g * y = y * g) {n d : ℕ} (hd : d < 2) (hs : St j g n d) :
    ∃ n', St j g n' (d + 1) := by
  obtain ⟨hn, h48, h56, α, hα, ha, hfix⟩ := hs
  obtain ⟨-, t, ht, hpre, hlf, -, hfi, α', hα', ha', hfix'⟩ :=
    node_step hj hn h56 hgP hc hα ha (by rw [h48]; exact hfix)
  rw [h48] at hpre hlf hfi ha' hfix'
  have e2 : Nat.blt d 2 = true := blt_tt hd
  rw [e2] at hpre hfi ha'
  obtain ⟨h48', h56'⟩ := hlf hd
  generalize hn' : Nat.add (fld(LF n, 64, 65535)) t = n' at hpre hfi ha' h48' h56'
  have hlt : n' < 212 := by
    have h := CFSG.KS.allN_spec ch431009lc n hn
    beta_reduce at h
    rw [strictB_eqL, h48, e2] at h
    have := Nat.le_of_ble_eq_true h
    change fld(LF n, 64, 65535) + fld(LF n, 80, 255) ≤ 212 at this
    change fld(LF n, 64, 65535) + t = n' at hn'
    omega
  have hmap : ∀ x, aN (LF n') x = aN (LF n) (ap (TC (fld(LF n', Nat.mul 16 d, 65535))) x) := by
    intro x
    obtain rfl | rfl : d = 0 ∨ d = 1 := by omega
    · unfold aN
      rw [h48', h48]
      rfl
    · have e0 : fld(LF n', 0, 65535) = fld(LF n, 0, 65535) := hpre 0 (by norm_num)
      unfold aN
      rw [h48', h48, e0]
      rfl
  refine ⟨n', hlt, h48', h56', α', hα', fun x hx => ?_, fun m hm => hfix' m (by omega)⟩
  rw [hmap]
  exact ha' x hx

theorem st_three {j : ℕ} (hj : j < 5) {g : Equiv.Perm (Fin 3510)} (hgP : g ∈ fi22P)
    (hc : ∀ y ∈ dSub j, g * y = y * g) {n : ℕ} (hs : St j g n 2) :
    ∃ n3, offK j ≤ n3 ∧ n3 < offK (Nat.succ j) ∧ ∃ α ∈ fi22P,
      (∀ x < 3510, leafA CFSG.KD.Fi22Twist.TF CFSG.KD.Fi22Twist.KF n3 x =
        pt (MonoidHom.id _) α x) ∧
      ∀ m < 3, pt (MonoidHom.id _) α (bp m) = pt (MonoidHom.id _) g (bp m) := by
  obtain ⟨hn, h48, h56, α, hα, ha, hfix⟩ := hs
  obtain ⟨-, t, ht, hpre, -, hrange, hfi, α', hα', ha', hfix'⟩ :=
    node_step hj hn h56 hgP hc hα ha (by rw [h48]; exact hfix)
  rw [h48] at hpre hrange hfi ha' hfix'
  have e2 : Nat.blt 2 2 = false := rfl
  rw [e2] at hpre hfi ha'
  obtain ⟨r1, r2⟩ := hrange (by norm_num)
  generalize hn3 : Nat.add (fld(LF n, 64, 65535)) t = n3 at hpre hfi ha' r1 r2
  have hn3 : n3 < 2997 := by
    obtain ⟨o0, o1, o2, o3, o4, o5⟩ := offK_vals
    interval_cases j <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, o1, o2, o3, o4, o5] at r2 <;>
      omega
  have hk := CFSG.KS.allN_spec ch431009kf n3 hn3
  beta_reduce at hk
  rw [strictB_eqL] at hk
  obtain ⟨k0, hk⟩ := (bAnd_iff _ _).1 hk
  obtain ⟨k1, k2⟩ := (bAnd_iff _ _).1 hk
  have e0 : fld(CFSG.KD.Fi22Twist.KF n3, 0, 65535) = fld(LF n, 0, 65535) := hpre 0 (by norm_num)
  have e1 : fld(CFSG.KD.Fi22Twist.KF n3, 16, 65535) = fld(LF n, 16, 65535) := hpre 1 (by norm_num)
  have hmap : ∀ x, leafA CFSG.KD.Fi22Twist.TF CFSG.KD.Fi22Twist.KF n3 x =
      aN (LF n) (ap (TC (fld(CFSG.KD.Fi22Twist.KF n3, Nat.mul 16 2, 65535))) x) := by
    intro x
    unfold leafA aN
    rw [← tc_lt (Nat.le_of_ble_eq_true k0), ← tc_lt (Nat.le_of_ble_eq_true k1),
      ← tc_lt (Nat.le_of_ble_eq_true k2), e0, e1, h48]
    rfl
  refine ⟨n3, r1, r2, α', hα', fun x hx => ?_, fun m hm => hfix' m (by omega)⟩
  rw [hmap]
  exact ha' x hx

theorem szL3 : szL 3 = 720 := by decide
theorem szL4 : szL 4 = 8 := by decide
theorem szL5 : szL 5 = 2 := by decide

theorem mem_cSub {j : ℕ} (hj : j < 5) {g : Equiv.Perm (Fin 3510)} (hgP : g ∈ fi22P)
    (hc : ∀ y ∈ dSub j, g * y = y * g) : g ∈ cSub j := by
  obtain ⟨n1, s1⟩ := st_step hj hgP hc (d := 0) (by norm_num) (st_root hj g)
  obtain ⟨n2, s2⟩ := st_step hj hgP hc (d := 1) (by norm_num) s1
  obtain ⟨n3, r1, r2, α, hα, ha, hfix⟩ := st_three hj hgP hc s2
  have hP' : α⁻¹ * g ∈ fi22P := mul_mem (inv_mem hα) hgP
  have hfix3 : ∀ m < 3, pt (MonoidHom.id _) (α⁻¹ * g) (bp m) = bp m := by
    intro m hm
    rw [pt_mul, ← hfix m hm, ← pt_mul, inv_mul_cancel, pt_one]
  have hback : ∀ x, pt (MonoidHom.id _) α (pt (MonoidHom.id _) (α⁻¹ * g) x) =
      pt (MonoidHom.id _) g x := fun x => by rw [← pt_mul, mul_inv_cancel_left]
  obtain ⟨k, hk, hkv⟩ := lv_orbit (i := 3) (by norm_num) hP' hfix3
  rw [szL3] at hk
  have hbo : fld(BF k, 0, 4095) = ap (OF 3) k := by
    have h := CFSG.KS.allN_spec ch431009bo k hk
    exact Nat.eq_of_beq_eq_true h
  have hlt : ∀ x < 3510, pt (MonoidHom.id _) (α⁻¹ * g) x < 3510 := fun x hx => pt_lt _ _ hx
  have h3 : leafA CFSG.KD.Fi22Twist.TF CFSG.KD.Fi22Twist.KF n3 (fld(BF k, 0, 4095)) =
      pt (MonoidHom.id _) g (bp 3) := by
    rw [hbo, hkv, ha _ (hlt _ (by decide)), hback]
  obtain ⟨φ, ⟨u, hu, hφu⟩, hφfix, hφpts⟩ := bf_mem k hk
  have hr0 := bf_root (bf_all 0 (by norm_num))
  have hP'' : u⁻¹ * (α⁻¹ * g) ∈ fi22P := mul_mem (inv_mem hu) hP'
  have hu3 : pt (MonoidHom.id _) u 3 = pt (MonoidHom.id _) (α⁻¹ * g) (bp 3) := by
    rw [← hφu 3 (by norm_num), ← hkv, ← hbo, ← hr0.1]
    exact (hφpts 0 (by norm_num)).symm
  have hfix4 : ∀ m < 4, pt (MonoidHom.id _) (u⁻¹ * (α⁻¹ * g)) (bp m) = bp m := by
    intro m hm
    rw [pt_mul]
    rcases Nat.lt_or_ge m 3 with h | h
    · have hum : pt (MonoidHom.id _) u (bp m) = bp m := by
        rw [← hφu _ (bp_lt m (by omega))]
        exact hφfix m h
      have e : pt (MonoidHom.id _) u⁻¹ (bp m) =
          pt (MonoidHom.id _) u⁻¹ (pt (MonoidHom.id _) u (bp m)) := by rw [hum]
      rw [hfix3 m h, e, ← pt_mul, inv_mul_cancel, pt_one]
    · obtain rfl : m = 3 := by omega
      rw [← hu3, ← pt_mul, inv_mul_cancel, pt_one]
      rfl
  obtain ⟨p, hp, hpv⟩ := lv_orbit (i := 4) (by norm_num) hP'' hfix4
  rw [szL4] at hp
  have hw8 := wf8_sound (wf_all 8 (by norm_num)) p hp
  have hB4 : fld(BF k, Nat.mul 12 (Nat.succ p), 4095) = pt (MonoidHom.id _) (α⁻¹ * g) (bp 4) := by
    rw [hφpts (Nat.succ p) (by omega), hw8.1, hpv, hφu _ (pt_lt _ _ (bp_lt 4 (by norm_num))),
      ← pt_mul, mul_inv_cancel_left]
  have h4 : leafA CFSG.KD.Fi22Twist.TF CFSG.KD.Fi22Twist.KF n3
      (fld(BF k, Nat.mul 12 (Nat.succ p), 4095)) = pt (MonoidHom.id _) g (bp 4) := by
    rw [hB4, ha _ (hlt _ (bp_lt 4 (by norm_num))), hback]
  have h4' : leafA CFSG.KD.Fi22Twist.TF CFSG.KD.Fi22Twist.KF n3 (fld(BF k, 12 * (p + 1), 4095)) =
      pt (MonoidHom.id _) g 6 := h4
  have hRel := jx_rel hj
  have hD' : ∀ e < 27, ∀ x < 3510, pt (MonoidHom.id _) g (ap (DF (Nat.add (Nat.mul 27 j) e)) x) =
      ap (DF (Nat.add (Nat.mul 27 j) e)) (pt (MonoidHom.id _) g x) := d_comm hj hc
  have hpass := pass_of_base (M := CFSG.KD.N3153.M) (Dj := fun e => DF (Nat.add (Nat.mul 27 j) e))
    (BF := BF) (a := leafA CFSG.KD.Fi22Twist.TF CFSG.KD.Fi22Twist.KF n3)
    (g := pt (MonoidHom.id _) g) (k := k) (p := p) (relV_sound hRel.2.1) (relV_sound hRel.2.2.1)
    (fun x hx => pt_lt _ _ hx) (eb_inv hgP) (d_comm hj hc) (d_lt hj)
    (fun m hm => by rw [ha _ (bp_lt m (by omega)), hfix m hm]) h3 h4'
  have hcode := blockK_sound (blk_all hj n3 r1 r2) k p hk hp hpass
  obtain ⟨hz, hl⟩ := leafK_sound (lf_all hj n3 r1 r2)
  obtain ⟨s, hs, hsv⟩ := codeMem_lt9 hcode hz (by omega)
  obtain ⟨-, hq⟩ := hl s hs k p hsv hp
  obtain ⟨l, hl19, hlfix, hl3, hl4, hl5⟩ := wf_sound wf_all bf_all k hk p hp
  obtain ⟨w, hw, hwx⟩ := wAp_mem hl19
  have hb4 := (lv_base (lv_all (20 * 4 + 19) (by norm_num))).1
  have hP5 : w⁻¹ * (α⁻¹ * g) ∈ fi22P := mul_mem (inv_mem hw) hP'
  have hfix5 : ∀ m < 5, pt (MonoidHom.id _) (w⁻¹ * (α⁻¹ * g)) (bp m) = bp m := by
    intro m hm
    rw [pt_mul]
    have key : pt (MonoidHom.id _) (α⁻¹ * g) (bp m) = pt (MonoidHom.id _) w (bp m) := by
      rcases Nat.lt_or_ge m 3 with h | h
      · rw [hfix3 m h, ← hwx _ (bp_lt m (by omega)), hlfix m h]
      · obtain rfl | rfl : m = 3 ∨ m = 4 := by omega
        · rw [← hwx _ (bp_lt 3 (by norm_num)), hl3, hbo, hkv]
        · rw [← hwx _ (bp_lt 4 (by norm_num)), ← hb4, hl4, hb4, hB4]
    rw [key, ← pt_mul, inv_mul_cancel, pt_one]
  obtain ⟨q, hq2, hqv⟩ := lv_orbit (i := 5) (by norm_num) hP5 hfix5
  rw [szL5] at hq2
  have hv5 : leafA CFSG.KD.Fi22Twist.TF CFSG.KD.Fi22Twist.KF n3
      (fld(WF (Nat.add 8 k), Nat.mul 12 (Nat.add (Nat.mul 2 p) q), 4095)) =
      pt (MonoidHom.id _) g (bp 5) := by
    have hO5 : ap (OF 5) q < 3510 := by
      rw [hqv]
      exact pt_lt _ _ (bp_lt6 5 (by norm_num))
    rw [hl5 q hq2, hwx _ hO5, hqv, ← pt_mul, mul_inv_cancel_left,
      ha _ (pt_lt _ _ (bp_lt6 5 (by norm_num))), hback]
  have hfull : leafFull BF WF (leafA CFSG.KD.Fi22Twist.TF CFSG.KD.Fi22Twist.KF n3) k p q =
      baseImg g := by
    rw [leafFull_sum (a := leafA CFSG.KD.Fi22Twist.TF CFSG.KD.Fi22Twist.KF n3)
      (fun x => ap_lt _ _), h3, h4, hv5, ha _ (bp_lt 0 (by norm_num)),
      ha _ (bp_lt 1 (by norm_num)), ha _ (bp_lt 2 (by norm_num)), hfix 0 (by norm_num),
      hfix 1 (by norm_num), hfix 2 (by norm_num)]
    rfl
  have hcg : ∀ l ≤ 5, cg (leafFull BF WF (leafA CFSG.KD.Fi22Twist.TF CFSG.KD.Fi22Twist.KF n3)
      k p q) l = pt (MonoidHom.id _) g (bp l) := by
    intro l hl
    rw [hfull, cg_baseImg g (by omega)]
  rcases leafV_sound (hq q hq2) with ⟨i, hi, hik⟩ | hrel | ⟨mm, hmm, e, he, hne⟩
  · obtain ⟨c, hc', hck⟩ := (orbC hj).1 i hi
    have : c = g := baseImg_inj (cSub_le_P hj hc') hgP (hck.trans (hik.trans hfull))
    rw [← this]
    exact hc'
  · have := relK_intro (relV_sound hRel.2.2.2) hcg fun e he l hl =>
      d_comm hj hc e he _ (bp_lt6 l (by omega))
    rw [this] at hrel
    exact absurd hrel (by decide)
  · exfalso
    apply hne
    rw [hcg mm (by omega), hv5, ← hD' e he _ (bp_lt6 mm (by omega))]
    exact eb_inv hgP _ (d_lt hj e he _ (bp_lt6 mm (by omega))) _ (bp_lt6 5 (by norm_num))

theorem cent_eq_cSub {j : ℕ} (hj : j < 5) :
    fi22P ⊓ Subgroup.centralizer (dSub j : Set (Equiv.Perm (Fin 3510))) = cSub j := by
  refine le_antisymm (fun g hg => ?_) (le_inf (cSub_le_P hj) (cSub_le_cent hj))
  obtain ⟨hgP, hgc⟩ := Subgroup.mem_inf.1 hg
  exact mem_cSub hj hgP fun y hy => (Subgroup.mem_centralizer_iff.1 hgc y hy).symm

end CertificateChecks.KernelFi22Twist

end
