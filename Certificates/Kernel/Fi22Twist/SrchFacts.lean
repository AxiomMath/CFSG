module

public import Certificates.Kernel.Fi22Twist.CardCU
public import Certificates.Kernel.Fi22Twist.SrchChk
public import Certificates.Kernel.Fi22Twist.LvChk
public import Certificates.Kernel.Fi22Twist.TfChk
public import Certificates.Kernel.Fi22Twist.BfChk
public import CFSG.Certificates.Kernel.Fi22Twist.LvOrbSound
public import CFSG.Certificates.Kernel.Fi22Twist.TfSound
public import CFSG.Monster.B.Fischer.Fi22Order
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelFi22Twist

open CFSG.KC.Enum CFSG.KC.E27Lie CFSG.KC.Fi22Twist CFSG.KD.Fi22Twist CFSG.KS CFSG.KS.E27Lie
open CFSG.KS.Fi22Twist CFSG.KC.Fi22Rk CFSG.KC.BfsPin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.Native CFSG.KS.Raw
open CFSG.Monster.B.Fischer CertificateChecks.KernelSpor

set_option maxRecDepth 400000

theorem blk_cover {f : ℕ → Bool} {B : ℕ → ℕ} {lo hi w nb : ℕ} (hw : 0 < w)
    (hB : ∀ k, B k = lo + w * k)
    (h : ∀ k < nb, allBlk (B k) (fun i => bIf(Nat.blt i hi, f i, true)) w = true)
    (hN : hi ≤ lo + w * nb) : ∀ i, lo ≤ i → i < hi → f i = true := by
  intro i hlo hhi
  have hk : (i - lo) / w < nb := by
    rw [Nat.div_lt_iff_lt_mul hw]
    have := Nat.mul_comm w nb
    omega
  have e := allBlk_spec (h _ hk) ((i - lo) % w) (Nat.mod_lt _ hw)
  have ei : Nat.add (B ((i - lo) / w)) ((i - lo) % w) = i := by
    change B ((i - lo) / w) + (i - lo) % w = i
    rw [hB]
    have := Nat.div_add_mod (i - lo) w
    omega
  rw [ei, blt_tt hhi] at e
  exact e

theorem mulB (w : ℕ) : ∀ k, Nat.mul w k = 0 + w * k := fun k => (Nat.zero_add _).symm

#kc_forall_tree tf431009All (fun k => ch431009tf_ k = true) 109
  CertificateChecks.KernelFi22Twist.ch431009tf_

#kc_forall_tree bf431009All (fun k => ch431009bf_ k = true) 15
  CertificateChecks.KernelFi22Twist.ch431009bf_

#kc_forall_tree lv431009All (fun k => ch431009lv_ k = true) 120
  CertificateChecks.KernelFi22Twist.ch431009lv_

#kc_forall_tree tp431009All (fun k => ch431009tp_ k = true) 14
  CertificateChecks.KernelFi22Twist.ch431009tp_

#kc_forall_tree nd431009All (fun k => ch431009nd_ k = true) 212
  CertificateChecks.KernelFi22Twist.ch431009nd_

theorem tf_all : ∀ f < 865, tfK CFSG.KD.Fi22Twist.TF CFSG.KD.Fi22Twist.TT Fi22ChT.F f = true := by
  refine fun f hf => blk_cover (lo := 0) (hi := 865) (w := 8) (nb := 109) (by norm_num) (mulB 8)
    (fun k hk => ?_) (by norm_num) f (Nat.zero_le _) hf
  have h := tf431009All k hk
  unfold ch431009tf_ at h
  exact h

theorem bf_all : ∀ k < 720, bfK BF Fi22ChT.F k = true := by
  intro k hk
  have hk' : k / 48 < 15 := by omega
  have h := bf431009All (k / 48) hk'
  unfold ch431009bf_ at h
  have e := allBlk_spec h (k % 48) (Nat.mod_lt _ (by norm_num))
  have ei : Nat.add (Nat.mul 48 (k / 48)) (k % 48) = k := by
    change 48 * (k / 48) + k % 48 = k
    omega
  rwa [ei] at e

theorem tp_all : ∀ f < 891, tfPtK TC TTC OF f = true := by
  refine fun f hf => blk_cover (lo := 0) (hi := 891) (w := 64) (nb := 14) (by norm_num) (mulB 64)
    (fun k hk => ?_) (by norm_num) f (Nat.zero_le _) hf
  have h := tp431009All k hk
  unfold ch431009tp_ at h
  exact h

theorem lv_all : ∀ u < 120, lvK OF PF Fi22ChT.F u = true := fun u hu => lv431009All u hu

theorem nd_all : ∀ n < 212,
    nodeK TC TTC OF CFSG.KD.N3153.M DF GF LF CFSG.KD.Fi22Twist.KF n = true :=
  fun n hn => nd431009All n hn


theorem get_ap {p x : ℕ} (hx : x < 3510) : (unpack 3510 12 p)[x]! = ap p x := by
  rw [CFSG.KC.Fi22RkS.get_unpack hx]
  rfl

theorem ap_strong {g x : ℕ} (hg : g < 19) (hx : x < 3510) :
    ap (Fi22ChT.F g) x = pt (MonoidHom.id _) (fi22StrongPerm g) x := by
  have e : (fi22StrongArrs[g]!)[x]! = ((fi22StrongPerm g ⟨x, hx⟩ : Fin 3510) : ℕ) :=
    rep_fi22Strong hg ⟨x, hx⟩
  rw [← get_ap hx, ← Fi22X.strong_eq hg, e, pt, dif_pos hx, MonoidHom.id_apply]

theorem strong_memP {g : ℕ} (hg : g < 19) : fi22StrongPerm g ∈ fi22P := by
  have h := fi22Chain_strong_mem ⟨g, hg⟩
  rw [fi22Chain_strong_get] at h
  exact h

@[expose] def PMap (φ : ℕ → ℕ) : Prop :=
  ∃ h ∈ fi22P, ∀ x < 3510, φ x = pt (MonoidHom.id _) h x

theorem pmap_id (φ : ℕ → ℕ) (hφ : ∀ x < 3510, φ x = x) : PMap φ :=
  ⟨1, one_mem _, fun x hx => by rw [hφ x hx, pt_one]⟩

theorem pmap_step (j : ℕ) (hj : j < 19) (φ ψ : ℕ → ℕ) (hψ : PMap ψ)
    (h : ∀ x < 3510, φ x = ap (Fi22ChT.F j) (ψ x)) : PMap φ := by
  obtain ⟨u, hu, hψu⟩ := hψ
  refine ⟨fi22StrongPerm j * u, mul_mem (strong_memP hj) hu, fun x hx => ?_⟩
  rw [h x hx, hψu x hx, ap_strong hj (pt_lt _ _ hx), pt_mul]

theorem tc_lt {f : ℕ} (hf : f < 865) : TC f = CFSG.KD.Fi22Twist.TF f := by
  unfold TC
  rw [blt_tt hf]

theorem ttc_lt {f : ℕ} (hf : f < 865) : TTC f = CFSG.KD.Fi22Twist.TT f := by
  unfold TTC
  rw [blt_tt hf]

theorem tc_mem : ∀ f < 891, PMap (ap (TC f)) := by
  have hTF := tf_sound tf_all PMap pmap_id pmap_step
  intro f
  induction f using Nat.strongRecOn with
  | ind f ih =>
    intro hf
    by_cases hlt : f < 865
    · rw [tc_lt hlt]
      exact hTF f hlt
    have hc : tfK TC TTC Fi22ChT.F f = true := by
      have h := ch431009tf2
      unfold ch431009tf2_ at h
      have hf' : f - 865 < 26 := by omega
      have e := allBlk_spec h (f - 865) hf'
      have ei : Nat.add 865 (f - 865) = f := by
        change 865 + (f - 865) = f
        omega
      rwa [ei] at e
    unfold tfK at hc
    rw [strictB_eqT, strictB_eqT] at hc
    cases hb : Nat.beq (fld(TTC f, 8, 65535)) 0
    · rw [hb] at hc
      change Bool.rec (motive := fun _ => Bool) false _ _ = true at hc
      obtain ⟨h1, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
      obtain ⟨h2, hc⟩ := (CFSG.KS.bAnd_iff _ _).1 hc
      rw [strictB_eqT, strictB_eqT] at hc
      have hpar : fld(TTC f, 24, 65535) < f := Nat.le_of_ble_eq_true h1
      have hj : Nat.shiftRight (TTC f) 40 < 19 := Nat.le_of_ble_eq_true h2
      refine pmap_step _ hj _ _ (ih _ hpar (Nat.lt_trans hpar hf)) fun x hx => ?_
      exact Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec hc x hx)
    · rw [hb] at hc
      exact pmap_id _ fun x hx => Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec hc x hx)

theorem bf_mem : ∀ k < 720, ∃ φ : ℕ → ℕ, PMap φ ∧ (∀ m < 3, φ (bp m) = bp m) ∧
    ∀ p < 9, fld(BF k, Nat.mul 12 p, 4095) = φ (fld(BF 0, Nat.mul 12 p, 4095)) :=
  bf_sound bf_all PMap pmap_id pmap_step

theorem base_list : fi22Chain.base.toList = [(0 : Fin 3510), 1, 2, 3, 6, 4] := by decide

theorem bp_fin {m : ℕ} (hm : m < 6) :
    ∃ b : Fin 3510, (b : ℕ) = bp m ∧ b ∈ fi22Chain.base.toList.take (m + 1) := by
  rw [base_list]
  interval_cases m
  exacts [⟨0, rfl, by decide⟩, ⟨1, rfl, by decide⟩, ⟨2, rfl, by decide⟩, ⟨3, rfl, by decide⟩,
    ⟨6, rfl, by decide⟩, ⟨4, rfl, by decide⟩]

theorem take_bp {i : ℕ} (hi : i ≤ 6) {b : Fin 3510} (hb : b ∈ fi22Chain.base.toList.take i) :
    ∃ m < i, (b : ℕ) = bp m := by
  rw [base_list] at hb
  interval_cases i <;> simp at hb
  all_goals rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact ⟨0, by norm_num, rfl⟩ | exact ⟨1, by norm_num, rfl⟩ | exact ⟨2, by norm_num, rfl⟩
    | exact ⟨3, by norm_num, rfl⟩ | exact ⟨4, by norm_num, rfl⟩ | exact ⟨5, by norm_num, rfl⟩

theorem take_mono {i m : ℕ} (hm : m < i) {b : Fin 3510}
    (hb : b ∈ fi22Chain.base.toList.take (m + 1)) : b ∈ fi22Chain.base.toList.take i :=
  List.take_subset_take_left _ (by omega) hb

theorem fix_of_pt {h : Equiv.Perm (Fin 3510)} {i : ℕ} (hi : i ≤ 6)
    (hfix : ∀ m < i, pt (MonoidHom.id _) h (bp m) = bp m) :
    ∀ b ∈ fi22Chain.base.toList.take i, h b = b := by
  intro b hb
  obtain ⟨m, hm, e⟩ := take_bp hi hb
  have k := hfix m hm
  rw [← e, pt, dif_pos b.2] at k
  exact Fin.ext k

theorem pt_of_fix {h : Equiv.Perm (Fin 3510)} {i : ℕ} (hi : i ≤ 6)
    (hfix : ∀ b ∈ fi22Chain.base.toList.take i, h b = b) :
    ∀ m < i, pt (MonoidHom.id _) h (bp m) = bp m := by
  intro m hm
  obtain ⟨b, e, hb⟩ := bp_fin (m := m) (by omega)
  have k := hfix b (take_mono hm hb)
  rw [← e, pt, dif_pos b.2]
  change ((h b : Fin 3510) : ℕ) = b
  rw [k]

theorem strong_list : fi22Chain.strong.toList = List.ofFn fun j : Fin 19 => fi22StrongPerm j := by
  change (Vector.ofFn fun j : Fin 19 => fi22StrongPerm j).toList = _
  exact Vector.toList_ofFn

theorem lv_orbit {i : ℕ} (hi : i < 6) {h : Equiv.Perm (Fin 3510)} (hP : h ∈ fi22P)
    (hfix : ∀ m < i, pt (MonoidHom.id _) h (bp m) = bp m) :
    ∃ k < szL i, ap (OF i) k = pt (MonoidHom.id _) h (bp i) := by
  have hv := fi22Chain_valid.1
  have hmem : h ∈ fi22Chain.levelSubgroup i :=
    (fi22Chain.mem_levelSubgroup_iff hv i (by change i ≤ 6; omega) h).2
      ⟨hP, fix_of_pt (by omega) hfix⟩
  have hb := lv_base (lv_all (20 * i + 19) (by omega))
  have key : ∀ y ∈ fi22Chain.levelSubgroup i, ∀ x, (∃ k < szL i, ap (OF i) k = x) →
      ∃ k < szL i, ap (OF i) k = pt (MonoidHom.id _) y x := by
    intro y hy
    unfold CFSG.Certificates.RawSchreierDatum.levelSubgroup at hy
    induction hy using Subgroup.closure_induction with
    | mem s hs =>
      obtain ⟨hs1, hs2⟩ := (fi22Chain.mem_levelGenerators_iff i s).1 hs
      rw [strong_list, List.mem_ofFn] at hs1
      obtain ⟨⟨g, hg⟩, rfl⟩ := hs1
      have hfs := pt_of_fix (by change i ≤ 6; omega) hs2
      have hfixS : ∀ m < i, ap (Fi22ChT.F g) (bp m) = bp m := by
        intro m hm
        rw [ap_strong hg (bp_lt6 m (by omega))]
        exact hfs m hm
      have hc := lv_gen hg (lv_all (20 * i + g) (by omega)) hfixS
      rintro x ⟨k, hk, rfl⟩
      obtain ⟨q, hq, e⟩ := hc k hk
      refine ⟨q, hq, ?_⟩
      rw [e, ap_strong hg (hb.2 k hk).1]
    | one =>
      intro x hx
      rwa [pt_one]
    | mul a b _ _ iha ihb =>
      intro x hx
      rw [pt_mul]
      exact iha _ (ihb x hx)
    | inv a _ iha =>
      have hpow : ∀ n : ℕ, ∀ x, (∃ k < szL i, ap (OF i) k = x) →
          ∃ k < szL i, ap (OF i) k = pt (MonoidHom.id _) (a ^ n) x := by
        intro n
        induction n with
        | zero =>
          intro x hx
          rwa [pow_zero, pt_one]
        | succ n ihn =>
          intro x hx
          rw [pow_succ, pt_mul]
          exact ihn _ (iha x hx)
      have hinv : a⁻¹ = a ^ (orderOf a - 1) := by
        refine inv_eq_of_mul_eq_one_left ?_
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]
      intro x hx
      rw [hinv]
      exact hpow _ x hx
  exact key h hmem _ ⟨0, by interval_cases i <;> decide, hb.1⟩

end CertificateChecks.KernelFi22Twist

end
