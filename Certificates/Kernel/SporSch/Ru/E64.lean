
module

public import Certificates.Kernel.SporSch.Ru.E64K
public import Certificates.Kernel.SporSch.Ru.E64Misc
public import CFSG.Quasithin.Vol2.KGFactG2RuE64Base
import Certificates.Kernel.SporSch.Ru.G2Ru7164
import Certificates.Kernel.Misc.RuSq.Bind
import CFSG.Certificates.Kernel.Misc.RuInvCov
import CFSG.Certificates.SchreierBaseImageDecoding
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases
import CFSG.Certificates.Kernel.Common.ForallTree
public import Certificates.Kernel.SporSch.Ru.E64Rows0
public import Certificates.Kernel.SporSch.Ru.E64Rows1
public import Certificates.Kernel.SporSch.Ru.E64Rows2
public import Certificates.Kernel.SporSch.Ru.E64Rows3
public import Certificates.Kernel.SporSch.Ru.E64Keep0
public import Certificates.Kernel.SporSch.Ru.E64Keep1
public import Certificates.Kernel.SporSch.Ru.E64Keep2
public import Certificates.Kernel.SporSch.Ru.E64Keep3
public import CFSG.Sporadic.Schreier.RuSylow
public import CFSG.Sporadic.Schreier.RuTreeElt
import CFSG.Certificates.Kernel.Misc.RuInvHash
import CFSG.Certificates.Kernel.Spor.ClassOneH
import CFSG.Certificates.Kernel.Spor.RawOrbGrp

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuE64

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.RuE64 CertificateChecks.KernelSporSch.RuE64D
open CFSG.Quasithin.H13.Ch4.G2Ru CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open CFSG.KLie.CT (bit popc sumN anyN)

theorem bit_eq (X j : Nat) : bit X j = X.testBit j := by
  have e : bit X j = Nat.beq ((X >>> j) &&& 1) 1 := rfl
  rw [e, Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ j) with h | h <;> rw [h] <;> rfl

theorem popc_eq (w X : Nat) : popc w X = (List.range w).countP (X.testBit ·) := by
  induction w with
  | zero => rfl
  | succ w ih =>
    change ((X >>> w) &&& 1) + popc w X = _
    rw [ih, List.range_succ, List.countP_append, List.countP_singleton, Nat.add_comm]
    congr 1
    rw [Nat.and_one_is_mod, Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
    rcases Nat.mod_two_eq_zero_or_one (X / 2 ^ w) with h | h <;> simp [h]

theorem sumN_eq (n : Nat) (f : Nat → Bool) :
    sumN n (fun i => Bool.rec (motive := fun _ => Nat) 0 1 (f i)) = (List.range n).countP f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Bool.rec (motive := fun _ => Nat) 0 1 (f n) + sumN n _ = _
    rw [ih, List.range_succ, List.countP_append, List.countP_singleton, Nat.add_comm]
    cases f n <;> rfl

theorem anyN_eq (n : Nat) (f : Nat → Bool) : anyN n f = (List.range n).any f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change CFSG.KLie.CT.orB (f n) (anyN n f) = _
    rw [ih, List.range_succ, List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_comm]
    cases f n <;> rfl

theorem allN_eq (n : Nat) (f : Nat → Bool) : allN n f = allLt n f := by
  apply Bool.eq_iff_iff.mpr
  rw [CFSG.KS.Raw.Orb.allN_iff, allLt_iff]

theorem countP_range_congr {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) :
    (List.range n).countP f = (List.range n).countP g :=
  List.countP_congr fun i hi => by rw [h i (List.mem_range.1 hi)]

theorem any_range_congr {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) :
    (List.range n).any f = (List.range n).any g := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range]
  exact ⟨fun ⟨i, hi, e⟩ => ⟨i, hi, (h i hi) ▸ e⟩, fun ⟨i, hi, e⟩ => ⟨i, hi, (h i hi).symm ▸ e⟩⟩

theorem allLt_congr {n : Nat} {f g : Nat → Bool} (h : ∀ i < n, f i = g i) :
    allLt n f = allLt n g := by
  apply Bool.eq_iff_iff.mpr
  rw [allLt_iff, allLt_iff]
  exact ⟨fun hf i hi => (h i hi) ▸ hf i hi, fun hg i hi => (h i hi).symm ▸ hg i hi⟩

theorem eqB_true {a b : Bool} (h : eqB a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem filterMap_ite {α β : Type} (p : α → Bool) (f : α → β) :
    ∀ l : List α, l.filterMap (fun b => if p b = true then some (f b) else none) = (l.filter p).map f
  | [] => rfl
  | a :: l => by
    rw [List.filterMap_cons, List.filter_cons, filterMap_ite p f l]
    cases p a <;> rfl

theorem flatMap_filterMap {α : Type} (k : Nat) (hk : 0 < k) (P : Nat → Nat → Bool)
    (F : Nat → Nat → α) : ∀ m : Nat,
    (List.range m).flatMap (fun a => (List.range k).filterMap fun b =>
        if P a b = true then some (F a b) else none) =
      ((List.range (k * m)).filter fun c => P (c / k) (c % k)).map fun c => F (c / k) (c % k)
  | 0 => by simp
  | m + 1 => by
    rw [List.range_succ, List.flatMap_append, flatMap_filterMap k hk P F m,
      show k * (m + 1) = k * m + k by ring, List.range_add, List.filter_append,
      List.map_append, List.flatMap_singleton]
    congr 1
    rw [List.filter_map, List.map_map, filterMap_ite]
    have e1 : ∀ b ∈ List.range k, (k * m + b) / k = m ∧ (k * m + b) % k = b := by
      intro b hb
      have hb' := List.mem_range.1 hb
      refine ⟨?_, ?_⟩
      · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt hb', Nat.zero_add]
      · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb']
    have hf : (List.range k).filter ((fun c => P (c / k) (c % k)) ∘ fun b => k * m + b) =
        (List.range k).filter (P m) :=
      List.filter_congr fun b hb => by
        simp only [Function.comp_apply, (e1 b hb).1, (e1 b hb).2]
    rw [hf]
    apply List.map_congr_left
    intro b hb
    have hb' := (List.mem_filter.1 hb).1
    simp only [Function.comp_apply, (e1 b hb').1, (e1 b hb').2]

theorem eq_of_base {g h : Equiv.Perm (Fin 4060)} (hg : g ∈ ruS) (hh : h ∈ ruS)
    (h1 : g 1 = h 1) (h0 : g 0 = h 0) : g = h := by
  have hA := ruChainS4060_arrays
  have hQ := (validSchreier_of_chainOK hA (by norm_num : 0 < 4) ruInv_check.1).1
  rw [← ruChainS4060_sub] at hg hh
  have hd := (ruChainS4060.schreier_base_image_decoding hQ
    (fun i => g (ruChainS4060.base.get i))).2.1
  have e1 := (hd g).2 ⟨hg, fun _ => rfl⟩
  have e2 := (hd h).2 ⟨hh, fun i => by
    obtain ⟨i, hi⟩ := i
    have hi2 : i < 2 := hi
    interval_cases i
    · exact h1.symm
    · exact h0.symm⟩
  rw [e1] at e2
  exact Option.some.inj e2

noncomputable def gC (c : Nat) : Equiv.Perm (Fin 4060) :=
  ChainArrays.levT 4060 (ruField4060 4) (ruBaseArr 4060 ruS4060ChainBase) 0 (c / 8) *
    ChainArrays.levT 4060 (ruField4060 4) (ruBaseArr 4060 ruS4060ChainBase) 1 (c % 8)

theorem lev_size : (ChainArrays.lev 4060 (ruField4060 4) (ruBaseArr 4060 ruS4060ChainBase) 0).pts.size
      = 2048 ∧
    (ChainArrays.lev 4060 (ruField4060 4) (ruBaseArr 4060 ruS4060ChainBase) 1).pts.size = 8 := by
  have h := ruInv_check.2.1
  unfold rawOrbitSizes at h
  have hs : (rawLevels 4060 (ruField4060 4) (ruBaseArr 4060 ruS4060ChainBase)).size = 2 := by
    have := congrArg List.length h
    simpa using this
  have key : ∀ i (hi : i < 2), (ChainArrays.lev 4060 (ruField4060 4)
      (ruBaseArr 4060 ruS4060ChainBase) i).pts.size = [2048, 8][i] := by
    intro i hi
    have e := List.getElem_of_eq h (i := i) (by simpa [hs] using hi)
    simp only [List.getElem_map, Array.getElem_toList] at e
    rw [ChainArrays.lev, getElem!_pos _ i (by omega)]
    exact e
  exact ⟨key 0 (by norm_num), key 1 (by norm_num)⟩

theorem gC_mem {c : Nat} (hc : c < 16384) : gC c ∈ ruS := by
  have hA := ruChainS4060_arrays
  rw [← ruChainS4060_sub]
  exact Subgroup.mul_mem _
    (chain_levT_mem_original hA (by norm_num) ruInv_check.1 (by decide)
      (by rw [lev_size.1]; omega))
    (chain_levT_mem_original hA (by norm_num) ruInv_check.1 (by decide)
      (by rw [lev_size.2]; omega))

theorem rep_gC {c : Nat} (hc : c < 16384) :
    Rep 4060 (prod2A 4060 ruLevS (c / 8) (c % 8)) (gC c) :=
  chain_rep_prod2A ruChainS4060_arrays ruInv_check.1 (by rw [ruChainS4060_baseCount])
    (by rw [lev_size.1]; omega) (by rw [lev_size.2]; omega)

theorem tr_pt {i k : Nat} (hi : i < 2) (hk : k < (ChainArrays.lev 4060 (ruField4060 4)
    (ruBaseArr 4060 ruS4060ChainBase) i).pts.size) (x : Fin 4060) :
    ap (trK LR TR i k) x = (ChainArrays.levT 4060 (ruField4060 4)
      (ruBaseArr 4060 ruS4060ChainBase) i k x : ℕ) := by
  obtain ⟨hsz, hP⟩ := CFSG.KC.Misc.RuInv.P.lev2 CertificateChecks.KernelMisc.RuSq.bindsSq
    CertificateChecks.KernelMisc.RuSq.permS CertificateChecks.KernelMisc.RuSqS.hl hi
  have hk' : k < rcnt (LR i) := by
    rw [← hsz]
    exact hk
  obtain ⟨g, hr, hp⟩ := hP k hk'
  have hr' := (ruChainS4060_arrays.rep_levT (chainCheckFacts ruInv_check.1)
    (by rw [ruChainS4060_baseCount]; omega) hk)
  rw [Rep.unique hr' hr]
  exact hp x

theorem ev_eq {c : Nat} (hc : c < 16384) (x : Fin 4060) : evK LR TR c x = (gC c x : ℕ) := by
  unfold evK
  have h1 := tr_pt (i := 1) (k := c % 8) (by norm_num) (by rw [lev_size.2]; omega) x
  rw [h1]
  have h0 := tr_pt (i := 0) (k := c / 8) (by norm_num) (by rw [lev_size.1]; omega)
    (ChainArrays.levT 4060 (ruField4060 4) (ruBaseArr 4060 ruS4060ChainBase) 1 (c % 8) x)
  rw [h0, gC, Equiv.Perm.mul_apply]

theorem ev_lt {c : Nat} (hc : c < 16384) (x : Fin 4060) : evK LR TR c x < 4060 := by
  rw [ev_eq hc]
  exact (gC c x).2

theorem ev1 {c : Nat} (hc : c < 16384) : evK LR TR c 1 = (gC c 1 : ℕ) := ev_eq hc 1

theorem ev0 {c : Nat} (hc : c < 16384) : evK LR TR c 0 = (gC c 0 : ℕ) := ev_eq hc 0

theorem fin_eq_iff {a b : Fin 4060} : a = b ↔ (a : ℕ) = b := Fin.ext_iff

theorem beq_dec (a b : Nat) : Nat.beq a b = decide (a = b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.beq_eq]

theorem bAnd_eq' (a b : Bool) : bAnd(a, b) = (a && b) := by cases a <;> rfl

theorem bNot_eq (c : Bool) : bIf(c, false, true) = !c := by cases c <;> rfl

theorem blt_dec (a b : Nat) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]

theorem ble_dec (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.ble_eq]

theorem invK_form (a1 a0 b1 b0 : Nat) :
    bAnd(Nat.beq b1 1, bAnd(Nat.beq b0 0, bIf(bAnd(Nat.beq a1 1, Nat.beq a0 0), false, true))) =
      true ↔ ((b1 = 1 ∧ b0 = 0) ∧ ¬(a1 = 1 ∧ a0 = 0)) := by
  by_cases h1 : b1 = 1 <;> by_cases h0 : b0 = 0 <;> by_cases g1 : a1 = 1 <;>
    by_cases g0 : a0 = 0 <;> simp [beq_dec, bAnd_eq', bNot_eq, h1, h0, g1, g0]

theorem invol_eq {c : Nat} (hc : c < 16384) :
    ruIsInvolA (prod2A 4060 ruLevS (c / 8) (c % 8)) = invK LR TR c := by
  have hm := gC_mem hc
  have hsq : gC c * gC c = 1 ↔ (gC c * gC c) 1 = (1 : Equiv.Perm (Fin 4060)) 1 ∧
      (gC c * gC c) 0 = (1 : Equiv.Perm (Fin 4060)) 0 :=
    ⟨fun h => by rw [h]; exact ⟨rfl, rfl⟩, fun ⟨h1, h0⟩ => eq_of_base (ruS.mul_mem hm hm)
      ruS.one_mem h1 h0⟩
  have hone : gC c = 1 ↔ gC c 1 = (1 : Equiv.Perm (Fin 4060)) 1 ∧
      gC c 0 = (1 : Equiv.Perm (Fin 4060)) 0 :=
    ⟨fun h => by rw [h]; exact ⟨rfl, rfl⟩, fun ⟨h1, h0⟩ => eq_of_base hm ruS.one_mem h1 h0⟩
  apply Bool.eq_iff_iff.mpr
  rw [ruIsInvolA_iff (rep_gC hc)]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [orderOf_eq_prime_iff, pow_two, hsq, ne_eq, hone]
  unfold invK
  rw [ev1 hc, ev0 hc, ev_eq hc, ev_eq hc, invK_form]
  simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply, fin_eq_iff]
  exact Iff.rfl

theorem cd_lt {i : Nat} (hi : i < 687) : cd i < 16384 :=
  Nat.blt_eq.mp (CFSG.KS.Raw.Orb.allN_iff.1 cdLt i hi)

theorem g2Inv_list : g2Inv = ((List.range 687).map fun i =>
    prod2A 4060 ruLevS (cd i / 8) (cd i % 8)).toArray := by
  have hs0 : ruLevS[0]!.pts.size = 2048 := lev_size.1
  have hs1 : ruLevS[1]!.pts.size = 8 := lev_size.2
  unfold g2Inv
  rw [hs0, hs1]
  have e := flatMap_filterMap (α := Array ℕ) 8 (by norm_num)
    (fun a b => ruIsInvolA (prod2A 4060 ruLevS a b)) (fun a b => prod2A 4060 ruLevS a b) 2048
  rw [e]
  apply congrArg List.toArray
  have hf : (List.range (8 * 2048)).filter (fun c => ruIsInvolA (prod2A 4060 ruLevS (c / 8) (c % 8)))
      = (List.range 16384).filter (invK LR TR) :=
    List.filter_congr fun c hc => invol_eq (List.mem_range.1 hc)
  rw [hf, ← codesOK, List.map_map]
  apply List.map_congr_left
  intro i _
  rfl

theorem g2Inv_size : g2Inv.size = 687 := by
  rw [g2Inv_list]
  simp

theorem g2Inv_get {i : Nat} (hi : i < 687) :
    g2Inv[i]! = prod2A 4060 ruLevS (cd i / 8) (cd i % 8) := by
  rw [g2Inv_list, getElem!_pos _ i (by simpa using hi)]
  simp

theorem rep_inv {i : Nat} (hi : i < 687) : Rep 4060 g2Inv[i]! (gC (cd i)) := by
  rw [g2Inv_get hi]
  exact rep_gC (cd_lt hi)

theorem com_eq {i j : Nat} (hi : i < 687) (hj : j < 687) :
    (g2ComM[i]!)[j]! = comK LR TR (cd i) (cd j) := by
  rw [g2ComM_get (by rw [g2Inv_size]; exact hi) (by rw [g2Inv_size]; exact hj)]
  have hmi := gC_mem (cd_lt hi)
  have hmj := gC_mem (cd_lt hj)
  apply Bool.eq_iff_iff.mpr
  rw [g2Com_iff (rep_inv hi) (rep_inv hj)]
  unfold comK
  rw [ev1 (cd_lt hj), ev0 (cd_lt hj), ev1 (cd_lt hi), ev0 (cd_lt hi), ev_eq (cd_lt hi),
    ev_eq (cd_lt hi), ev_eq (cd_lt hj), ev_eq (cd_lt hj)]
  simp only [bAnd_eq', beq_dec, Bool.and_eq_true, decide_eq_true_iff, ← fin_eq_iff]
  constructor
  · intro h
    have h1 := congrArg (fun g : Equiv.Perm (Fin 4060) => g 1) h
    have h0 := congrArg (fun g : Equiv.Perm (Fin 4060) => g 0) h
    exact ⟨h1, h0⟩
  · rintro ⟨h1, h0⟩
    exact eq_of_base (ruS.mul_mem hmi hmj) (ruS.mul_mem hmj hmi) h1 h0

theorem wr_get {r e : Nat} (hr : r < 4) (he : e < 64) :
    (g2WrArr[r]!)[e]! = unpack 4060 12 (U r e) := by
  have hsz : g2WArr.size = 64 := by rw [g2WArr, Array.size_ofFn]
  have hw : g2WArr[e]! = g2WProd e := by
    rw [getElem!_pos g2WArr e (by rw [hsz]; exact he)]
    unfold g2WArr
    rw [Array.getElem_ofFn]
  rw [g2WrArr, getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn,
    getElem!_pos _ e (by rw [Array.size_map, hsz]; exact he), Array.getElem_map,
    ← getElem!_pos g2WArr e (by rw [hsz]; exact he), hw]
  obtain ⟨s1, s2⟩ := G2Ru7164.sw_eq (w := g2ConjWords.getD r []) (by
    interval_cases r <;> decide)
  obtain ⟨w1, w2⟩ := G2Ru7164.wprod_eq e
  unfold ruConjA
  rw [s1, w1]
  exact (G2Ru7164.conj_eq s2 w2).1

theorem rep_wr {r e : Nat} (hr : r < 4) (he : e < 64) :
    Rep 4060 ((g2WrArr[r]!)[e]!) (g2Sigma r * g2WElt e * (g2Sigma r)⁻¹) := by
  have hent : (g2WrArr[r]!)[e]! = ruConjA (g2SW (g2ConjWords.getD r [])) g2WArr[e]! := by
    rw [g2WrArr, getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn,
      getElem!_pos _ e (by simpa [g2WArr] using he), Array.getElem_map,
      ← getElem!_pos g2WArr e (by simpa [g2WArr] using he)]
  rw [hent]
  exact rep_ruConjA (rep_g2Sigma hr) (rep_g2WArr he)

theorem wr_mem (r e : Nat) : g2Sigma r * g2WElt e * (g2Sigma r)⁻¹ ∈ ruS :=
  ruS.mul_mem (ruS.mul_mem (g2Sigma_mem r) (g2W_le (g2WElt_mem e))) (ruS.inv_mem (g2Sigma_mem r))

theorem ub_eq {r e : Nat} (hr : r < 4) (he : e < 64) :
    ub r (2 * e) = (((g2Sigma r * g2WElt e * (g2Sigma r)⁻¹) 1 : Fin 4060) : ℕ) ∧
      ub r (2 * e + 1) = (((g2Sigma r * g2WElt e * (g2Sigma r)⁻¹) 0 : Fin 4060) : ℕ) := by
  have hc : ubC r = true := by
    interval_cases r
    · exact ub0
    · exact ub1
    · exact ub2
    · exact ub3
  have h := CFSG.KS.Raw.Orb.allN_iff.1 hc e he
  obtain ⟨h1, h0⟩ := (bAnd_iff _ _).1 h
  have hr' := rep_wr hr he
  rw [wr_get hr he] at hr'
  have a1 := hr'.apply (i := 1) (by norm_num)
  have a0 := hr'.apply (i := 0) (by norm_num)
  rw [CFSG.KS.Raw.Orb.unpack_get (by norm_num)] at a1 a0
  exact ⟨(Nat.eq_of_beq_eq_true h1).trans a1, (Nat.eq_of_beq_eq_true h0).trans a0⟩

theorem w_rows {r : Nat} (hr : r < 4) : wC r = true := by
  interval_cases r
  · exact w0
  · exact w1
  · exact w2
  · exact w3

theorem inW_eq {r j : Nat} (hr : r < 4) (hj : j < 687) : (g2InWM[r]!)[j]! = bit (W r) j := by
  have hw := eqB_true (CFSG.KS.Raw.Orb.allN_iff.1 (w_rows hr) j hj)
  rw [hw, g2InWM_get hr (by rw [g2Inv_size]; exact hj)]
  unfold inWK
  rw [anyN_eq]
  have hsz : (g2WrArr[r]!).size = 64 := by
    rw [g2WrArr, getElem!_pos _ r (by simpa using hr), Array.getElem_ofFn]
    simp [g2WArr]
  have key : ∀ e < 64, eqA 4060 g2Inv[j]! ((g2WrArr[r]!)[e]!) =
      bAnd(Nat.beq (evK LR TR (cd j) 1) (ub r (2 * e)),
        Nat.beq (evK LR TR (cd j) 0) (ub r (2 * e + 1))) := by
    intro e he
    obtain ⟨u1, u0⟩ := ub_eq hr he
    rw [u1, u0, ev1 (cd_lt hj), ev0 (cd_lt hj)]
    apply Bool.eq_iff_iff.mpr
    rw [eqA_iff (rep_inv hj) (rep_wr hr he), bAnd_iff]
    constructor
    · intro h
      rw [h]
      exact ⟨Nat.beq_refl _, Nat.beq_refl _⟩
    · rintro ⟨h1, h0⟩
      exact eq_of_base (gC_mem (cd_lt hj)) (wr_mem r e) (Fin.ext (Nat.eq_of_beq_eq_true h1))
        (Fin.ext (Nat.eq_of_beq_eq_true h0))
  apply Bool.eq_iff_iff.mpr
  rw [Array.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨e, he, h⟩
    rw [hsz] at he
    refine ⟨e, List.mem_range.2 he, ?_⟩
    rw [← key e he, getElem!_pos (g2WrArr[r]!) e (by rw [hsz]; exact he)]
    exact h
  · rintro ⟨e, he, h⟩
    have he' := List.mem_range.1 he
    refine ⟨e, by rw [hsz]; exact he', ?_⟩
    rw [← key e he', getElem!_pos (g2WrArr[r]!) e (by rw [hsz]; exact he')] at h
    exact h

#kc_forall_tree rowAll (fun i => rowC i = true) 687 CertificateChecks.KernelSporSch.RuE64.rowC
#kc_forall_tree keepAll (fun i => keepC i = true) 687 CertificateChecks.KernelSporSch.RuE64.keepC

theorem com_bit {i j : Nat} (hi : i < 687) (hj : j < 687) : (g2ComM[i]!)[j]! = bit (R i) j := by
  rw [com_eq hi hj, eqB_true (CFSG.KS.Raw.Orb.allN_iff.1 (rowAll i hi) j hj)]

theorem cn_eq {i j : Nat} (hi : i < 687) (hj : j < 687) :
    g2Cn i j = popc 687 (Nat.land (R i) (R j)) := by
  unfold g2Cn
  rw [g2Inv_size, popc_eq]
  apply countP_range_congr
  intro k hk
  rw [com_bit hi hk, com_bit hj hk, bit_eq, bit_eq]
  exact (Nat.testBit_and _ _ _).symm

theorem keep_bit {i j : Nat} (hi : i < 687) (hj : j < 687) : (g2KeepM[i]!)[j]! = bit (K i) j := by
  rw [eqB_true (CFSG.KS.Raw.Orb.allN_iff.1 (keepAll i hi) j hj),
    g2KeepM_get (by rw [g2Inv_size]; exact hi) (by rw [g2Inv_size]; exact hj), com_bit hi hj,
    cn_eq hi hj]
  unfold keepK
  rw [beq_dec, bNot_eq, ble_dec, bAnd_eq', bAnd_eq']
  by_cases hij : i = j
  · simp [hij]
  · simp [hij, Bool.and_assoc]

theorem deg_eq {i : Nat} (hi : i < 687) : g2DegA[i]! = deg i := by
  rw [g2DegA_get (by rw [g2Inv_size]; exact hi), g2Inv_size,
    Nat.eq_of_beq_eq_true (CFSG.KS.Raw.Orb.allN_iff.1 degC i hi), popc_eq]
  apply countP_range_congr
  intro j hj
  rw [keep_bit hi hj, bit_eq]

theorem multi_eq {i : Nat} (hi : i < 687) : g2Multi i = multiK W i := by
  unfold g2Multi multiK
  rw [sumN_eq]
  have e : (List.range 4).countP (fun r => (g2InWM[r]!)[i]!) =
      (List.range 4).countP (fun r => bit (W r) i) :=
    countP_range_congr fun r hr => inW_eq hr hi
  rw [e, ble_dec]

theorem local_eq {i : Nat} (hi : i < 687) : g2E64Local i = localK 687 K deg W i := by
  unfold g2E64Local localK
  rw [deg_eq hi, multi_eq hi, anyN_eq, g2Inv_size]
  have e : (List.range 4).any (fun r => (g2InWM[r]!)[i]! && allLt 687 fun j =>
      !(g2KeepM[i]!)[j]! || decide (g2DegA[j]! < 62) || (g2InWM[r]!)[j]!) =
      (List.range 4).any (fun r => bAnd(bit (W r) i, allN 687 fun j =>
        bIf(bit (K i) j, bIf(Nat.blt (deg j) 62, true, bit (W r) j), true))) := by
    apply any_range_congr
    intro r hr
    rw [inW_eq hr hi, allN_eq]
    have e2 : allLt 687 (fun j => !(g2KeepM[i]!)[j]! || decide (g2DegA[j]! < 62) ||
        (g2InWM[r]!)[j]!) = allLt 687 (fun j => bIf(bit (K i) j, bIf(Nat.blt (deg j) 62, true,
          bit (W r) j), true)) := by
      apply allLt_congr
      intro j hj
      rw [keep_bit hi hj, deg_eq hj, inW_eq hr hj, blt_dec]
      cases decide (deg j < 62) <;> cases bit (K i) j <;> rfl
    rw [e2]
    cases bit (W r) i <;> rfl
  rw [e, blt_dec]
  cases decide (deg i < 62) <;> cases multiK W i <;> rfl

theorem check_eq : g2E64Check = e64K 687 K deg W := by
  unfold g2E64Check e64K
  rw [g2Inv_size, allN_eq, sumN_eq]
  have e1 : allLt 687 g2E64Local = allLt 687 (localK 687 K deg W) :=
    allLt_congr fun i hi => local_eq hi
  have e2 : (List.range 687).countP g2Multi = (List.range 687).countP (multiK W) :=
    countP_range_congr fun i hi => multi_eq hi
  rw [e1, e2, ble_dec, bAnd_eq']

theorem e64Check : g2E64Check = true := by
  rw [check_eq]
  exact fin

end CertificateChecks.KernelSporSch.RuE64

end
