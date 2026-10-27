module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM12Inputs
public import Certificates.Kernel.M12Ctr.Check

public section

namespace Certificates.KernelM12Ctr

open Equiv Certificates.KernelM12Ctr
open CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

@[expose] def gensL : List (Perm (Fin 12)) :=
  M12Lat.tGens ++ [permOf 12 [[0, 4], [1, 8], [2, 5], [3, 10], [6, 7], [9, 11]]]

theorem allB_iff (n : Nat) (p : Nat → Bool) : allB n p = true ↔ ∀ k < n, p k = true := by
  induction n with
  | zero => exact ⟨fun _ k hk => absurd hk (Nat.not_lt_zero k), fun _ => rfl⟩
  | succ n ih =>
    have e : allB (n + 1) p = (p n && allB n p) := rfl
    rw [e, Bool.and_eq_true, ih]
    refine ⟨fun ⟨h1, h2⟩ k hk => ?_, fun h => ⟨h n (Nat.lt_succ_self n), fun k hk => h k (by omega)⟩⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact h2 k hk
    · exact h1

theorem tab_lt : ∀ k : Fin 4, ∀ i : Fin 12, ((gensL.getD k.val 1) i).val = ap k.val i.val := by
  decide +kernel

theorem tab_eq (k : Nat) (i : Fin 12) : ((gensL.getD k 1) i).val = ap k i.val := by
  by_cases hk : k < 4
  · exact tab_lt ⟨k, hk⟩ i
  · have hl1 : gensL.length = 4 := rfl
    have hl2 : tabs.length = 4 := rfl
    have h1 : gensL.getD k 1 = 1 := List.getD_eq_default _ _ (by omega)
    have h2 : tabs.getD k [] = [] := List.getD_eq_default _ _ (by omega)
    rw [h1, Perm.one_apply, ap, h2, List.getD_nil]

theorem getD_mem (k : Nat) : gensL.getD k 1 ∈ Subgroup.closure {g | g ∈ gensL} := by
  by_cases hk : k < gensL.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact Subgroup.subset_closure (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Subgroup.one_mem _

@[expose] def wordP (ws : List Nat) : Perm (Fin 12) := (ws.map fun k => gensL.getD k 1).prod

theorem wordP_mem (ws : List Nat) : wordP ws ∈ Subgroup.closure {g | g ∈ gensL} := by
  refine list_prod_mem fun g hg => ?_
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hg
  exact getD_mem k

theorem wordP_apply (ws : List Nat) (i : Fin 12) : (wordP ws i).val = evalW ws i.val := by
  induction ws with
  | nil => rfl
  | cons k ws ih =>
    have e1 : wordP (k :: ws) = gensL.getD k 1 * wordP ws := by simp [wordP]
    have e2 : evalW (k :: ws) i.val = ap k (evalW ws i.val) := rfl
    rw [e1, Perm.mul_apply, tab_eq, ih, e2]

@[expose] def toF (h : Perm (Fin 12)) (x : Nat) : Nat := if hx : x < 12 then (h ⟨x, hx⟩).val else x

theorem toF_lt (h : Perm (Fin 12)) (x : Nat) (hx : x < 12) : toF h x < 12 := by
  simp only [toF, hx, dite_true]
  exact (h ⟨x, hx⟩).isLt

theorem imgF_congr {f g : Nat → Nat} (hfg : ∀ x < 12, f x = g x) (n : Nat) :
    imgF f n = imgF g n := by
  simp only [imgF]
  rw [hfg _ (Nat.mod_lt _ (by omega)), hfg _ (Nat.mod_lt _ (by omega)),
    hfg _ (Nat.mod_lt _ (by omega))]

theorem enc3_lt {a b c : Nat} (ha : a < 12) (hb : b < 12) (hc : c < 12) : enc3 a b c < 1728 := by
  simp only [enc3]
  omega

theorem imgF_toF_lt (h : Perm (Fin 12)) (n : Nat) : imgF (toF h) n < 1728 :=
  enc3_lt (toF_lt h _ (Nat.mod_lt _ (by omega))) (toF_lt h _ (Nat.mod_lt _ (by omega)))
    (toF_lt h _ (Nat.mod_lt _ (by omega)))

theorem imgF_enc3 (f : Nat → Nat) {a b c : Nat} (ha : a < 12) (hb : b < 12) (hc : c < 12) :
    imgF f (enc3 a b c) = enc3 (f a) (f b) (f c) := by
  have e1 : (144 * a + 12 * b + c) / 144 % 12 = a := by omega
  have e2 : (144 * a + 12 * b + c) / 12 % 12 = b := by omega
  have e3 : (144 * a + 12 * b + c) % 12 = c := by omega
  simp only [imgF, enc3, e1, e2, e3]

theorem toF_mul (g h : Perm (Fin 12)) (x : Nat) (hx : x < 12) : toF (g * h) x = toF g (toF h x) := by
  simp only [toF, hx, dite_true, Perm.mul_apply]
  rw [dif_pos (h ⟨x, hx⟩).isLt]

theorem imgF_toF_mul (g h : Perm (Fin 12)) (n : Nat) :
    imgF (toF (g * h)) n = imgF (toF g) (imgF (toF h) n) := by
  have ha := Nat.mod_lt (n / 144) (show 12 > 0 by omega)
  have hb := Nat.mod_lt (n / 12) (show 12 > 0 by omega)
  have hc := Nat.mod_lt n (show 12 > 0 by omega)
  have e : imgF (toF h) n = enc3 (toF h (n / 144 % 12)) (toF h (n / 12 % 12)) (toF h (n % 12)) :=
    rfl
  rw [e, imgF_enc3 _ (toF_lt h _ ha) (toF_lt h _ hb) (toF_lt h _ hc)]
  simp only [imgF, toF_mul g h _ ha, toF_mul g h _ hb, toF_mul g h _ hc]

@[expose] def Pres (V : Nat) (h : Perm (Fin 12)) : Prop :=
  ∀ n < 1728, V.testBit n = true → V.testBit (imgF (toF h) n) = true

theorem pres_mul {V : Nat} {g h : Perm (Fin 12)} (hg : Pres V g) (hh : Pres V h) :
    Pres V (g * h) := fun n hn hV => by
  rw [imgF_toF_mul]
  exact hg _ (imgF_toF_lt h n) (hh n hn hV)

theorem pres_one (V : Nat) : Pres V 1 := fun n hn hV => by
  have e : imgF (toF 1) n = n := by
    have e1 : ∀ x < 12, toF 1 x = x := fun x hx => by simp [toF, hx]
    rw [imgF_congr e1]
    simp only [imgF, enc3]
    omega
  rw [e]
  exact hV

theorem pres_pow {V : Nat} {h : Perm (Fin 12)} (hh : Pres V h) (m : Nat) : Pres V (h ^ m) := by
  induction m with
  | zero => exact pres_one V
  | succ m ih => rw [pow_succ]; exact pres_mul ih hh

theorem pres_inv {V : Nat} {h : Perm (Fin 12)} (hh : Pres V h) : Pres V h⁻¹ := by
  have hpos := orderOf_pos h
  have e : h ^ (orderOf h - 1) * h = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [← eq_inv_of_mul_eq_one_left e]
  exact pres_pow hh _

theorem pres_closure {V : Nat}
    (hV : ∀ n < 1728, V.testBit n = true → ∀ k < 4, V.testBit (imgF (ap k) n) = true)
    {h : Perm (Fin 12)} (hh : h ∈ Subgroup.closure {g | g ∈ gensL}) : Pres V h := by
  induction hh using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    intro n hn hVn
    have e : ∀ x < 12, toF gensL[k] x = ap k x := fun x hx => by
      have := tab_eq k ⟨x, hx⟩
      rw [List.getD_eq_getElem _ _ hk] at this
      simp only [toF, hx, dite_true, this]
    rw [imgF_congr e]
    exact hV n hn hVn k hk
  | one => exact pres_one V
  | mul g h _ _ hg hh => exact pres_mul hg hh
  | inv g _ hg => exact pres_inv hg

theorem tupChk_spec {V x : Nat} {f : Nat → Nat} (h : tupChk V x f = true) :
    (∀ n < 1728, V.testBit n = true → ∀ k < 4, V.testBit (imgF (ap k) n) = true) ∧
      V.testBit x = true ∧ V.testBit (imgF f x) = false := by
  simp only [tupChk, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun n hn hVn k hk => ?_, h2, h3⟩
  have := (allB_iff _ _).mp h1 n hn
  rw [hVn, Bool.not_true, Bool.false_or, allB_iff] at this
  exact this k hk

theorem orb_spec (i : Fin 12) : (wordP (orbW.getD i.val []) 0).val = i.val := by
  have h := kOrb
  rw [orbOK, orbChk, allB_iff] at h
  have := h i.val i.isLt
  rw [beq_iff_eq] at this
  rw [wordP_apply]
  exact this

theorem cent_spec (q : Nat) (hq : q < 12) (h : commB (fq q) = true) : q = 0 ∨ q = 1 := by
  have hc := kCent
  rw [centOK, allB_iff] at hc
  have := hc q hq
  rw [h, Bool.not_true, Bool.or_false, Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at this
  exact this

theorem center_trivial (w : Perm (Fin 12))
    (hw : w ∈ Subgroup.closure {g | g ∈ M12Lat.tGens ++
      [permOf 12 [[0, 4], [1, 8], [2, 5], [3, 10], [6, 7], [9, 11]]]})
    (hc : ∀ g ∈ M12Lat.tGens ++ [permOf 12 [[0, 4], [1, 8], [2, 5], [3, 10], [6, 7], [9, 11]]],
      w * g = g * w) : w = 1 := by
  change w ∈ Subgroup.closure {g | g ∈ gensL} at hw
  change ∀ g ∈ gensL, w * g = g * w at hc
  have hle : Subgroup.closure {g | g ∈ gensL} ≤ Subgroup.centralizer {w} := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hc g hg
  have hcomm : ∀ h ∈ Subgroup.closure {g | g ∈ gensL}, w * h = h * w := fun h hh =>
    (Subgroup.mem_centralizer_iff.mp (hle hh)) w rfl
  have hwf : ∀ i : Fin 12, (w i).val = fq (w 0).val i.val := by
    intro i
    have h0 : wordP (orbW.getD i.val []) 0 = i := Fin.ext (orb_spec i)
    have e := congrArg (fun p : Perm (Fin 12) => p 0) (hcomm _ (wordP_mem (orbW.getD i.val [])))
    simp only [Perm.mul_apply, h0] at e
    rw [e, wordP_apply]
    rfl
  have hfc : commB (fq (w 0).val) = true := by
    rw [commB, allB_iff]
    intro k _
    rw [allB_iff]
    intro i hi
    rw [beq_iff_eq]
    have e := congrArg (fun p : Perm (Fin 12) => p ⟨i, hi⟩) (hcomm _ (getD_mem k))
    simp only [Perm.mul_apply] at e
    have e1 := hwf (gensL.getD k 1 ⟨i, hi⟩)
    rw [tab_eq] at e1
    rw [← e1, e, tab_eq, hwf]
  rcases cent_spec _ (w 0).isLt hfc with h0 | h1
  · ext i
    rw [hwf, h0]
    have := orb_spec i
    rw [wordP_apply] at this
    exact this
  · exfalso
    obtain ⟨hV, h54, hc1⟩ := tupChk_spec (V := orbMask 54 192) (x := 54) (f := fq 1)
      (by rw [← tupOK.eq_1]; exact kTup)
    have hp := pres_closure hV hw 54 (by omega) h54
    have e : ∀ x < 12, toF w x = fq 1 x := fun x hx => by
      have := hwf ⟨x, hx⟩
      rw [h1] at this
      simp only [toF, hx, dite_true, this]
    rw [imgF_congr e, hc1] at hp
    exact Bool.false_ne_true hp

end Certificates.KernelM12Ctr

end
