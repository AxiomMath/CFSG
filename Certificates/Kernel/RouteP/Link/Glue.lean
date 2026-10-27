module

public import Certificates.Kernel.RouteP.Link.Checks
public import Certificates.Kernel.RouteP.Text.CoverGens
public import Certificates.Kernel.RouteP.Pres.Rep
public import Certificates.Kernel.RouteP.Cocode.Glue
public import Certificates.Kernel.RouteP.Y332.Glue
public import CFSG.Certificates.Kernel.RouteP.MTabs
public import CFSG.Certificates.Kernel.Common.ForallTree

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.KC.Fi24Net CFSG.Sporadic.Th
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

#kc_forall_tree lkP_all (fun g => CFSG.KD.RouteP.lkP g = true) 42 CFSG.KD.RouteP.LinkCk.p
#kc_forall_tree lkO_all (fun g => CFSG.KD.RouteP.lkO g = true) 42 CFSG.KD.RouteP.LinkCk.o
#kc_forall_tree lkY_all (fun g => CFSG.KD.RouteP.lkY g = true) 42 CFSG.KD.RouteP.LinkCk.y

theorem lk_spec {NW : Nat → Nat → Nat} {KA KB : Nat → Nat} (h : ∀ g < 42, lkck NW KA KB g = true) :
    (∀ k < 19, genOK CG (NW 0) 0 k = true) ∧ (∀ k < 19, genOK CG (NW 1) 32 k = true) ∧
      kapLinkOK CG (KA 0) 19 = true ∧ kapLinkOK CG (KB 0) 20 = true ∧
      kapLinkOK CG (KA 1) 51 = true ∧ kapLinkOK CG (KB 1) 52 = true := by
  refine ⟨fun k hk => ?_, fun k hk => ?_, h 38 (by decide), h 39 (by decide), h 40 (by decide),
    h 41 (by decide)⟩
  · have hg := h k (by omega)
    unfold lkck at hg
    have e1 : Nat.blt k 38 = true := Nat.blt_eq.mpr (by omega)
    have e2 : Nat.div k 19 = 0 := by change k / 19 = 0; omega
    have e3 : Nat.mod k 19 = k := by change k % 19 = k; omega
    rw [e1, e2, e3] at hg
    exact hg
  · have hg := h (19 + k) (by omega)
    unfold lkck at hg
    have e1 : Nat.blt (19 + k) 38 = true := Nat.blt_eq.mpr (by omega)
    have e2 : Nat.div (19 + k) 19 = 1 := by change (19 + k) / 19 = 1; omega
    have e3 : Nat.mod (19 + k) 19 = k := by change (19 + k) % 19 = k; omega
    rw [e1, e2, e3] at hg
    exact hg

theorem and3_eq (z : Nat) : z &&& 3 = (if z.testBit 0 then 1 else 0) + (if z.testBit 1 then 2 else 0) := by
  have e : (3 : Nat) = 2 ^ 2 - 1 := rfl
  have t0 : z.testBit 0 = (z % 2 ^ 2).testBit 0 := by rw [Nat.testBit_mod_two_pow]; simp
  have t1 : z.testBit 1 = (z % 2 ^ 2).testBit 1 := by rw [Nat.testBit_mod_two_pow]; simp
  rw [e, Nat.and_two_pow_sub_one_eq_mod, t0, t1]
  have hr : z % 2 ^ 2 < 4 := Nat.mod_lt _ (by decide)
  generalize z % 2 ^ 2 = r at hr ⊢
  interval_cases r <;> decide

theorem cgd_rec (p : Nat) (_ : p < 306936) :
    CGD 0 p = recF CG 0 p + 1 ∧ CGD 1 p = kb CG 19 p ∧ CGD 2 p = recF CG 32 p + 1 ∧
      CGD 3 p = kb CG 51 p := by
  have hR : CGR p = (CG (p / 512) >>> (64 * (p % 512))) % 2 ^ 64 := by
    unfold CGR
    have e1 : Nat.shiftRight p 9 = p / 512 := Nat.shiftRight_eq_div_pow p 9
    have e2 : Nat.land p 511 = p % 512 := Nat.and_two_pow_sub_one_eq_mod p 9
    have e3 : (18446744073709551615 : Nat) = 2 ^ 64 - 1 := rfl
    change Nat.land (Nat.shiftRight (CG (Nat.shiftRight p 9)) (Nat.land p 511 * 64)) 18446744073709551615 = _
    rw [e1, e2, e3, Nat.mul_comm]
    exact Nat.and_two_pow_sub_one_eq_mod _ 64
  have e19 : (524287 : Nat) = 2 ^ 19 - 1 := rfl
  have d0 : CGD 0 p = Nat.land (Nat.shiftRight (CGR p) 0) 524287 + 1 := rfl
  have d1 : CGD 1 p = Nat.land (Nat.shiftRight (CGR p) 19) 3 := rfl
  have d2 : CGD 2 p = Nat.land (Nat.shiftRight (CGR p) 32) 524287 + 1 := rfl
  have d3 : CGD 3 p = Nat.land (Nat.shiftRight (CGR p) 51) 3 := rfl
  have tb : ∀ o i, o + i < 64 → (Nat.shiftRight (CGR p) o).testBit i =
      (CG (p / 512)).testBit (64 * (p % 512) + (o + i)) := by
    intro o i hoi
    change (CGR p >>> o).testBit i = _
    rw [hR, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    simp [hoi]
  have fl : ∀ o, o + 19 ≤ 64 → Nat.land (Nat.shiftRight (CGR p) o) 524287 = recF CG o p := by
    intro o ho
    rw [e19]
    change Nat.shiftRight (CGR p) o &&& (2 ^ 19 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
    apply Nat.eq_of_testBit_eq
    intro i
    unfold recF
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hi : i < 19
    · rw [tb o i (by omega), Nat.testBit_shiftRight]
      simp only [hi, decide_true, Bool.true_and]
      congr 1
      omega
    · simp [hi]
  have kk : ∀ o, o + 2 ≤ 64 → Nat.land (Nat.shiftRight (CGR p) o) 3 = kb CG o p := by
    intro o ho
    change Nat.shiftRight (CGR p) o &&& 3 = _
    rw [and3_eq, tb o 0 (by omega), tb o 1 (by omega)]
    unfold kb
    rfl
  exact ⟨by rw [d0, fl 0 (by decide)], by rw [d1, kk 19 (by decide)], by rw [d2, fl 32 (by decide)],
    by rw [d3, kk 51 (by decide)]⟩

theorem mTabs_P : Rep 920808 (mTabs ())[0]! (gP 0) ∧ Rep 920808 (mTabs ())[1]! (gP 1) := by
  obtain ⟨g0, g1, a0, b0, a1, b1⟩ := lk_spec (NW := NWP) (KA := KAP) (KB := KBP) lkP_all
  exact mTabs_rep_of coverGens_lines cgd_rec (lokP (by decide)) g0 a0 b0 (lokP (by decide)) g1 a1 b1

theorem mTabs_O : Rep 920808 (mTabs ())[0]! (gO 0) ∧ Rep 920808 (mTabs ())[1]! (gO 1) := by
  obtain ⟨g0, g1, a0, b0, a1, b1⟩ := lk_spec (NW := NWO) (KA := KAO) (KB := KBO) lkO_all
  exact mTabs_rep_of coverGens_lines cgd_rec (lokO (by decide)) g0 a0 b0 (lokO (by decide)) g1 a1 b1

theorem mTabs_Y : Rep 920808 (mTabs ())[0]! (gY 0) ∧ Rep 920808 (mTabs ())[1]! (gY 1) := by
  obtain ⟨g0, g1, a0, b0, a1, b1⟩ := lk_spec (NW := NWY) (KA := KAY) (KB := KBY) lkY_all
  exact mTabs_rep_of coverGens_lines cgd_rec (lokY (by decide)) g0 a0 b0 (lokY (by decide)) g1 a1 b1

end CertificateChecks.KernelRouteP

end
