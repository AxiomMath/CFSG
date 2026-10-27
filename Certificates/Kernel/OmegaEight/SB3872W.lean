module

public import Certificates.Kernel.OmegaEight.SB3872

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3872

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch CertificateChecks.KernelO8.SB3871

@[expose] def upC (c : ℕ) : ℕ := fld(c, 7, 511)

@[expose] noncomputable def upMul (a b : ℕ) : ℕ := fld(sMtRow a, Nat.mul 9 b, 511)

@[expose] noncomputable def preU (FF : List ℕ) (u : ℕ) : Bool :=
  (List.range sGens.length).all fun j =>
    upMul u (upC (sGens.getD j 0)) == upMul (upC (FF.getD j 0)) u

@[expose] noncomputable def zListU (F : ℕ → ℕ) (FF : List ℕ) : List ℕ :=
  (List.range 512).flatMap fun u => if preU FF u then
    ((List.range 128).map (· + 128 * u)).filter fun z =>
      ((List.range sGens.length).all fun j => mulK z (sGens.getD j 0) == mulK (FF.getD j 0) z) &&
        F z == z
  else []

theorem upC_add {e u : ℕ} (he : e < 128) (hu : u < 512) : upC (e + 128 * u) = u := by
  rw [upC, l511, shr_eq]
  norm_num
  omega

theorem upC_mulK (c d : ℕ) : upC (mulK c d) = upMul (upC c) (upC d) := by
  unfold mulK sMulG
  rw [strictN_eq', strictN_eq', strictN_eq']
  have h1 : Nat.land c 127 < 2 ^ 7 := by rw [l127]; exact Nat.mod_lt _ (by norm_num)
  have h2 : Nat.land (Nat.shiftRight (sActRow (Nat.land (Nat.shiftRight c 7) 511))
      (Nat.mul 7 (Nat.land d 127))) 127 < 2 ^ 7 := by rw [l127]; exact Nat.mod_lt _ (by norm_num)
  have h3 : Nat.land (Nat.shiftRight (sMtRow (Nat.land (Nat.shiftRight c 7) 511))
      (Nat.mul 9 (Nat.land (Nat.shiftRight d 7) 511))) 511 < 512 := by
    rw [l511]; exact Nat.mod_lt _ (by norm_num)
  exact upC_add (Nat.xor_lt_two_pow h1 h2) h3

theorem range_blocks (n : ℕ) :
    List.range (128 * n) = (List.range n).flatMap fun u => (List.range 128).map (· + 128 * u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, List.range_add, ih, List.range_succ (n := n), List.flatMap_append,
      List.flatMap_singleton]
    congr 1
    exact List.map_congr_left fun x _ => Nat.add_comm _ _

theorem zListW_eq (F : ℕ → ℕ) (FF : List ℕ) : zListW F FF = zListU F FF := by
  rw [zListW, zListU, sMul_eqK, (by norm_num : 65536 = 128 * 512), range_blocks, List.filter_flatMap]
  refine List.flatMap_congr fun u hu => ?_
  rw [List.mem_range] at hu
  split
  · rfl
  · next hp =>
    refine List.filter_eq_nil_iff.2 fun z hz hpz => hp ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hz
    rw [List.mem_range] at he
    rw [Bool.and_eq_true, List.all_eq_true] at hpz
    rw [preU, List.all_eq_true]
    intro j hj
    have hz := congrArg upC (beq_iff_eq.1 (hpz.1 j hj))
    rw [upC_mulK, upC_mulK, upC_add he hu] at hz
    exact beq_iff_eq.2 hz

end CertificateChecks.KernelO8.SB3872

end
