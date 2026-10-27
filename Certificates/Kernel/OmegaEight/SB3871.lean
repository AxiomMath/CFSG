module

public import Certificates.Data.Kernel.O8.SB
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSAutData
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchLike
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.GroupTheory.Sylow
public import Std.Data.HashMap

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.SB3871

open CFSG.KC.Enum CFSG.KC.SB CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] noncomputable def mulK (c d : Nat) : Nat := sMulG sActRow sMtRow c d

@[expose] noncomputable def invK (c : Nat) : Nat := sInvG sActRow sGinvLit c

@[expose] noncomputable def linK (v : Nat) : Nat := linG a9LinLit v

@[expose] noncomputable def coK (c : Nat) : Nat := coG a9CoRow c

@[expose] noncomputable def nfEK (x : Nat) : Nat := nfEG sNfRow x

@[expose] noncomputable def nfAK (x : Nat) : Nat := nfAG sNfRow x

@[expose] noncomputable def mK (k : Nat) : Nat :=
  nIf(Nat.blt k (nat_lit 65536),
    fld(sMRow (Nat.shiftRight k (nat_lit 9)), Nat.mul (nat_lit 9) (Nat.land k (nat_lit 511)),
      nat_lit 511), nat_lit 0)

@[expose] noncomputable def treeK (o m c : Nat) : Nat :=
  nIf(Nat.blt c (nat_lit 65536),
    fld(sTreeRow (Nat.shiftRight c (nat_lit 7)),
      Nat.add (Nat.mul (nat_lit 28) (Nat.land c (nat_lit 127))) o, m), nat_lit 0)

@[expose] noncomputable def korbK (v : Nat) : List (ℕ × ℕ) :=
  if v < 512 then (List.range (sKOrbRow v % 2 ^ 8)).map fun k =>
    (sKOrbRow v / 2 ^ (32 * k + 8) % 2 ^ 16, sKOrbRow v / 2 ^ (32 * k + 24) % 2 ^ 16) else []

@[expose] noncomputable def canonK (o ki d : Nat) : Nat :=
  if ki < 56 ∧ d < 512 then
    sCanonRow ((512 * ki + d) / 128) / 2 ^ (18 * ((512 * ki + d) % 128) + o) % 2 ^ 9 else 0

theorem fld_eq (r o w : Nat) : Nat.land (Nat.shiftRight r o) (2 ^ w - 1) = r / 2 ^ o % 2 ^ w := by
  change (r >>> o) &&& (2 ^ w - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem land_eq (x w : Nat) : Nat.land x (2 ^ w - 1) = x % 2 ^ w := by
  change x &&& (2 ^ w - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod]

theorem shr_eq (x k : Nat) : Nat.shiftRight x k = x / 2 ^ k := Nat.shiftRight_eq_div_pow x k

theorem l15 (x : Nat) : Nat.land x 15 = x % 16 := land_eq x 4
theorem l127 (x : Nat) : Nat.land x 127 = x % 128 := land_eq x 7
theorem l255 (x : Nat) : Nat.land x 255 = x % 256 := land_eq x 8
theorem l511 (x : Nat) : Nat.land x 511 = x % 512 := land_eq x 9
theorem l65535 (x : Nat) : Nat.land x 65535 = x % 65536 := land_eq x 16
theorem strictN_eq' (y : ℕ) (k : ℕ → ℕ) : strictN y k = k y := by cases y <;> rfl

theorem nIf_blt {a b : Nat} (t e : Nat) :
    Bool.rec (motive := fun _ => Nat) e t (Nat.blt a b) = if a < b then t else e := by
  by_cases h : a < b
  · rw [ite_eq_left h, show Nat.blt a b = true from Nat.blt_eq.mpr h]
  · rw [ite_eq_right h, show Nat.blt a b = false from Bool.eq_false_iff.2 fun e => h (Nat.blt_eq.mp e)]

theorem sMul_eqK : sMul = mulK := by
  funext c d
  have hg : c / 128 % 512 < 512 := Nat.mod_lt _ (by norm_num)
  have he : d % 128 < 128 := Nat.mod_lt _ (by norm_num)
  have hh : d / 128 % 512 < 512 := Nat.mod_lt _ (by norm_num)
  have k1 : (c / 128 % 512) * 128 + d % 128 < 65536 := by omega
  have k2 : (c / 128 % 512) * 512 + d / 128 % 512 < 262144 := by omega
  rw [sMul, mulK, sMulG, strictN_eq', strictN_eq', strictN_eq',
    getElem!_pos sAct _ (by simpa [sAct] using k1), getElem!_pos sMt _ (by simpa [sMt] using k2)]
  simp only [sAct, sMt, Array.getElem_ofFn, l127, l511, shr_eq, Nat.mul_eq, Nat.add_eq]
  have e1 : ((c / 128 % 512) * 128 + d % 128) / 128 = c / 128 % 512 := by omega
  have e2 : ((c / 128 % 512) * 128 + d % 128) % 128 = d % 128 := by omega
  have e3 : ((c / 128 % 512) * 512 + d / 128 % 512) / 512 = c / 128 % 512 := by omega
  have e4 : ((c / 128 % 512) * 512 + d / 128 % 512) % 512 = d / 128 % 512 := by omega
  rw [e1, e2, e3, e4]
  rfl

theorem sInv_eqK : sInv = invK := by
  funext c
  have hg : c / 128 % 512 < 512 := Nat.mod_lt _ (by norm_num)
  have hgi : sGinvLit / 2 ^ (9 * (c / 128 % 512)) % 2 ^ 9 < 512 := Nat.mod_lt _ (by norm_num)
  have k1 : (sGinvLit / 2 ^ (9 * (c / 128 % 512)) % 2 ^ 9) * 128 + c % 128 < 65536 := by omega
  rw [sInv, invK, sInvG, getElem!_pos sGinv _ (by simpa [sGinv] using hg)]
  simp only [sGinv, Array.getElem_ofFn]
  rw [strictN_eq', getElem!_pos sAct _ (by simpa [sAct] using k1)]
  simp only [sAct, Array.getElem_ofFn, l127, l511, shr_eq, Nat.mul_eq, Nat.add_eq]
  have e1 : ((sGinvLit / 2 ^ (9 * (c / 128 % 512)) % 2 ^ 9) * 128 + c % 128) / 128 =
      sGinvLit / 2 ^ (9 * (c / 128 % 512)) % 2 ^ 9 := by omega
  have e2 : ((sGinvLit / 2 ^ (9 * (c / 128 % 512)) % 2 ^ 9) * 128 + c % 128) % 128 = c % 128 := by
    omega
  rw [e1, e2]
  rfl

theorem a9LinTab_get (v : ℕ) : a9LinTab[v]! = linK v := by
  rw [linK, linG, nIf_blt]
  by_cases hv : v < 512
  · rw [ite_eq_left hv, getElem!_pos a9LinTab _ (by simpa [a9LinTab] using hv)]
    simp only [a9LinTab, Array.getElem_ofFn, l65535, shr_eq, Nat.mul_eq]
    rfl
  · rw [ite_eq_right hv, getElem!_neg a9LinTab _ (by simpa [a9LinTab] using hv)]
    rfl

theorem a9CoTab_get (c : ℕ) : a9CoTab[c]! = coK c := by
  rw [coK, coG, nIf_blt]
  by_cases hc : c < 65536
  · rw [ite_eq_left hc, getElem!_pos a9CoTab _ (by simpa [a9CoTab] using hc)]
    simp only [a9CoTab, Array.getElem_ofFn, l127, l511, shr_eq, Nat.mul_eq]
    rfl
  · rw [ite_eq_right hc, getElem!_neg a9CoTab _ (by simpa [a9CoTab] using hc)]
    rfl

theorem sNfTab_get (x : ℕ) : sNfTab[x]! = (nfEK x, nfAK x) := by
  rw [nfEK, nfAK, nfEG, nfAG, nIf_blt, nIf_blt]
  by_cases hx : x < 65536
  · rw [ite_eq_left hx, ite_eq_left hx, getElem!_pos sNfTab _ (by simpa [sNfTab] using hx)]
    simp only [sNfTab, Array.getElem_ofFn, l127, l511, shr_eq, Nat.mul_eq, Nat.add_eq]
    rfl
  · rw [ite_eq_right hx, ite_eq_right hx, getElem!_neg sNfTab _ (by simpa [sNfTab] using hx)]
    rfl

theorem sMTab_get (k : ℕ) : sMTab[k]! = mK k := by
  rw [mK, nIf_blt]
  by_cases hk : k < 65536
  · rw [ite_eq_left hk, getElem!_pos sMTab _ (by simpa [sMTab] using hk)]
    simp only [sMTab, Array.getElem_ofFn, l511, shr_eq, Nat.mul_eq]
    rfl
  · rw [ite_eq_right hk, getElem!_neg sMTab _ (by simpa [sMTab] using hk)]
    rfl

theorem sTree_par (c : ℕ) : sTree.1[c]! = treeK 0 65535 c := by
  rw [treeK, nIf_blt]
  by_cases hc : c < 65536
  · rw [ite_eq_left hc, getElem!_pos sTree.1 _ (by simpa [sTree] using hc)]
    simp only [sTree, Array.getElem_ofFn, l127, l65535, shr_eq, Nat.mul_eq, Nat.add_eq]
    rfl
  · rw [ite_eq_right hc, getElem!_neg sTree.1 _ (by simpa [sTree] using hc)]
    rfl

theorem sTree_pj (c : ℕ) : sTree.2.1[c]! = treeK 16 15 c := by
  rw [treeK, nIf_blt]
  by_cases hc : c < 65536
  · rw [ite_eq_left hc, getElem!_pos sTree.2.1 _ (by simpa [sTree] using hc)]
    simp only [sTree, Array.getElem_ofFn, l127, l15, shr_eq, Nat.mul_eq, Nat.add_eq]
    rfl
  · rw [ite_eq_right hc, getElem!_neg sTree.2.1 _ (by simpa [sTree] using hc)]
    rfl

theorem sTree_dep (c : ℕ) : sTree.2.2[c]! = treeK 20 255 c := by
  rw [treeK, nIf_blt]
  by_cases hc : c < 65536
  · rw [ite_eq_left hc, getElem!_pos sTree.2.2 _ (by simpa [sTree] using hc)]
    simp only [sTree, Array.getElem_ofFn, l127, l255, shr_eq, Nat.mul_eq, Nat.add_eq]
    rfl
  · rw [ite_eq_right hc, getElem!_neg sTree.2.2 _ (by simpa [sTree] using hc)]
    rfl

theorem sKOrb_get (v : ℕ) : sKOrb[v]! = korbK v := by
  rw [korbK]
  by_cases hv : v < 512
  · rw [ite_eq_left hv, getElem!_pos sKOrb _ (by simpa [sKOrb] using hv)]
    simp only [sKOrb, Array.getElem_ofFn]
  · rw [ite_eq_right hv, getElem!_neg sKOrb _ (by simpa [sKOrb] using hv)]
    rfl

theorem sCanon_get (ki d : ℕ) : (sCanon[ki]!)[d]! = (canonK 0 ki d, canonK 9 ki d) := by
  rw [canonK, canonK]
  by_cases h : ki < 56 ∧ d < 512
  · rw [ite_eq_left h, ite_eq_left h, getElem!_pos sCanon _ (by simpa [sCanon] using h.1)]
    simp only [sCanon, Array.getElem_ofFn]
    rw [getElem!_pos _ _ (by simpa using h.2), Array.getElem_ofFn]
    simp
  · rw [ite_eq_right h, ite_eq_right h]
    by_cases hk : ki < 56
    · have hd : ¬ d < 512 := fun hd => h ⟨hk, hd⟩
      rw [getElem!_pos sCanon _ (by simpa [sCanon] using hk)]
      simp only [sCanon, Array.getElem_ofFn]
      rw [getElem!_neg _ _ (by simpa using hd)]
      rfl
    · rw [getElem!_neg sCanon _ (by simpa [sCanon] using hk)]
      rfl

end CertificateChecks.KernelO8.SB3871

end
