module

public import Certificates.Kernel.RouteP.Cocode.Check
public import Certificates.Kernel.RouteP.Obj.Nets
public import CFSG.Certificates.Kernel.RouteP.LineSound
public import CFSG.Certificates.Kernel.RouteP.TabComplete
public import CFSG.Certificates.Kernel.Common.ForallTree
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.Certificates.Kernel.BfsPinUnpack
public import Certificates.Data.Kernel.KDense.KeysDistinct
public import Certificates.Data.Kernel.KDense.LetterOK
public import Certificates.Data.Kernel.KDense.Plan
public import Mathlib

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

#kc_forall_tree ck_all (fun g => CFSG.KD.RouteP.ck g = true) 580 CFSG.KD.RouteP.CocodeCk.c
#kc_forall_tree nk_all (fun j => CFSG.KD.RouteP.nk j = true) 58 CFSG.KD.RouteP.ObjNets.n

noncomputable abbrev gO (r : Nat) : Perm Pt := gT NWO KAO KBO r

theorem lokO {z : ℤ} (hz : z.natAbs - 1 < 58) : LOK NWO KAO KBO z :=
  CFSG.KC.Benes.andB_true (nk_all _ hz)

theorem idOK_cw {i : Nat} (hi : i < 29) {k : Nat} (hk : k < 19) : idOK NWO (cw i) k = true := by
  have hlt : 20 * i + k < 580 := by omega
  have h := ck_all (20 * i + k) hlt
  unfold ck at h
  have e1 : Nat.mod (20 * i + k) 20 = k := by change (20 * i + k) % 20 = k; omega
  have e2 : Nat.div (20 * i + k) 20 = i := by change (20 * i + k) / 20 = i; omega
  rw [e1, e2, Nat.blt_eq.mpr hk] at h
  exact h

theorem idKOK_cw {i : Nat} (hi : i < 29) : idKOK NWO KAO KBO (cw i) = true := by
  have hlt : 20 * i + 19 < 580 := by omega
  have h := ck_all (20 * i + 19) hlt
  unfold ck at h
  have e1 : Nat.mod (20 * i + 19) 20 = 19 := by change (20 * i + 19) % 20 = 19; omega
  have e2 : Nat.div (20 * i + 19) 20 = i := by change (20 * i + 19) / 20 = i; omega
  rw [e1, e2, show Nat.blt 19 19 = false from rfl] at h
  exact h

theorem cwT_letters : ∀ i < 29, ∀ l ∈ cwT i, 1 ≤ l.natAbs ∧ l.natAbs ≤ 13 := by decide +kernel

@[expose] noncomputable def cG (l : ℤ) : Perm Pt :=
  if l = 1 then gO 53 else if l = -1 then (gO 53)⁻¹ else if l = 2 then gO 57 else if l = -2 then (gO 57)⁻¹
  else if 3 ≤ l ∧ l < 14 then gO (31 + 2 * (l - 3).toNat) else 1

@[expose] noncomputable def ρc (l : ℤ) : Perm Pt :=
  if 0 ≤ l then cG l else (cG (-l))⁻¹

theorem ρc_eq_cG {l : ℤ} (hl : -2 ≤ l) : ρc l = cG l := by
  unfold ρc
  by_cases h : 0 ≤ l
  · rw [if_pos h]
  · rw [if_neg h]
    rcases (by omega : l = -1 ∨ l = -2) with rfl | rfl
    · simp [cG]
    · simp [cG]

theorem ρc_neg (l : ℤ) : ρc (-l) = (ρc l)⁻¹ := by
  unfold ρc
  by_cases h : 0 < l
  · rw [if_neg (by omega), if_pos (by omega), neg_neg]
  · by_cases h0 : l = 0
    · subst h0
      simp [cG]
    · rw [if_pos (by omega), if_neg (by omega), inv_inv]

theorem cG_act {l : ℤ} (h1 : 1 ≤ l) (h2 : l ≤ 13) (y : Pt) :
    (cG l y).val = eL NWO KAO KBO (cl l) y.val := by
  unfold cG cl
  rcases (by omega : l = 1 ∨ l = 2 ∨ 3 ≤ l) with rfl | rfl | h3
  · exact gT_apply (lokO (by decide)) y
  · exact gT_apply (lokO (by decide)) y
  · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨h3, by omega⟩]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h3]
    have e : -(2 * l + 26) = Int.negSucc (31 + 2 * (l - 3).toNat) := by
      rw [Int.negSucc_eq]
      omega
    rw [e]
    exact gT_apply (lokO (by simp; omega)) y

theorem ρc_act {l : ℤ} (hl : 1 ≤ l.natAbs ∧ l.natAbs ≤ 13) (y : Pt) :
    (ρc l y).val = eL NWO KAO KBO (cl l) y.val := by
  by_cases hp : 0 < l
  · rw [ρc_eq_cG (by omega)]
    exact cG_act (by omega) (by omega) y
  · have hn : 1 ≤ -l ∧ -l ≤ 13 := by omega
    have e : ρc l = (cG (-l))⁻¹ := by
      unfold ρc
      rw [if_neg (by omega)]
    rw [e]
    unfold cG
    rcases (by omega : -l = 1 ∨ -l = 2 ∨ 3 ≤ -l) with h | h | h3
    · rw [if_pos h]
      have e2 : cl l = Int.ofNat (53 + 1) := by
        unfold cl
        rw [if_neg (by omega), if_pos (by omega)]
        rfl
      rw [e2]
      exact gT_inv_apply (lokO (by decide)) y
    · rw [if_neg (by omega), if_neg (by omega), if_pos h]
      have e2 : cl l = Int.ofNat (57 + 1) := by
        unfold cl
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
        rfl
      rw [e2]
      exact gT_inv_apply (lokO (by decide)) y
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos ⟨h3, by omega⟩]
      have e2 : cl l = Int.ofNat (31 + 2 * (-l - 3).toNat + 1) := by
        unfold cl
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
          Int.ofNat_eq_coe]
        omega
      rw [e2]
      exact gT_inv_apply (lokO (by simp; omega)) y

theorem wordG_eq_cw {u v : List ℤ} {i : Nat} (hi : i < 29) (he : cwT i = u ++ invW v) :
    wordG ρc u = wordG ρc v := by
  have hlet := cwT_letters i hi
  rw [he] at hlet
  refine wordG_eq_of ρc cl ρc_neg (fun l hl y => ρc_act (hlet l hl) y) ?_ ?_ ?_
  · intro z hz
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hz
    have := hlet l hl
    refine lokO ?_
    unfold cl
    split_ifs <;> omega
  · intro k hk
    have := idOK_cw hi hk
    unfold cw at this
    rwa [he] at this
  · have := idKOK_cw hi
    unfold cw at this
    rwa [he] at this

theorem wordG_cG {w : List ℤ} (h : ∀ l ∈ w, -2 ≤ l) : wordG cG w = wordG ρc w := by
  unfold wordG
  congr 1
  exact List.map_congr_left fun l hl => (ρc_eq_cG (h l hl)).symm

theorem hn32 : (920808 : Nat) < 2 ^ 32 := by decide

theorem rep_cocodeLetter {tabs : Array Table} (hR : ∀ r < 58, Rep 920808 tabs[r]! (gO r)) (l : ℤ) :
    Rep 920808 (cocodeLetter tabs (invT degree tabs[aReg]!) (invT degree tabs[bReg]!) l) (cG l) := by
  unfold cocodeLetter cG
  split_ifs with h1 h2 h3 h4 h5
  · exact hR 53 (by decide)
  · exact rep_invT hn32 (hR 53 (by decide))
  · exact hR 57 (by decide)
  · exact rep_invT hn32 (hR 57 (by decide))
  · have : epsReg (l - 3).toNat = 31 + 2 * (l - 3).toNat := rfl
    rw [this]
    exact hR _ (by omega)
  · exact Rep.idT hn32

theorem epsWord_ge (m : Nat) : ∀ l ∈ epsWord m, -2 ≤ l := by
  have key : ∀ k s m, ∀ l ∈ epsLetters k s m, -2 ≤ l := by
    intro k
    induction k with
    | zero => intro s m l hl; simp [epsLetters] at hl
    | succ k ih =>
      intro s m l hl
      unfold epsLetters at hl
      rcases List.mem_append.1 hl with hl | hl
      · split_ifs at hl <;> simp at hl
        omega
      · exact ih _ _ l hl
  exact key 11 0 m

theorem relLetters_ge : ∀ i < 7, ∀ l ∈ (relLetters ())[i]!, -2 ≤ l := by decide +kernel

theorem eqTab_words {tabs : Array Table} (hR : ∀ r < 58, Rep 920808 tabs[r]! (gO r)) {u v : List ℤ}
    (hu : ∀ l ∈ u, -2 ≤ l) (hv : ∀ l ∈ v, -2 ≤ l) (huv : wordG ρc u = wordG ρc v) :
    eqTab degree (wordT degree (cocodeLetter tabs (invT degree tabs[aReg]!) (invT degree tabs[bReg]!)) u)
      (wordT degree (cocodeLetter tabs (invT degree tabs[aReg]!) (invT degree tabs[bReg]!)) v) = true := by
  have h1 := Rep.wordT hn32 u fun l _ => rep_cocodeLetter hR l
  have h2 := Rep.wordT hn32 v fun l _ => rep_cocodeLetter hR l
  rw [wordG_cG hu] at h1
  rw [wordG_cG hv, ← huv] at h2
  exact eqTab_of_rep h1 h2

theorem cocodeOKAt_of {tabs : Array Table} (hR : ∀ r < 58, Rep 920808 tabs[r]! (gO r)) :
    cocodeOKAt tabs = true := by
  unfold cocodeOKAt
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨invOK_invT_of_rep hn32 (hR 53 (by decide)), invOK_invT_of_rep hn32 (hR 57 (by decide))⟩,
    ?_⟩, ?_⟩, ?_⟩
  · unfold conjOK
    rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    refine eqTab_words hR (by intro l hl; simp at hl; omega) (epsWord_ge _) (wordG_eq_cw (i := j) (by omega) ?_)
    unfold cwT
    rw [if_pos hj']
  · unfold conjOK
    rw [List.all_eq_true]
    intro j hj
    have hj' := List.mem_range.1 hj
    refine eqTab_words hR (by intro l hl; simp at hl; omega) (epsWord_ge _)
      (wordG_eq_cw (i := 11 + j) (by omega) ?_)
    unfold cwT
    rw [if_neg (by omega), if_pos (by omega), show 11 + j - 11 = j by omega]
  · unfold relOK
    rw [List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    refine eqTab_words hR (relLetters_ge i hi') (epsWord_ge _) (wordG_eq_cw (i := 22 + i) (by omega) ?_)
    unfold cwT
    rw [if_neg (by omega), if_neg (by omega), show 22 + i - 22 = i by omega]

end CertificateChecks.KernelRouteP

end
