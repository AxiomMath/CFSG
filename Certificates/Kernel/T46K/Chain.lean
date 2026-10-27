
module

public import Certificates.Kernel.T46K.ChainChecks
public import Certificates.Kernel.T46K.Letters
public import CFSG.Certificates.Kernel.Spor.PChainSound
public import CFSG.Fischer.T46UnitaryBase
public import CFSG.Fischer.UnitaryAction
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases
public import CFSG.Sporadic.Fi22.LocalCertBase

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelT46.t0All CertificateChecks.KernelT46.t0Sl 11
#kon_join CertificateChecks.KernelT46.t1All CertificateChecks.KernelT46.t1Sl 8

namespace CertificateChecks.KernelT46

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.TBfs CFSG.KS.PC CFSG.KS.TW CFSG.KS.T46K
  CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Fischer
  CFSG.F4.Native

theorem sl_spec {n cnt r lo len : Nat} {L : Nat → Nat → Nat} {LV : Nat → Nat}
    {PTS POS PAR LAB TI : Nat → Nat} (h : tbfsSlK n cnt r L LV PTS POS PAR LAB TI lo len = true) :
    ∀ k, lo ≤ k → k < lo + len → k < cnt → tbfsPtK n cnt r L LV PTS POS PAR LAB TI k = true := by
  intro k h1 h2 h3
  have h' := Raw.Orb.allN_iff.1 h (k - lo) (by omega)
  rw [Raw.Orb.strictB_eq] at h'
  have e : Nat.add lo (k - lo) = k := by
    change lo + (k - lo) = k
    omega
  rw [e, Eq.mpr Nat.blt_eq h3] at h'
  exact h'

theorem cnts : CNTT 0 = 693 ∧ CNTT 1 = 512 ∧ CNTT 2 = 120 ∧ CNTT 3 = 36 ∧ CNTT 4 = 6 := by
  have h := sizes_ok
  unfold sizesK at h
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.beq_eq] at h
  exact h

theorem pt_of {i c : Nat} (h : ptSl i c = true) : ∀ k, 64 * c ≤ k → k < 64 * c + 64 → k < CNTT i →
    tbfsPtK 693 (CNTT i) (lvK LK BT 106 i).length LK (lvAt LK BT 106 i) (PTST i) (POST i) (PART i)
      (LABT i) (TIT i) k = true := by
  intro k h1 h2 h3
  unfold ptSl at h
  exact sl_spec h k (by change c * 64 ≤ k; omega) (by change k < c * 64 + 64; omega) h3

theorem tree_spec {i : Nat} (hi : i < 5) :
    tbfsHdK 693 (BT i) (CNTT i) (PTST i) (POST i) (PART i) (LABT i) = true ∧
      ∀ k < CNTT i, tbfsPtK 693 (CNTT i) (lvK LK BT 106 i).length LK (lvAt LK BT 106 i) (PTST i)
        (POST i) (PART i) (LABT i) (TIT i) k = true := by
  refine ⟨Raw.Orb.allN_iff.1 hd_ok i hi, fun k hk => ?_⟩
  obtain ⟨c0, c1, c2, c3, c4⟩ := cnts
  have h234 := t234_ok
  unfold t234K at h234
  simp only [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h234
  obtain ⟨a0, a1, a2, a3⟩ := h234
  interval_cases i
  · rw [c0] at hk
    have hs : k / 64 < 11 := by omega
    exact pt_of (t0All (k / 64) hs) k (by omega) (by omega) (by rw [c0]; exact hk)
  · rw [c1] at hk
    have hs : k / 64 < 8 := by omega
    exact pt_of (t1All (k / 64) hs) k (by omega) (by omega) (by rw [c1]; exact hk)
  · rw [c2] at hk
    rcases (by omega : k < 64 ∨ 64 ≤ k) with hk' | hk'
    · exact pt_of a0 k (by omega) (by omega) (by rw [c2]; exact hk)
    · exact pt_of a1 k (by omega) (by omega) (by rw [c2]; exact hk)
  · rw [c3] at hk
    exact pt_of a2 k (by omega) (by omega) (by rw [c3]; exact hk)
  · rw [c4] at hk
    exact pt_of a3 k (by omega) (by omega) (by rw [c4]; exact hk)

theorem rangeK_eq : ∀ (n : Nat) (acc : List Nat),
    Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun k ih acc => ih (List.cons k acc)) n acc = List.range n ++ acc
  | 0, acc => rfl
  | n + 1, acc => by
    change Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun k ih acc => ih (List.cons k acc)) n (n :: acc) = _
    rw [rangeK_eq n, List.range_succ, List.append_assoc]
    rfl

theorem QT_eq : QT = List.range 693 := by
  unfold QT rangeK
  exact (rangeK_eq 693 []).trans (List.append_nil _)

theorem chain_hyp : ChainHyp 693 106 5 (t46Letters ()) t46Base (t46Q ()) t46Base LK BT QT BT CNTT
    PTST POST PART LABT TIT where
  letters := ⟨letters.1, fun l hl x hx => ((letters.2 l hl).2 x hx).1⟩
  inv := ⟨rfl, inv_ok⟩
  base := ⟨rfl, fun i hi => by interval_cases i <;> exact ⟨rfl, by decide⟩⟩
  chk := by
    refine ⟨by rw [QT_eq]; simp [t46Q], fun t ht => ?_, rfl, fun i hi => ?_⟩
    · rw [QT_eq] at ht ⊢
      rw [List.getD_eq_getElem _ _ ht, List.getElem_range]
      simpa using ht
    · rw [QT_eq]
      interval_cases i <;> exact ⟨rfl, by decide, by decide⟩
  tree := fun i hi => tree_spec hi

theorem prod_cnt : ((List.range 5).map CNTT).prod = 9196830720 := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := cnts
  change CNTT 0 * (CNTT 1 * (CNTT 2 * (CNTT 3 * (CNTT 4 * 1)))) = _
  rw [c0, c1, c2, c3, c4]

theorem perm_of_TR {t : Table} {σ : Equiv.Perm (Fin 693)} (ht : TR 693 t (actN σ)) :
    permOfT 693 t = σ := by
  ext x
  have hr : ∀ y < 693, ap t y < 693 := fun y hy => by rw [(ht.2 y hy).1]; exact (ht.2 y hy).2
  have hinj : ∀ a < 693, ∀ b < 693, ap t a = ap t b → a = b := fun a ha b hb e => by
    rw [(ht.2 a ha).1, (ht.2 b hb).1, actN_of_lt _ ha, actN_of_lt _ hb] at e
    exact congrArg Fin.val (σ.injective (Fin.ext e))
  rw [permOfT_val hr hinj, (ht.2 x x.isLt).1, actN_of_lt _ x.isLt]

theorem t46gs_mem (j : Nat) : t46gs j ∈ piSU.range := by
  unfold t46gs wordG
  exact Subgroup.list_prod_mem _ fun x hx => by
    obtain ⟨z, -, rfl⟩ := List.mem_map.1 hx
    exact t46G_mem_range z

theorem letter_mem {l : Nat} (hl : l < 106) : permOfT 693 (t46Letters ())[l]! ∈ piSU.range := by
  have hj : l / 2 < (t46Letters ()).size / 2 := by rw [letters.1]; omega
  have hR := rep_t46Letters (l / 2) hj
  have hE : TR 693 (t46Letters ())[2 * (l / 2)]! (actN (t46gs (l / 2))) :=
    ⟨(letters.2 _ (by omega)).1, fun x hx => ⟨by rw [hR x hx, idx_of_lt _ hx, actN_of_lt _ hx]; rfl,
      actN_lt _ hx⟩⟩
  rcases Nat.mod_two_eq_zero_or_one l with h2 | h2
  · have e : 2 * (l / 2) = l := by omega
    rw [e] at hE
    rw [perm_of_TR hE]
    exact t46gs_mem _
  · have e : 2 * (l / 2) + 1 = l := by omega
    have hk : l / 2 < 106 / 2 := by omega
    have hO := letters.2 l hl
    have hI : TR 693 (t46Letters ())[l]! (actN (t46gs (l / 2))⁻¹) := by
      refine ⟨hO.1, fun x hx => ⟨?_, actN_lt _ hx⟩⟩
      rw [(hO.2 x hx).1]
      have hy := (hO.2 x hx).2
      have hfg := pair_inv (fun x hx => (invK_spec inv_ok hk hx).1)
        (fun x hx => (invK_spec inv_ok hk hx).2.2) x hx
      rw [e] at hfg
      have h1 : actN (t46gs (l / 2)) (LK l x) = x := by
        rw [← (hE.2 _ hy).1, ((letters.2 _ (by omega)).2 _ hy).1, hfg]
      calc LK l x = actN (t46gs (l / 2))⁻¹ (actN (t46gs (l / 2)) (LK l x)) := by
            rw [← actN_mul, inv_mul_cancel, actN_one]
        _ = actN (t46gs (l / 2))⁻¹ x := by rw [h1]
    rw [perm_of_TR hI]
    exact Subgroup.inv_mem _ (t46gs_mem _)

theorem letters_card :
    Nat.card (Subgroup.closure (Set.range fun l : Fin 106 => permOfT 693 (t46Letters ())[l.val]!)) ≤
      ((List.range 5).map CNTT).prod := by
  rw [prod_cnt]
  have hle : Subgroup.closure (Set.range fun l : Fin 106 => permOfT 693 (t46Letters ())[l.val]!) ≤
      piSU.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨l, rfl⟩
    exact letter_mem l.isLt
  exact (Subgroup.card_le_of_le hle).trans card_range_le

theorem chain_eq : chainTrees 693 (t46Letters ()) t46Base =
      Array.ofFn (n := 5) (fun i => tbfsRec 693 (CNTT i.val) (PTST i.val) (POST i.val)
        (PART i.val) (LABT i.val)) ∧
    ∀ chunks, chainOK 693 (t46Letters ()) t46Base (t46Q ()) t46Base
      (chainTrees 693 (t46Letters ()) t46Base) chunks = true :=
  pchain_of_card chain_hyp letters_card

theorem sizes : orbitSizes (t46Trees ()) = [693, 512, 120, 36, 6] := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := cnts
  change orbitSizes (chainTrees 693 (t46Letters ()) t46Base) = _
  rw [chain_eq.1]
  simp only [orbitSizes, tbfsRec, Array.toList_ofFn, List.ofFn_succ, List.ofFn_zero, List.map_cons,
    List.map_nil, Array.size_ofFn]
  change [CNTT 0, CNTT 1, CNTT 2, CNTT 3, CNTT 4] = _
  rw [c0, c1, c2, c3, c4]

theorem t46_chain : (uPtsOK && chainOK 693 (t46Letters ()) t46Base (t46Q ()) t46Base (t46Trees ()) 3 &&
    orbitSizes (t46Trees ()) == [693, 512, 120, 36, 6]) = true := by
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨CFSG.KD.Misc.Unitary.uPtsOK_true, chain_eq.2 3⟩, sizes⟩

end CertificateChecks.KernelT46

end
