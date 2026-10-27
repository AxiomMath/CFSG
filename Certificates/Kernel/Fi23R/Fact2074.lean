
module

public import Certificates.Kernel.Fi23R.Fact2075
public import Certificates.Kernel.Fi23R.Fact10031
public import CFSG.Sporadic.FischerOddCore.Fi23UniqCheckInputs
import Certificates.Kernel.Fi23R.Uniq
import Certificates.Kernel.Fi23R.Trip
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23R

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R CFSG.KD.Fi23K CFSG.KD.Fi23R CFSG.KS.Raw.Orb
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Fi23.Native CertificateChecks.KernelFi23M
  CFSG.Sporadic.FischerOddCore

@[expose] noncomputable def nfix (p : Pt) : ℕ := (Finset.univ.filter fun i : Fin 31671 => p i = i).card

theorem nfix_conj (p q : Pt) : nfix (q * p * q⁻¹) = nfix p := by
  unfold nfix
  refine Finset.card_bij (fun i _ => q⁻¹ i) (fun i hi => ?_)
    (fun a _ b _ h => q⁻¹.injective h)
    (fun j hj => ⟨q j, ?_, Equiv.Perm.inv_eq_iff_eq.2 rfl⟩)
  · rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    have h := hi.2
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at h
    exact Equiv.Perm.eq_inv_iff_eq.2 h
  · rw [Finset.mem_filter] at hj ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq.2 rfl, hj.2]

theorem countP_nfix (w : List ℕ) (hw : ∀ c ∈ w, okL c) :
    (List.range 31671).countP (fxW G w) = nfix (wp w) := by
  have ha := wp_acts w hw
  have e : (List.range 31671).countP (fxW G w) = Nat.count (fun m => fxW G w m = true) 31671 := by
    unfold Nat.count
    exact List.countP_congr fun i _ => by simp
  rw [e, Nat.count_eq_card_filter_range]
  unfold nfix
  symm
  refine Finset.card_bij (fun i _ => i.val) (fun i hi => ?_) (fun a _ b _ h => Fin.ext h)
    (fun b hb => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨i.isLt, ?_⟩
    rw [fxW_iff, ← ha i.val i.isLt]
    exact congrArg Fin.val hi
  · simp only [Finset.mem_filter, Finset.mem_range] at hb
    refine ⟨⟨b, hb.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply Fin.ext
    rw [ha b hb.1]
    exact (fxW_iff w b).1 hb.2

theorem getD_mem (gens : List ℕ) (i : ℕ) : gens.getD i 0 ∈ 0 :: gens := by
  by_cases hi : i < gens.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.mem_cons_of_mem _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact List.mem_cons_self

theorem cmB_comm {wY : List ℕ} (hY : ∀ c ∈ wY, okL c) {g : ℕ} (hg : g < 31671)
    (h : cmB wY g = true) : wp wY * cT g = cT g * wp wY := by
  have hok : ∀ c ∈ [128 + g], okL c := fun c hc => by
    rw [List.mem_singleton] at hc
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
  unfold cmB at h
  have e := wp_eq_of_eqB h (ok_append hok hY) (ok_append hY hok)
  rw [show (128 + g) :: wY = [128 + g] ++ wY from rfl, wp_append, wp_append, wp_cons, wp_nil,
    one_mul, lp_big (by omega), Nat.add_sub_cancel_left] at e
  exact e

theorem fix_step {wY : List ℕ} {g : ℕ} (hg : g < 31671) (hc : wp wY * cT g = cT g * wp wY)
    {y : ℕ} (hy : y < 31671) :
    tA G g y < 31671 ∧ nfix (cT (tA G g y) * wp wY) = nfix (cT y * wp wY) := by
  refine ⟨tA_lt g hy, ?_⟩
  have e1 : tA G g y = (cT g ⟨y, hy⟩).val := (cT_acts hg y hy).symm
  have e2 : cT (tA G g y) = cT g * cT y * (cT g)⁻¹ := by
    rw [e1]
    exact (cT_conj (tk g * wD * (tk g)⁻¹) hy).symm
  have hci : (cT g)⁻¹ * wp wY = wp wY * (cT g)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hc, mul_assoc, mul_inv_cancel, mul_one]
  have e3 : cT g * cT y * (cT g)⁻¹ * wp wY = cT g * (cT y * wp wY) * (cT g)⁻¹ := by
    simp only [mul_assoc, hci]
  rw [e2, e3, nfix_conj]

theorem orbit_count {wY : List ℕ} (hY : ∀ c ∈ wY, okL c) {gens : List ℕ}
    (hg : ∀ g ∈ 0 :: gens, g < 31671) (hc : (0 :: gens).all (cmB wY) = true) {r c : ℕ}
    (hr : r < 31671) :
    wapp G gens 7 c r < 31671 ∧ nfix (cT (wapp G gens 7 c r) * wp wY) = nfix (cT r * wp wY) := by
  refine wapp_ind (fun y => y < 31671 ∧ nfix (cT y * wp wY) = nfix (cT r * wp wY)) gens ?_ 7 c r
    ⟨hr, rfl⟩
  intro i y ⟨hy, hfy⟩
  have hmem := getD_mem gens i
  have hgl := hg _ hmem
  have hcm := cmB_comm hY hgl (List.all_eq_true.1 hc _ hmem)
  obtain ⟨h1, h2⟩ := fix_step hgl hcm hy
  exact ⟨h1, h2.trans hfy⟩

theorem gU_lt : ∀ g ∈ 0 :: gU, g < 31671 := by decide
theorem gT_lt : ∀ g ∈ 0 :: gT, g < 31671 := by decide

theorem nfix_tab {X : Table} {wY : List ℕ} (hX : RW X wY) {k : ℕ} (hk : k < 31671) :
    fi23UniqFix (compT 31671 (treeActTab orbLit (dTab orbLit) (genTables orbLit (-2)) k) X) =
      nfix (cT k * wp wY) := by
  have hT := rw_compT (rw_treeActTab hk) hX
  unfold fi23UniqFix
  rw [hT.countP, countP_nfix _ hT.2.1, wp_append, wp_cons, wp_nil, one_mul, lp_big (by omega),
    Nat.add_sub_cancel_left]

theorem uniq_ok : fi23UniqOK orbLit = true := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := base_facts
  have hX := rw_X
  have c39 : (List.range 31671).countP (fxW G (wX ++ [167])) = 183 := by
    have ha := uniq0_ok
    have hb := uniq1_ok
    unfold uniq0 uCnt at ha
    unfold uniq1 uCnt at hb
    replace ha := Nat.eq_of_beq_eq_true ha
    replace hb := Nat.eq_of_beq_eq_true hb
    have s := cntS_add (fxW G (wX ++ [167])) 0 23684 7987
    simp only [Nat.zero_add, Nat.reduceAdd] at s
    rw [← cntS_zero]
    omega
  have hr : nfix (cT 39 * wp wX) = 183 := by
    have e : wp (wX ++ [167]) = cT 39 * wp wX := by
      rw [wp_append, wp_cons, wp_nil, one_mul, lp_big (by norm_num)] <;> rfl
    rw [← e, ← countP_nfix _ (ok_append ok_wX (by decide)), c39]
  have hs : orbSl G wX exU (wr 0) gU 39 39 0 31671 = true := uscan_ok
  unfold fi23UniqOK
  dsimp only
  rw [allIn_eq_true]
  intro k _ hk
  by_cases h0 : k = 0
  · subst h0
    simp
  by_cases h1 : k = 1
  · subst h1
    simp
  by_cases hf : wa G wX k = k
  · obtain ⟨c, r, hr', hwk⟩ := orbSl_spec hs k hk (by rw [Nat.zero_add]; exact exU_false h0 h1)
      (by rw [Nat.zero_add]; exact hf)
    rw [Nat.zero_add] at hwk
    have hr39 : r = 39 := hr'.elim id id
    subst hr39
    obtain ⟨-, hn⟩ := orbit_count ok_wX gU_lt h8 (c := c) (r := 39) (by norm_num)
    rw [hwk] at hn
    rw [nfix_tab hX hk, hn, hr]
    simp
  · rw [hX.ap hk]
    simp [hf]

theorem trip_ok : fi23TripOK orbLit = true := by
  obtain ⟨-, -, -, -, -, -, -, -, h9⟩ := base_facts
  have hX := rw_XC
  have hr : nfix (cT 53 * wp wXC) = 183 := by
    have hc := cmB_comm ok_wXC (g := 53) (by norm_num) (List.all_eq_true.1 h9 53 (by decide))
    have e : wp w53 = cT 53 * wp wXC := by
      rw [show w53 = 181 :: wXC from rfl, wp_cons, lp_big (by norm_num)]
      exact hc
    rw [← e, ← countP_nfix _ (by decide), hunt_count]
  have hs0 : orbSl G wXC exT (wr 1) gT 53 53 0 21940 = true := tscan0_ok
  have hs1 : orbSl G wXC exT (wr 1) gT 53 53 21940 9731 = true := tscan1_ok
  unfold fi23TripOK
  dsimp only
  rw [allIn_eq_true]
  intro k _ hk
  by_cases h0 : k = 0
  · subst h0
    simp
  by_cases h1 : k = 1
  · subst h1
    simp
  by_cases h39 : k = 39
  · subst h39
    simp
  by_cases hf : wa G wXC k = k
  · have hw : ∃ c, wapp G gT 7 c 53 = k := by
      by_cases hlo : k < 21940
      · obtain ⟨c, r, hr', hwk⟩ := orbSl_spec hs0 k hlo
          (by rw [Nat.zero_add]; exact exT_false h0 h1 h39) (by rw [Nat.zero_add]; exact hf)
        rw [Nat.zero_add] at hwk
        rw [hr'.elim id id] at hwk
        exact ⟨c, hwk⟩
      · have e : 21940 + (k - 21940) = k := by omega
        obtain ⟨c, r, hr', hwk⟩ := orbSl_spec hs1 (k - 21940) (by omega)
          (by rw [e]; exact exT_false h0 h1 h39) (by rw [e]; exact hf)
        rw [e] at hwk
        rw [hr'.elim id id] at hwk
        exact ⟨c, hwk⟩
    obtain ⟨c, hwk⟩ := hw
    obtain ⟨-, hn⟩ := orbit_count ok_wXC gT_lt h9 (c := c) (r := 53) (by norm_num)
    rw [hwk] at hn
    rw [nfix_tab hX hk, hn, hr]
    simp
  · rw [hX.ap hk]
    simp [hf]

end CertificateChecks.KernelFi23R

end
