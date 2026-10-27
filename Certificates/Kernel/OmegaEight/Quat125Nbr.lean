module

public import Certificates.Kernel.OmegaEight.Quat125Ident
public import Certificates.Kernel.OmegaEight.Quat125KN
public import CFSG.Certificates.Kernel.Common.ForallTree
import CFSG.Certificates.Kernel.PackSetSound
public import CFSG.ClassicalInvolution.Asc77.AscT8X4
public import CFSG.ClassicalInvolution.Asc77.AscT8YA3
public import CFSG.ClassicalInvolution.AschTight.S1916F2a
public import CFSG.ClassicalInvolution.AschTight.S19BCSW
public import CFSG.ClassicalInvolution.Q3.Q3AMDBStmt
public import CFSG.ClassicalInvolution.Q3.Q3T6DCfg
public import CFSG.ClassicalInvolution.Q3.Q3T6DPart1
public import CFSG.ClassicalInvolution.Q3.Q3T6OpenSDEnd
public import CFSG.ClassicalInvolution.Q3.Q3T8B10
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T01
public import CFSG.ClassicalInvolution.Q3.Q3T8P26T02
public import CFSG.ClassicalInvolution.Q3.Q3T8P26TH01
public import CFSG.ClassicalInvolution.Q3.Q3TIMain
public import CFSG.ClassicalInvolution.Q3.Q3TIYOAMain
public import CFSG.ClassicalInvolution.Q3.Q3TKMem
public import CFSG.ClassicalInvolution.Q3.TL3S8Gold
public import CFSG.ClassicalInvolution.Q3.TL3S8Sd
public import CFSG.ClassicalInvolution.Q3.TL4SecIdDatum
public import CFSG.ClassicalInvolution.SmallCases.NobqFinal
public import CFSG.Foundations
public import CFSG.Goldschmidt.Steps.G310Core2
public import CFSG.Goldschmidt.Steps.G37Core
public import CFSG.Goldschmidt75.TheoremB
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingEscape
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingInherit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherStrongEmbeddingThreeOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Moufang.Three
public import Certificates.Kernel.OmegaEight.Quat125Glue
public import Certificates.Kernel.OmegaEight.Roots127Glue
public import Certificates.Kernel.OmegaEight.Roots127Sound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8.Q125

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
open CertificateChecks.KernelO8 CertificateChecks.KernelO8.E4C CFSG.KC.PCent
open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4

theorem q125_mask9 : mask 9 = 511 := rfl

theorem q125_pg {p : Nat} (hp : CFSG.KC.BfsPin.PP 360 9 p) (i : Fin 360) :
    pg 9 511 p i = (toPerm 360 9 p i).val := by
  rw [toPerm_apply hp, q125_mask9]

theorem q125_root_pp {l : Nat} (hl : l < 8) : CFSG.KC.BfsPin.PP 360 9 (AP.S l) :=
  e4c_pp (root_facts hl).2.2.1

theorem q125_pid_pp : CFSG.KC.BfsPin.PP 360 9 pid := CFSG.KC.BfsPin.PP.id ch550106sz

theorem q125_e4L_pp : ∀ x ∈ e4L, CFSG.KC.BfsPin.PP 360 9 x := by
  obtain ⟨-, -, -, -, -, hpx, hpu, hpv⟩ := e4c_pm
  intro P hP
  simp only [e4L, e4Q, List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact q125_pid_pp
  · exact hpx
  · exact hpu
  · exact hpu.mul hpx
  · exact hpv
  · exact hpv.mul hpx
  · exact hpu.mul hpv
  · exact (hpu.mul hpv).mul hpx

theorem q125_e4Mem {L : List Nat} {x : Nat} (h : e4Mem L x = true) : x ∈ L := by
  unfold e4Mem at h
  obtain ⟨l, hl, he⟩ := List.any_eq_true.1 h
  rwa [Nat.eq_of_beq_eq_true he]

theorem q125_allL {f : Nat → Bool} : ∀ {L : List Nat}, q125AllL L f = true → ∀ x ∈ L, f x = true
  | [], _, x, hx => absurd hx List.not_mem_nil
  | a :: L, h, x, hx => by
    obtain ⟨h1, h2⟩ := q125bAnd.1 h
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact q125_allL h2 x hx

theorem q125_notB {b : Bool} (h : bIf(b, false, true) = true) : b = false := by
  revert h
  cases b <;> decide

@[expose] noncomputable def q125LP (l : Nat) : Equiv.Perm (Fin 360) :=
  if l = 0 then 1 else toPerm 360 9 (AP.S (l - 1))

@[expose] noncomputable def q125Lt (W i : Nat) : Nat := fld(W, Nat.mul (nat_lit 4) i, nat_lit 15)

@[expose] noncomputable def q125WP (W : Nat) : Equiv.Perm (Fin 360) :=
  ((List.range 20).map fun i => q125LP (q125Lt W i)).prod

theorem q125_GT {l p : Nat} (hl : l < 8) (hp : p < 360) :
    letK (gtK (fun l => AP.S l) 8) (l + 1) p = pg 9 511 (AP.S l) p := by
  have h := kLet125
  rw [q125sB] at h
  have h1 := CFSG.KC.Pack.allN_spec h l hl
  beta_reduce at h1
  exact Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec h1 p hp)

theorem q125_LP_apply {l : Nat} (hl : l ≤ 8) (p : Fin 360) :
    letK (gtK (fun l => AP.S l) 8) l p = (q125LP l p).val := by
  rcases l with _ | l
  · rw [q125LP, if_pos rfl, Equiv.Perm.one_apply]
    rfl
  · rw [q125_GT (by omega) p.2, q125_pg (q125_root_pp (by omega))]
    simp only [q125LP, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]

theorem q125_LP_inv {l : Nat} (hl : l ≤ 8) : (q125LP l)⁻¹ = q125LP l := by
  unfold q125LP
  split_ifs with h0
  · exact inv_one
  · have h := kInvol125
    have hl' : l - 1 < 8 := by omega
    have e := Nat.eq_of_beq_eq_true (CFSG.KC.Pack.allN_spec h (l - 1) hl')
    have hp := q125_root_pp hl'
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← e4c_mul hp hp, e, e4c_pid]

@[expose] noncomputable def q125Up (W q n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) q (fun i ih => strictN ih fun p =>
    letK (gtK (fun l => AP.S l) 8) (fld(W, Nat.mul (nat_lit 4) i, nat_lit 15)) p) n

@[expose] noncomputable def q125Dn (W q n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) q (fun i ih => strictN ih fun p =>
    letK (gtK (fun l => AP.S l) 8)
      (fld(W, Nat.mul (nat_lit 4) (Nat.sub (nat_lit 19) i), nat_lit 15)) p) n

theorem q125Up_succ (W q n : Nat) :
    q125Up W q (n + 1) = letK (gtK (fun l => AP.S l) 8) (q125Lt W n) (q125Up W q n) :=
  q125sN (q125Up W q n) fun p => letK (gtK (fun l => AP.S l) 8) (q125Lt W n) p

theorem q125Dn_succ (W q n : Nat) :
    q125Dn W q (n + 1) = letK (gtK (fun l => AP.S l) 8) (q125Lt W (19 - n)) (q125Dn W q n) :=
  q125sN (q125Dn W q n) fun p => letK (gtK (fun l => AP.S l) 8) (q125Lt W (19 - n)) p

theorem q125_walkUp_n {W : Nat} (hL : ∀ i, q125Lt W i ≤ 8) (q : Fin 360) : ∀ n,
    q125Up W q.val n = ((((List.range n).map fun i => q125LP (q125Lt W i)).reverse.prod) q).val
  | 0 => by simp [q125Up]
  | n + 1 => by
    rw [q125Up_succ, q125_walkUp_n hL q n, q125_LP_apply (hL n), List.range_succ,
      List.map_append, List.reverse_append, List.map_singleton, List.reverse_singleton,
      List.singleton_append, List.prod_cons, Equiv.Perm.mul_apply]

theorem q125_walkDn_n {W : Nat} (hL : ∀ i, q125Lt W i ≤ 8) (q : Fin 360) : ∀ n, n ≤ 20 →
    q125Dn W q.val n = ((((List.range' (20 - n) n).map fun i => q125LP (q125Lt W i)).prod) q).val
  | 0, _ => by simp [q125Dn]
  | n + 1, h => by
    have e1 : 20 - (n + 1) = 19 - n := by omega
    have e2 : 19 - n + 1 = 20 - n := by omega
    rw [q125Dn_succ, q125_walkDn_n hL q n (by omega), q125_LP_apply (hL _), e1,
      List.range'_succ, e2, List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]

theorem q125_walkUp {W : Nat} (hL : ∀ i, q125Lt W i ≤ 8) (q : Fin 360) :
    walkUp (gtK (fun l => AP.S l) 8) W q = ((q125WP W)⁻¹ q).val := by
  have hmap : ((List.range 20).map fun i => q125LP (q125Lt W i)) =
      (List.range 20).map ((fun x => x⁻¹) ∘ fun i => q125LP (q125Lt W i)) :=
    List.map_congr_left fun i _ => (q125_LP_inv (hL i)).symm
  have e : walkUp (gtK (fun l => AP.S l) 8) W q = q125Up W q.val 20 := rfl
  rw [e, q125_walkUp_n hL q 20, q125WP, List.prod_inv_reverse, List.map_map, ← hmap]

theorem q125_walkDn {W : Nat} (hL : ∀ i, q125Lt W i ≤ 8) (q : Fin 360) :
    walkDn (gtK (fun l => AP.S l) 8) W q = (q125WP W q).val := by
  have e : walkDn (gtK (fun l => AP.S l) 8) W q = q125Dn W q.val 20 := rfl
  rw [e, q125_walkDn_n hL q 20 le_rfl, Nat.sub_self, ← List.range_eq_range', q125WP]

#kc_forall_tree ch125mN (fun s => q125Mem s = true) 13 CertificateChecks.KernelO8.Q125.ch125m

theorem q125_row {k : Nat} (hk : k < 6300) :
    memRowK RT MT swaps (fixMK e4U om0V (nat_lit 240)) (mainK 0) k = true := by
  have hs : k / 512 < 13 := by omega
  have h := ch125mN (k / 512) hs
  unfold q125Mem at h
  rw [q125sB] at h
  have h2 := CFSG.KC.Pack.allBlk_spec h (k % 512) (Nat.mod_lt _ (by norm_num))
  beta_reduce at h2
  have e : Nat.add (Nat.mul (nat_lit 512) (k / 512)) (k % 512) = k := by
    change 512 * (k / 512) + k % 512 = k
    omega
  rw [e, q125bIfT (q125blt.2 hk)] at h2
  exact (q125bAnd.1 h2).1

theorem q125_row_facts {M0 X0 k : Nat} (h : memRowK RT MT swaps M0 X0 k = true) :
    (k = 0 → rowW (RT k) = 0) ∧
    (k ≠ 0 → ∃ p < 6300, 0 < Nat.land (rowW (RT k)) 15 ∧ Nat.land (rowW (RT k)) 15 < 9 ∧
      rowW (RT p) = Nat.shiftRight (rowW (RT k)) 4) ∧
    (Nat.shiftRight (rowN (RT k)) 9 = 0 → Nat.land (rowN (RT k)) 511 < 240 ∧
      bitK (MT k) (Nat.land (rowN (RT k)) 511) = true ∧
      pg 9 511 X0 (Nat.land (rowN (RT k)) 511) < 240 ∧
      bitK (MT k) (pg 9 511 X0 (Nat.land (rowN (RT k)) 511)) = false) ∧
    (Nat.shiftRight (rowN (RT k)) 9 = 3 → k = 0 ∨ k = 1 ∨ k = 3 ∨ k = 4) ∧
    Nat.shiftRight (rowN (RT k)) 9 < 4 := by
  unfold memRowK at h
  simp only [q125sB] at h
  obtain ⟨h1, h2⟩ := q125bAnd.1 h
  refine ⟨fun hk => ?_, fun hk => ?_, fun ht => ?_, fun ht => ?_, ?_⟩
  · rw [q125bIfT (q125beqT hk)] at h1
    exact Nat.eq_of_beq_eq_true (q125bAnd.1 h1).1
  · rw [q125bIfF (q125beqF hk)] at h1
    simp only [q125bAnd] at h1
    obtain ⟨hp, hl0, hl9, hW, -⟩ := h1
    exact ⟨_, q125blt.1 hp, q125blt.1 hl0, q125blt.1 hl9, Nat.eq_of_beq_eq_true hW⟩
  · rw [q125bIfT (q125beqT ht)] at h2
    simp only [q125bAnd] at h2
    obtain ⟨hq, hb, hx, hn⟩ := h2
    exact ⟨q125blt.1 hq, hb, q125blt.1 hx, q125_notB hn⟩
  · have hn0 : Nat.shiftRight (rowN (RT k)) 9 ≠ 0 := by omega
    rw [q125bIfF (q125beqF hn0), q125bIfT (q125beqT ht)] at h2
    by_cases h0 : k = 0
    · exact Or.inl h0
    rw [q125bIfF (q125beqF h0)] at h2
    by_cases h1 : k = 1
    · exact Or.inr (Or.inl h1)
    rw [q125bIfF (q125beqF h1)] at h2
    by_cases h3 : k = 3
    · exact Or.inr (Or.inr (Or.inl h3))
    rw [q125bIfF (q125beqF h3)] at h2
    exact Or.inr (Or.inr (Or.inr (Nat.eq_of_beq_eq_true h2)))
  · by_cases h0 : Nat.shiftRight (rowN (RT k)) 9 = 0
    · omega
    rw [q125bIfF (q125beqF h0)] at h2
    by_cases h3 : Nat.shiftRight (rowN (RT k)) 9 = 3
    · omega
    rw [q125bIfF (q125beqF h3)] at h2
    have := q125blt.1 h2
    omega

theorem q125_letters : ∀ W, ∀ k < 6300, rowW (RT k) = W → ∀ i, q125Lt W i ≤ 8 := by
  intro W
  induction W using Nat.strong_induction_on with
  | _ W ih =>
  intro k hk hW i
  obtain ⟨h0, h1, -⟩ := q125_row_facts (q125_row hk)
  by_cases hk0 : k = 0
  · rw [h0 hk0] at hW
    subst hW
    change (0 >>> (4 * i)) &&& 15 ≤ 8
    rw [Nat.zero_shiftRight, Nat.zero_and]
    omega
  · obtain ⟨p, hp, hl0, hl9, hpW⟩ := h1 hk0
    rw [hW] at hl0 hl9 hpW
    change 0 < W &&& 15 at hl0
    change W &&& 15 < 9 at hl9
    have hpos : 0 < W := by
      rcases Nat.eq_zero_or_pos W with rfl | h
      · rw [Nat.zero_and] at hl0
        exact absurd hl0 (lt_irrefl 0)
      · exact h
    have hlt : Nat.shiftRight W 4 < W := by
      change W >>> 4 < W
      rw [Nat.shiftRight_eq_div_pow]
      exact Nat.div_lt_self hpos (by norm_num)
    rcases i with _ | i
    · change (W >>> (4 * 0)) &&& 15 ≤ 8
      rw [Nat.mul_zero, Nat.shiftRight_zero]
      omega
    · have h' := ih _ hlt p hp hpW i
      have e : q125Lt W (i + 1) = q125Lt (Nat.shiftRight W 4) i := by
        change (W >>> (4 * (i + 1))) &&& 15 = ((W >>> 4) >>> (4 * i)) &&& 15
        rw [← Nat.shiftRight_add]
        congr 2
        ring
      rw [e]
      exact h'

theorem q125_K0_cl {x : Nat} (hx : x ∈ e4L) :
    q125ClAt e4U om0V (pinv e4U) (pinv om0V) (mainK 0) x = true := by
  have h := kK0Cl125
  simp only [q125bAnd, q125sB] at h
  exact q125_allL h.2 x hx

theorem q125_K0_sub {y : Equiv.Perm (Fin 360)} (hy : y ∈ q125K0) :
    ∃ x ∈ e4L, toPerm 360 9 x = y := by
  obtain ⟨-, -, -, -, -, -, hpu, hpv⟩ := e4c_pm
  have h := kK0Cl125
  simp only [q125bAnd] at h
  have h1 := h.1
  have eu : toPerm 360 9 (pinv e4U) = (toPerm 360 9 e4U)⁻¹ := toPerm_inv hpu
  have ev : toPerm 360 9 (pinv om0V) = (toPerm 360 9 om0V)⁻¹ := toPerm_inv hpv
  unfold q125K0 at hy
  induction hy using Subgroup.closure_induction_left with
  | one => exact ⟨pid, q125_e4Mem h1, e4c_pid⟩
  | mul_left a ha y _ hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    have hc := q125_K0_cl hx
    unfold q125ClAt at hc
    simp only [q125bAnd] at hc
    have px := q125_e4L_pp x hx
    rcases ha with rfl | rfl
    · exact ⟨pc e4U x, q125_e4Mem hc.1, e4c_mul hpu px⟩
    · exact ⟨pc om0V x, q125_e4Mem hc.2.1, e4c_mul hpv px⟩
  | inv_mul_cancel a ha y _ hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    have hc := q125_K0_cl hx
    unfold q125ClAt at hc
    simp only [q125bAnd] at hc
    have px := q125_e4L_pp x hx
    rcases ha with rfl | rfl
    · exact ⟨pc (pinv e4U) x, q125_e4Mem hc.2.2.1, by rw [e4c_mul (p := pinv e4U) hpu.inv px, eu]⟩
    · exact ⟨pc (pinv om0V) x, q125_e4Mem hc.2.2.2.1,
        by rw [e4c_mul (p := pinv om0V) hpv.inv px, ev]⟩

theorem q125_x0_mem : toPerm 360 9 (mainK 0) ∈ q125K0 := by
  rw [← e4c_u0_sq]
  have hU : toPerm 360 9 e4U ∈ q125K0 := Subgroup.subset_closure (Set.mem_insert _ _)
  exact q125K0.mul_mem hU hU

theorem q125_invol {y : Equiv.Perm (Fin 360)} (hy : y ∈ q125K0) (h2 : y * y = 1) (h1 : y ≠ 1) :
    y = toPerm 360 9 (mainK 0) := by
  obtain ⟨x, hx, rfl⟩ := q125_K0_sub hy
  have hc := q125_K0_cl hx
  unfold q125ClAt at hc
  simp only [q125bAnd] at hc
  have px := q125_e4L_pp x hx
  have hxx : pc x x = pid :=
    toPerm_injective (p := pc x x) (px.mul px) q125_pid_pp (by rw [e4c_mul px px, h2, e4c_pid])
  have hl := hc.2.2.2.2
  rw [q125bIfT (q125beqT hxx)] at hl
  cases hb : Nat.beq x pid
  · rw [q125bIfF hb] at hl
    rw [Nat.eq_of_beq_eq_true hl]
  · exact absurd (by rw [Nat.eq_of_beq_eq_true hb, e4c_pid]) h1

theorem q125_conj_x0 {h : Equiv.Perm (Fin 360)}
    (hh : h ∈ Subgroup.normalizer (q125K0 : Set (Equiv.Perm (Fin 360)))) :
    h * toPerm 360 9 (mainK 0) * h⁻¹ = toPerm 360 9 (mainK 0) := by
  obtain ⟨-, hx2, hx1⟩ := e4c_x0_facts
  have hm : h * toPerm 360 9 (mainK 0) * h⁻¹ ∈ q125K0 :=
    (Subgroup.mem_normalizer_iff.1 hh _).1 q125_x0_mem
  refine q125_invol hm ?_ ?_
  · calc h * toPerm 360 9 (mainK 0) * h⁻¹ * (h * toPerm 360 9 (mainK 0) * h⁻¹) =
        h * (toPerm 360 9 (mainK 0) * toPerm 360 9 (mainK 0)) * h⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  · intro e
    apply hx1
    calc toPerm 360 9 (mainK 0) = h⁻¹ * (h * toPerm 360 9 (mainK 0) * h⁻¹) * h := by group
      _ = 1 := by rw [e]; group

@[expose] def q125Fix (p : Fin 360) : Prop :=
  toPerm 360 9 e4U p = p ∧ toPerm 360 9 om0V p = p

theorem q125_fix_K0 {p : Fin 360} (hp : q125Fix p) {y : Equiv.Perm (Fin 360)} (hy : y ∈ q125K0) :
    y p = p := by
  have hle : q125K0 ≤ MulAction.stabilizer (Equiv.Perm (Fin 360)) p := by
    rw [q125K0, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hp.1
    · exact hp.2
  exact hle hy

theorem q125_fix_norm {p : Fin 360} (hp : q125Fix p) {y : Equiv.Perm (Fin 360)}
    (hy : y ∈ Subgroup.normalizer (q125K0 : Set (Equiv.Perm (Fin 360)))) : q125Fix (y p) := by
  have hyi := Subgroup.inv_mem _ hy
  have key : ∀ a ∈ q125K0, a (y p) = y p := fun a ha => by
    have hm : y⁻¹ * a * y⁻¹⁻¹ ∈ q125K0 := (Subgroup.mem_normalizer_iff.1 hyi a).1 ha
    rw [inv_inv] at hm
    have e := q125_fix_K0 hp hm
    calc a (y p) = y ((y⁻¹ * a * y) p) := by simp [Equiv.Perm.mul_apply]
      _ = y p := by rw [e]
  exact ⟨key _ (Subgroup.subset_closure (Set.mem_insert _ _)),
    key _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))⟩

theorem q125_fixB (p : Fin 360) : bitK (fixMK e4U om0V 360) p.val = true ↔ q125Fix p := by
  obtain ⟨-, -, -, -, -, -, hpu, hpv⟩ := e4c_pm
  have h := kFix125
  simp only [q125sB] at h
  have hp := CFSG.KC.Pack.allN_spec h p.val p.2
  beta_reduce at hp
  have e : q125Fix p ↔ pg 9 511 e4U p = p ∧ pg 9 511 om0V p = p := by
    rw [q125_pg hpu, q125_pg hpv, q125Fix, Fin.ext_iff, Fin.ext_iff]
  rw [e]
  cases hb : bitK (fixMK e4U om0V 360) p.val
  · rw [q125bIfF hb] at hp
    have hn := q125_notB hp
    refine ⟨fun h => Bool.noConfusion h, fun ⟨h1, h2⟩ => ?_⟩
    rw [q125beqT h1, q125beqT h2] at hn
    exact absurd hn (by decide)
  · rw [q125bIfT hb] at hp
    obtain ⟨h1, h2⟩ := q125bAnd.1 hp
    exact ⟨fun _ => ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩, fun _ => rfl⟩

theorem q125_not_le_walk {w z : Equiv.Perm (Fin 360)} {q : Fin 360} (hz : z ∈ q125K0)
    (hq : q125Fix q) (hout : ¬ q125Fix ((w * z * w⁻¹) q)) :
    ¬ conjSub w q125K0 ≤ Subgroup.normalizer (q125K0 : Set (Equiv.Perm (Fin 360))) :=
  fun hle => hout (q125_fix_norm hq (hle (conj_mem_conjSub hz)))

theorem q125_not_le_x0 {w : Equiv.Perm (Fin 360)} {q : Fin 360} (hq : q125Fix (w⁻¹ q))
    (hout : ¬ q125Fix (w⁻¹ (toPerm 360 9 (mainK 0) q))) :
    ¬ conjSub w q125K0 ≤ Subgroup.normalizer (q125K0 : Set (Equiv.Perm (Fin 360))) := by
  intro hle
  apply hout
  have key : ∀ a ∈ q125K0, a (w⁻¹ (toPerm 360 9 (mainK 0) q)) = w⁻¹ (toPerm 360 9 (mainK 0) q) := by
    intro a ha
    have hc := q125_conj_x0 (hle (conj_mem_conjSub ha))
    have e : a * (w⁻¹ * toPerm 360 9 (mainK 0) * w) = w⁻¹ * toPerm 360 9 (mainK 0) * w * a := by
      calc a * (w⁻¹ * toPerm 360 9 (mainK 0) * w) =
          w⁻¹ * ((w * a * w⁻¹) * toPerm 360 9 (mainK 0) * (w * a * w⁻¹)⁻¹) * w * a := by group
        _ = w⁻¹ * toPerm 360 9 (mainK 0) * w * a := by rw [hc]
    have e3 : (w⁻¹ * toPerm 360 9 (mainK 0) * w) (w⁻¹ q) = w⁻¹ (toPerm 360 9 (mainK 0) q) := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply w w⁻¹,
        mul_inv_cancel, Equiv.Perm.one_apply]
    calc a (w⁻¹ (toPerm 360 9 (mainK 0) q)) =
        (a * (w⁻¹ * toPerm 360 9 (mainK 0) * w)) (w⁻¹ q) := by
          rw [Equiv.Perm.mul_apply, e3]
      _ = (w⁻¹ * toPerm 360 9 (mainK 0) * w) (a (w⁻¹ q)) := by
          rw [e, Equiv.Perm.mul_apply]
      _ = w⁻¹ (toPerm 360 9 (mainK 0) q) := by rw [q125_fix_K0 hq ha, e3]
  exact ⟨key _ (Subgroup.subset_closure (Set.mem_insert _ _)),
    key _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))⟩

theorem q125_walk {k : Nat} (hk : k < 6300) (ht0 : 0 < Nat.shiftRight (rowN (RT k)) 9)
    (ht3 : Nat.shiftRight (rowN (RT k)) 9 < 3) :
    Nat.land (rowN (RT k)) 511 < 360 ∧
    bitK (fixMK e4U om0V 360) (Nat.land (rowN (RT k)) 511) = true ∧
    bitK (fixMK e4U om0V 360) (walkDn (gtK (fun l => AP.S l) 8) (rowW (RT k))
      (pg 9 511 (nIf(Nat.beq (Nat.shiftRight (rowN (RT k)) 9) 1, e4U, om0V))
        (walkUp (gtK (fun l => AP.S l) 8) (rowW (RT k)) (Nat.land (rowN (RT k)) 511)))) =
      false := by
  have h := kWalk125
  simp only [q125sB] at h
  have h' := CFSG.KC.Pack.allN_spec h k hk
  unfold walkOK at h'
  simp only [q125sB] at h'
  rw [q125bIfT (q125bAnd.2 ⟨q125blt.2 ht0, q125blt.2 ht3⟩)] at h'
  obtain ⟨a, h''⟩ := q125bAnd.1 h'
  obtain ⟨b, c⟩ := q125bAnd.1 h''
  exact ⟨q125blt.1 a, b, q125_notB c⟩

theorem q125_nbr {k : Nat} (hk : k < 6300) (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hk3 : k ≠ 3)
    (hk4 : k ≠ 4) (hM : ∀ p : Fin 360, p.val < 240 →
      (bitK (MT k) p.val = true ↔ q125Fix ((q125WP (rowW (RT k)))⁻¹ p))) :
    ¬ conjSub (q125WP (rowW (RT k))) q125K0 ≤
      Subgroup.normalizer (q125K0 : Set (Equiv.Perm (Fin 360))) := by
  obtain ⟨-, -, -, -, -, hpx, hpu, hpv⟩ := e4c_pm
  have hL := q125_letters _ k hk rfl
  obtain ⟨-, -, h0, h3, h4⟩ := q125_row_facts (q125_row hk)
  by_cases ht0 : Nat.shiftRight (rowN (RT k)) 9 = 0
  · obtain ⟨hq, hb, hx, hxb⟩ := h0 ht0
    have hq' : Nat.land (rowN (RT k)) 511 < 360 := by omega
    rw [q125_pg hpx ⟨_, hq'⟩] at hx hxb
    refine q125_not_le_x0 (q := ⟨_, hq'⟩) ((hM ⟨_, hq'⟩ hq).1 hb) fun hf => ?_
    rw [← hM _ hx, hxb] at hf
    exact Bool.noConfusion hf
  by_cases ht3 : Nat.shiftRight (rowN (RT k)) 9 = 3
  · rcases h3 ht3 with h | h | h | h <;> contradiction
  obtain ⟨hq, hb, hout⟩ := q125_walk hk (by omega) (by omega)
  have hb' := (q125_fixB ⟨_, hq⟩).1 hb
  rw [q125_walkUp hL ⟨_, hq⟩] at hout
  have hU : toPerm 360 9 e4U ∈ q125K0 := Subgroup.subset_closure (Set.mem_insert _ _)
  have hV : toPerm 360 9 om0V ∈ q125K0 := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  by_cases ht1 : Nat.shiftRight (rowN (RT k)) 9 = 1
  · rw [q125nIfT (q125beqT ht1), q125_pg hpu, q125_walkDn hL] at hout
    refine q125_not_le_walk hU hb' fun hf => ?_
    rw [← q125_fixB, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hout] at hf
    exact Bool.noConfusion hf
  · rw [q125nIfF (q125beqF ht1), q125_pg hpv, q125_walkDn hL] at hout
    refine q125_not_le_walk hV hb' fun hf => ?_
    rw [← q125_fixB, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hout] at hf
    exact Bool.noConfusion hf

theorem q125_WP1 : q125WP 1 = toPerm 360 9 (AP.S 0) := by
  unfold q125WP
  rw [List.range_succ_eq_map (n := 19), List.map_cons, List.prod_cons, List.map_map]
  have h0 : q125LP (q125Lt 1 0) = toPerm 360 9 (AP.S 0) := by
    have e : q125Lt 1 0 = 1 := rfl
    rw [e, q125LP, if_neg one_ne_zero]
  have hr : ((List.range 19).map ((fun i => q125LP (q125Lt 1 i)) ∘ Nat.succ)).prod = 1 := by
    refine List.prod_eq_one fun x hx => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    have e : q125Lt 1 (i + 1) = 0 := by
      change (1 >>> (4 * (i + 1))) &&& 15 = 0
      rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (Nat.one_lt_two_pow (by omega)),
        Nat.zero_and]
    simp only [Function.comp_apply, Nat.succ_eq_add_one, e, q125LP, ↓reduceIte]
  rw [h0, hr, mul_one]

theorem q125_edge : conjSub (q125WP (rowW (RT 1))) q125K0 ≠ q125K0 ∧
    conjSub (q125WP (rowW (RT 1))) q125K0 ≤
      Subgroup.normalizer (q125K0 : Set (Equiv.Perm (Fin 360))) := by
  obtain ⟨-, -, -, -, -, -, hpu, hpv⟩ := e4c_pm
  rw [Nat.eq_of_beq_eq_true kRow1W125, q125_WP1]
  have hX := q125_root_pp (l := 0) (by norm_num)
  have hk := kE4Nbr
  simp only [q125bAnd] at hk
  have he := hk.2.2.1
  unfold e4EdgeAt at he
  simp only [q125bAnd] at he
  have hE := he.2.2
  unfold e4Edge at hE
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hE
  obtain ⟨⟨hn, hnu⟩, hnv⟩ := hE
  refine ⟨fun e => ?_, ?_⟩
  · have key : ∀ z, CFSG.KC.BfsPin.PP 360 9 z → toPerm 360 9 z ∈ q125K0 →
        e4Mem e4L (cj (AP.S 0) z) = true := by
      intro z hz hzK
      have hc : toPerm 360 9 (cj (AP.S 0) z) ∈ q125K0 := by
        rw [q125_toPerm_cj hX hz, ← e]
        exact conj_mem_conjSub hzK
      obtain ⟨x, hx, ex⟩ := q125_K0_sub hc
      have hxe := toPerm_injective (q125_e4L_pp x hx) (q125_PP_cj hX hz) ex
      unfold e4Mem
      exact List.any_eq_true.2 ⟨x, hx, by rw [hxe]; exact Nat.beq_refl _⟩
    have hN : e4Norms e4L e4U om0V (AP.S 0) = true := by
      unfold e4Norms
      rw [Bool.and_eq_true]
      exact ⟨key _ hpu (Subgroup.subset_closure (Set.mem_insert _ _)),
        key _ hpv (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))⟩
    rw [hn] at hN
    exact Bool.noConfusion hN
  · have hc : conjSub (toPerm 360 9 (AP.S 0)) q125K0 = Subgroup.closure
        {toPerm 360 9 (AP.S 0) * toPerm 360 9 e4U * (toPerm 360 9 (AP.S 0))⁻¹,
          toPerm 360 9 (AP.S 0) * toPerm 360 9 om0V * (toPerm 360 9 (AP.S 0))⁻¹} := by
      unfold conjSub q125K0
      rw [MonoidHom.map_closure, Set.image_pair]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hc, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [← q125_toPerm_cj hX hpu]
      exact q125_norm (q125_PP_cj hX hpu) hnu
    · rw [← q125_toPerm_cj hX hpv]
      exact q125_norm (q125_PP_cj hX hpv) hnv

end CertificateChecks.KernelO8.Q125

end
