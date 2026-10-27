module

public import Certificates.Kernel.MonsterExist.P5.Pbar
public import CFSG.Certificates.Kernel.WeylE6Sound
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CertificateChecks.MonsterExist.P5

open CFSG.Monster.Existence.StdOdd.P5 CFSG.KC.WeylE6

@[expose] def PAText : String := include_str "p5pa.hex"

@[expose] noncomputable def PAN : Nat := by hex_nat PAText 39365 8205318441028770485

@[expose] noncomputable def paF (i : Fin 81) (n : Nat) : Nat := f8 PAN (243 * i.val + n)

theorem pa_one : ∀ n : Fin 243, paF 1 n.val = encV (aMat.mulVec (decV n.val)) := by decide +kernel

theorem pa_two : ∀ n : Fin 243, paF 2 n.val = encV (bMat.mulVec (decV n.val)) := by decide +kernel

theorem pa_zero : ∀ n : Fin 243, paF 0 n.val = n.val := by decide +kernel

theorem pa_step : ∀ i : Fin 81, ∀ n : Fin 243,
    paF (raF i) n.val = paF i (paF 1 n.val) ∧ paF (rbF i) n.val = paF i (paF 2 n.val) := by
  decide +kernel

abbrev RowOK (i : Fin 81) : Prop := ∀ n < 243, paF i n = encV ((pmat i).mulVec (decV n))

theorem rowOK_zero : RowOK 0 := fun n hn => by
  rw [pmat_zero, Matrix.one_mulVec, encV_decV hn]
  exact pa_zero ⟨n, hn⟩

theorem rowOK_step {i : Fin 81} (h : RowOK i) (c : Fin 2) : RowOK (step c i) := by
  intro n hn
  have hcase : ∀ (M : M5) (j : Fin 81), pmat j = pmat i * M →
      (∀ n < 243, paF j n = paF i (encV (M.mulVec (decV n)))) → paF j n = encV ((pmat j).mulVec (decV n)) := by
    intro M j hj hp
    rw [hp n hn, h _ (encV_lt _), decV_encV, hj, ← Matrix.mulVec_mulVec]
  unfold step
  split
  · refine hcase aMat (ra i) (pmat_ra i) fun m hm => ?_
    rw [ra_eq, (pa_step i ⟨m, hm⟩).1, pa_one ⟨m, hm⟩]
  · refine hcase bMat (rb i) (pmat_rb i) fun m hm => ?_
    rw [rb_eq, (pa_step i ⟨m, hm⟩).2, pa_two ⟨m, hm⟩]

theorem rowOK_walk (w : List (Fin 2)) : ∀ i, RowOK i → RowOK (walk w i) := by
  induction w with
  | nil => exact fun i h => h
  | cons c w ih => exact fun i h => ih _ (rowOK_step h c)

theorem paF_spec (i : Fin 81) : RowOK i := by
  have := rowOK_walk (pw i) 0 rowOK_zero
  rwa [walk_pw] at this

theorem encV_inj {x y : E5} (h : encV x = encV y) : x = y := by
  rw [← decV_encV x, ← decV_encV y, h]

@[expose] noncomputable def fixedCardM (l : List (Fin 81)) : ℕ :=
  (List.range 243).countP fun n => l.all fun i => Nat.beq (paF i n) n

theorem fixedCardM_eq (l : List (Fin 81)) :
    fixedCardM l = ((Finset.range 243).filter fun n => ∀ i ∈ l, paF i n = n).card := by
  rw [fixedCardM, List.countP_eq_length_filter, Finset.card_def, Finset.filter_val,
    Finset.range_val, Multiset.range, Multiset.filter_coe, Multiset.coe_card]
  refine congrArg List.length (List.filter_congr fun n _ => ?_)
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, Nat.beq_eq, decide_eq_true_eq]

theorem fixedCardL_eq : fixedCardL = fixedCardM := by
  funext l
  rw [fixedCardL, fixedCardM_eq, ← Finset.card_map ⟨encV, fun _ _ h => encV_inj h⟩]
  refine congrArg Finset.card (Finset.ext fun n => ?_)
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨v, hv, hn⟩
    change encV v = n at hn
    subst hn
    refine ⟨encV_lt v, fun i hi => ?_⟩
    rw [paF_spec i _ (encV_lt v), decV_encV, hv i hi]
  · rintro ⟨hn, hv⟩
    refine ⟨decV n, fun i hi => encV_inj ?_, encV_decV hn⟩
    rw [← paF_spec i _ hn, hv i hi, encV_decV hn]

end CertificateChecks.MonsterExist.P5

end
