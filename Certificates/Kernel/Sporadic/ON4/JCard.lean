
module

public import Certificates.Kernel.Sporadic.ON4.Arrays
public import Certificates.Kernel.Sporadic.ON.Order2212

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON4K

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.TW CFSG.KS.Words CFSG.ONSchreier CFSG.ONSchreier.Native
open CFSG.Sporadic.ON CFSG.Monster.B.Co2 CertificateChecks.KernelSpor.ON3
open CertificateChecks.KernelSpor.ON (TT UU Pq rho perm_eq rho_tab Pq_injective mv_facts
  ga_smul_Pq gb_smul_Pq TT_lt UU_lt TT_UU perm_facts')
open CFSG.Sporadic.ON.Native (nPts)

@[expose] def InJ (T : Nat → Nat) : Prop :=
  ∃ g : J, ∀ i < 245520, T i < 245520 ∧ g • Pq i = Pq (T i)

theorem inJ_comp {T U : Nat → Nat} (hT : InJ T) (hU : InJ U) : InJ fun i => T (U i) := by
  obtain ⟨g, hg⟩ := hT
  obtain ⟨h, hh⟩ := hU
  refine ⟨g * h, fun i hi => ⟨(hg _ (hh i hi).1).1, ?_⟩⟩
  rw [mul_smul, (hh i hi).2, (hg _ (hh i hi).1).2]

theorem inJ_inv {T U : Nat → Nat} (hT : InJ T) (hU : ∀ i < 245520, U i < 245520 ∧ T (U i) = i) :
    InJ U := by
  obtain ⟨g, hg⟩ := hT
  refine ⟨g⁻¹, fun i hi => ⟨(hU i hi).1, ?_⟩⟩
  have e := (hg _ (hU i hi).1).2
  rw [(hU i hi).2] at e
  rw [← e, inv_smul_smul]

theorem inJ_congr {T T' : Nat → Nat} (hT : InJ T) (h : ∀ i < 245520, T i = T' i) : InJ T' := by
  obtain ⟨g, hg⟩ := hT
  exact ⟨g, fun i hi => by rw [← h i hi]; exact hg i hi⟩

theorem inJ_id : InJ fun i => i := ⟨1, fun _ hi => ⟨hi, one_smul _ _⟩⟩

theorem inJ_word {k : Nat} {G GI : Nat → Nat → Nat} (hG : ∀ h < k, InJ (G h) ∧ InJ (GI h)) :
    ∀ w : List Int, LetM k w → InJ fun x => w.foldr (GZ G GI) x
  | [], _ => inJ_id
  | l :: w, hw => by
    have ih := inJ_word hG w (fun z hz => hw z (List.mem_cons_of_mem l hz))
    obtain ⟨h1, h2⟩ := hw l List.mem_cons_self
    have hl : InJ (GZ G GI l) := by
      unfold GZ
      by_cases hp : 0 < l
      · simp only [hp, ite_true]
        exact (hG _ (by omega)).1
      · simp only [hp, ite_false]
        exact (hG _ (by omega)).2
    exact inJ_comp hl ih

theorem qon_letters_ok : ((List.range 5).all fun k =>
    (decW (ONV.WC (k + 2)) (ONV.WL (k + 2))).all fun l => l != 0 && decide (l.natAbs ≤ k + 2)) =
      true := by
  decide +kernel

theorem TT_word {j x : Nat} (hj : 2 ≤ j ∧ j < 7) (hx : x < 245520) :
    TT j x = (decW (ONV.WC j) (ONV.WL j)).foldr (GZ TT UU) x := by
  have h := CertificateChecks.KernelSpor.ON.pt_of CertificateChecks.KernelSpor.ON.trAll
    (fun _ => rfl) x hx
  have hl : j - 2 < 5 := by omega
  have h2 := allBlk_spec ((bAnd_iff _ _).1 h).2 (j - 2) hl
  have e : Nat.add 2 (j - 2) = j := by
    simp only [Nat.add_eq]
    omega
  rw [e] at h2
  rw [Nat.eq_of_beq_eq_true h2, trace_eq]

theorem TT_inJ : ∀ j < 7, InJ (TT j) ∧ InJ (UU j) := by
  have hU : ∀ j < 7, InJ (TT j) → InJ (UU j) := fun j hj hT =>
    inJ_inv hT fun i hi => ⟨UU_lt hi, TT_UU hj hi⟩
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    have hT : InJ (TT j) := by
      rcases Nat.lt_or_ge j 2 with h | h
      · interval_cases j
        · exact ⟨CFSG.Sporadic.ON.ga, fun i hi => ⟨(mv_facts hi).1, ga_smul_Pq hi⟩⟩
        · exact ⟨CFSG.Sporadic.ON.gb, fun i hi => ⟨(mv_facts hi).2.1, gb_smul_Pq hi⟩⟩
      · have hw : LetM j (decW (ONV.WC j) (ONV.WL j)) := by
          have := List.all_eq_true.1 qon_letters_ok (j - 2) (List.mem_range.2 (by omega))
          have e : j - 2 + 2 = j := by omega
          rw [e] at this
          exact letM_of this
        exact inJ_congr (inJ_word (k := j) (fun h hh => ih h hh (by omega)) _ hw)
          fun x hx => (TT_word ⟨h, hj⟩ hx).symm
    exact ⟨hT, hU j hj hT⟩

theorem trW_inJ {k : Nat} (hk : k < 17) : InJ (trW k) ∧ InJ (trW (k + 23)) := by
  refine ⟨inJ_congr (inJ_word (k := 7) TT_inJ _ (let7 hk)) fun x _ => ?_,
    inJ_congr (inJ_word (k := 7) TT_inJ _ (letM_invW (let7 hk))) fun x _ => ?_⟩
  · rw [trW_eq, dec_eq (by omega)]
  · rw [trW_eq, dec_inv (by omega)]

theorem mG_inJ {j : Nat} (hj : j < 3) : InJ (mG j) ∧ InJ (mGI j) := by
  have z := inJ_congr (trW_inJ (k := 0) (by norm_num)).1 fun x hx => ((tab_facts hx).1).symm
  interval_cases j
  · exact ⟨z, z⟩
  · exact ⟨inJ_congr (trW_inJ (k := 7) (by norm_num)).1
      fun x hx => ((tab_facts hx).2.2.2.2.2.2.2.2.1).symm, (trW_inJ (k := 7) (by norm_num)).2⟩
  · exact ⟨inJ_congr (trW_inJ (k := 8) (by norm_num)).1
      fun x hx => ((tab_facts hx).2.2.2.2.2.2.2.2.2.1).symm, (trW_inJ (k := 8) (by norm_num)).2⟩

theorem c_inJ : InJ CT ∧ InJ CIT := by
  have c := inJ_congr (trW_inJ (k := 2) (by norm_num)).1 fun x hx => ((tab_facts hx).2.2.1).symm
  exact ⟨c, inJ_inv c fun i hi => ⟨(c_CI hi).2, (c_CI hi).1⟩⟩

theorem jO_inJ {j : Nat} (hj : j < 6) : InJ (jO j) := by
  rcases Nat.lt_or_ge j 3 with h | h
  · refine inJ_congr (mG_inJ h).1 fun x _ => ?_
    unfold jO
    rw [nIf_t (blt_of h)]
  · refine inJ_congr (inJ_comp c_inJ.1 (inJ_comp (mG_inJ (j := j - 3) (by omega)).1 c_inJ.2))
      fun x _ => ?_
    unfold jO
    have hb : Nat.blt j 3 = false := blt_false h
    rw [hb]
    rfl

theorem joint_card_le :
    Nat.card (Subgroup.closure (Set.range fun j : Fin 6 => permOfArr 245520 jointArrs[j.val]!)) ≤
      245520 * 52136 * 36 := by
  have hle : Subgroup.closure (Set.range fun j : Fin 6 => permOfArr 245520 jointArrs[j.val]!) ≤
      rho.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨g, hg⟩ := jO_inJ j.isLt
    have hp := jO_pair j.val j.isLt
    refine ⟨g, ?_⟩
    symm
    refine perm_eq (jOrig_get.2 j.val j.isLt) (rho_tab hg) (fun i hi => (hp i hi).1)
      fun a ha b hb e => ?_
    rw [← (hp a ha).2.2.1, ← (hp b hb).2.2.1, e]
  have hJ : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)
  calc Nat.card (Subgroup.closure (Set.range fun j : Fin 6 => permOfArr 245520 jointArrs[j.val]!))
      ≤ Nat.card rho.range := Subgroup.card_le_of_le hle
    _ ≤ Nat.card J := Nat.card_le_card_of_surjective _ rho.rangeRestrict_surjective
    _ = 245520 * 52136 * 36 := by rw [card_J]

end CertificateChecks.KernelSpor.ON4K

end
