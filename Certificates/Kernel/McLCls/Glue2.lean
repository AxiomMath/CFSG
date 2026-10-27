module

public import Certificates.Kernel.McLCls.Glue1
public import Certificates.Kernel.McLCls.Cls

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelMcLCls

open Subgroup CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.M305
  CertificateChecks.KernelLC.McLC CFSG.Sporadic.Th CFSG.Sporadic.SmallOddCore CFSG.Quasithin.KGC31
  CFSG.SectionRank.QTK.Insp443.McLCls CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore.Native CFSG.KS.MulH

theorem comm_iff {P Q : Nat} {g h : Equiv.Perm (Fin 275)} (hP : PRep 275 9 P g)
    (hQ : PRep 275 9 Q h) : m305comm P Q = true ↔ g * h = h * g := by
  unfold m305comm
  rw [CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · intro H
    ext x
    have e := Nat.eq_of_beq_eq_true (H x x.2)
    rw [hQ x, hP (h x), hP x, hQ (g x)] at e
    exact e
  · intro H i hi
    have e := congrArg (fun f : Equiv.Perm (Fin 275) => (f ⟨i, hi⟩ : ℕ)) H
    simp only [Equiv.Perm.mul_apply] at e
    have e1 := hQ ⟨i, hi⟩
    have e2 := hP ⟨i, hi⟩
    simp only at e1 e2
    rw [e1, e2, hP (h ⟨i, hi⟩), hQ (g ⟨i, hi⟩), e]
    exact Nat.beq_refl _

theorem sq_iff {P : Nat} {g : Equiv.Perm (Fin 275)} (cP : canonK 275 9 (mask 9) (275 * 9) P = true)
    (hP : PRep 275 9 P g) : m305sq P = true ↔ g * g = 1 := by
  unfold m305sq
  constructor
  · intro e
    exact eq_of_beq (prep_mul hP hP) prep_one e
  · intro e
    have h1 : m305mul P P = m305id :=
      CFSG.ClassicalInvolution.ListBridge.eq_of_prep (canon_mul cP cP) canon_one
        (prep_mul hP hP) (e ▸ prep_one)
    rw [h1]
    exact Nat.beq_refl _

theorem cnt_eq (f : Nat → Bool) : ∀ N : Nat,
    m305cnt N f = ((Finset.range N).filter fun j => f j = true).card
  | 0 => rfl
  | N + 1 => by
    change Bool.rec (motive := fun _ => Nat) (m305cnt N f) (Nat.succ (m305cnt N f)) (f N) = _
    rw [Finset.range_add_one, Finset.filter_insert]
    cases h : f N
    · simp only [Bool.false_eq_true, if_false]
      exact cnt_eq f N
    · rw [if_pos rfl, Finset.card_insert_of_notMem (by simp), ← cnt_eq f N]


theorem sE_gens : ∀ k < SE.ng, PRep 275 9 (SE.G k) (sP.getD k 1) := by
  intro k hk
  have hk3 : k < 3 := hk
  interval_cases k
  · have e : SE.G 0 = CT.F 6 := by decide +kernel
    rw [e]
    exact prep_cls (k := 6) (by norm_num)
  · have e : SE.G 1 = CT.F 7 := by decide +kernel
    rw [e]
    exact prep_cls (k := 7) (by norm_num)
  · have e : SE.G 2 = CT.F 8 := by decide +kernel
    rw [e]
    exact prep_cls (k := 8) (by norm_num)

theorem mem_S_iff (g : Equiv.Perm (Fin 275)) : g ∈ F.S ↔ ∃ i < SE.N, PRep 275 9 (SE.T i) g := by
  rw [S_eq]
  exact (CFSG.ClassicalInvolution.ListBridge.enum_closure SE.ok rfl sE_gens).1 g

theorem canon_SE : ∀ i < SE.N, canonK 275 9 (mask 9) (275 * 9) (SE.T i) = true :=
  CFSG.KC.BfsPin.bfsK_canon SE.ok

theorem W_mem_of_prod (c : Nat) : eElt F.v (bitVec 4 c) ∈ F.W := by
  unfold eElt
  refine F.W.list_prod_mem fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact F.W.pow_mem (subset_closure ⟨i, rfl⟩) _

theorem prep_prod4 (c : Nat) : PRep 275 9 (m305prod bs c) (eElt F.v (bitVec 4 c)) := by
  rw [v_eq]
  exact prep_prod bs_vs c

theorem prep_rK : PRep 275 9 rK F.r :=
  prep_mul (prep_cls (k := 3) (by norm_num)) prep_cen0

theorem cls_fact : ∀ x ∈ F.S, x * x = 1 → x ∈ F.W ∨
    x ∈ F.W.map (MulAut.conj F.r).toMonoidHom ∨
    Nat.card ↥{g : Equiv.Perm (Fin 275) | g ∈ F.S ∧ g * g = 1 ∧ g * x = x * g} < 16 := by
  intro x hx hx2
  obtain ⟨i, hi, hxi⟩ := (mem_S_iff x).1 hx
  have hc := cls
  unfold m305cls at hc
  have hc := CFSG.KS.Raw.Orb.allN_iff.1 hc i hi
  rcases bif_iff.1 hc with ⟨-, hA⟩ | ⟨-, hc⟩
  · exfalso
    rcases bif_iff.1 hA with ⟨h1, h2⟩ | ⟨h1, -⟩
    · exact Bool.false_ne_true h2
    · rw [(sq_iff (canon_SE i hi) hxi).2 hx2] at h1
      exact Bool.noConfusion h1
  rcases bif_iff.1 hc with ⟨-, hB⟩ | ⟨-, hc⟩
  · left
    rw [eq_of_beq hxi (prep_prod4 (Nat.sub (pg 6 (mask 6) sCodes i) 1)) hB]
    exact W_mem_of_prod _
  rcases bif_iff.1 hc with ⟨-, hC⟩ | ⟨-, hD⟩
  · right
    left
    have e := eq_of_beq (prep_mul hxi prep_rK)
      (prep_mul prep_rK (prep_prod4 (Nat.sub (pg 6 (mask 6) sCodes i) 17))) hC
    refine ⟨_, W_mem_of_prod (Nat.sub (pg 6 (mask 6) sCodes i) 17), ?_⟩
    change F.r * _ * F.r⁻¹ = x
    rw [← e, mul_inv_cancel_right]
  right
  right
  obtain ⟨-, hD⟩ := band.1 hD
  have hlt := Nat.blt_eq.mp hD
  rw [cnt_eq] at hlt
  refine lt_of_le_of_lt ?_ hlt
  classical
  have hsel : ∀ g ∈ {g : Equiv.Perm (Fin 275) | g ∈ F.S ∧ g * g = 1 ∧ g * x = x * g},
      ∃ j < SE.N, PRep 275 9 (SE.T j) g := fun g hg => (mem_S_iff g).1 hg.1
  let f : ↥{g : Equiv.Perm (Fin 275) | g ∈ F.S ∧ g * g = 1 ∧ g * x = x * g} →
      ↥((Finset.range SE.N).filter fun j => bAnd(m305sq (SE.T j), m305comm (SE.T j) (SE.T i)) =
        true) := fun g => ⟨Classical.choose (hsel g.1 g.2), by
      obtain ⟨hj, hp⟩ := Classical.choose_spec (hsel g.1 g.2)
      rw [Finset.mem_filter, Finset.mem_range, band]
      exact ⟨hj, (sq_iff (canon_SE _ hj) hp).2 g.2.2.1, (comm_iff hp hxi).2 g.2.2.2⟩⟩
  have hf : Function.Injective f := by
    intro a b e
    have e' : Classical.choose (hsel a.1 a.2) = Classical.choose (hsel b.1 b.2) :=
      congrArg Subtype.val e
    have ha := (Classical.choose_spec (hsel a.1 a.2)).2
    have hb := (Classical.choose_spec (hsel b.1 b.2)).2
    rw [e'] at ha
    exact Subtype.ext (prep_eq ha hb)
  have := Nat.card_le_card_of_injective f hf
  exact this.trans (Nat.card_eq_finsetCard _).le

end CertificateChecks.KernelMcLCls

end
