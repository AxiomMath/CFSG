
module

public import Certificates.Kernel.Fi23Tw.Facts
public import Certificates.Kernel.Fi23Y322.Glue
import Certificates.Kernel.Fi23Tw.Twin

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Tw

open CFSG.Sporadic.Fi23 CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KD.Fi23K
  CFSG.KC.Fi23R CFSG.KC.Fi23Five CFSG.KC.Fi23Tw CFSG.KD.Fi23Tw CFSG.KD.Fi23Cls
  CertificateChecks.KernelFi23Q CertificateChecks.KernelFi23Cls CertificateChecks.KernelFi23Y322
  CFSG.HardMathSupport.Dickson.I271.TabFi23 CFSG.KS.Raw.Orb
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 (t3)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem TR_lt : ∀ T ∈ CFSG.KD.Fi23Tw.TR, T.getD 0 0 < 31671 ∧ T.getD 1 0 < 31671 ∧ T.getD 2 0 < 31671 := by
  decide

theorem e_inv {k : ℕ} (hk : k < 31671) : (conjPt k)⁻¹ = conjPt k := by
  have h := conjPt_sq hk
  rw [pow_two] at h
  exact inv_eq_of_mul_eq_one_right h

theorem e_conj {a b : ℕ} (ha : a < 31671) (hb : b < 31671) :
    conjPt (tA G a b) = conjPt a * conjPt b * conjPt a := by
  have h := conjPt_smul (conjPt a) ⟨b, hb⟩
  have hv : (conjPt a • (⟨b, hb⟩ : Fin 31671)).val = tA G a b := by
    rw [← conjPt_acts ha b hb, idx_of_lt _ hb]
  rw [hv, e_inv ha] at h
  exact h

@[expose] noncomputable def zT (T : List ℕ) : CFSG.Sporadic.Fi23.J := conjPt (T.getD 0 0) * conjPt (T.getD 1 0)

theorem rot_prod {T : List ℕ} (hT : T ∈ CFSG.KD.Fi23Tw.TR) :
    conjPt (T.getD 1 0) * conjPt (T.getD 2 0) = zT T ∧
      conjPt (T.getD 2 0) * conjPt (T.getD 0 0) = zT T := by
  obtain ⟨hx, hy, hz⟩ := TR_lt T hT
  obtain ⟨h1, h2, h3, h4⟩ := trK_spec (allLL_spec (ch17340tri_ok : tri = true) T hT)
  set x := T.getD 0 0
  set y := T.getD 1 0
  set z := T.getD 2 0
  have ex := e_inv hx
  have ey := e_inv hy
  have hzx : conjPt z = conjPt x * conjPt y * conjPt x := by rw [← h1, e_conj hx hy]
  have hcube : (conjPt x * conjPt y) ^ 3 = 1 := by
    have := prod_eq_one (u := [x, y, x, y, x, y]) (by simp [hx, hy]) h4
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
    rw [pow_three]
    simpa [mul_assoc] using this
  have hxx : conjPt x * conjPt x = 1 := by rw [← pow_two]; exact conjPt_sq hx
  have hyy : conjPt y * conjPt y = 1 := by rw [← pow_two]; exact conjPt_sq hy
  have hinv : (zT T)⁻¹ = conjPt y * conjPt x := by
    unfold zT
    rw [mul_inv_rev, ex, ey]
  have hyz : conjPt y * conjPt z = zT T := by
    rw [hzx]
    unfold zT
    have e3 : conjPt x * conjPt y * (conjPt x * conjPt y) * (conjPt x * conjPt y) = 1 := by
      rw [← hcube, pow_three]
      group
    calc conjPt y * (conjPt x * conjPt y * conjPt x)
        = (conjPt x * conjPt x) * (conjPt y * (conjPt x * conjPt y * conjPt x)) *
            ((conjPt y * conjPt y)) := by rw [hxx, hyy]; group
      _ = conjPt x * (conjPt x * conjPt y * (conjPt x * conjPt y) * (conjPt x * conjPt y)) *
            conjPt y := by group
      _ = conjPt x * conjPt y := by rw [e3]; group
  have hzx' : conjPt z * conjPt x = zT T := by
    rw [hzx]
    unfold zT
    calc conjPt x * conjPt y * conjPt x * conjPt x = conjPt x * conjPt y * (conjPt x * conjPt x) := by
          group
      _ = conjPt x * conjPt y := by rw [hxx]; group
  exact ⟨hyz, hzx'⟩

theorem zT_inv {T : List ℕ} (hT : T ∈ CFSG.KD.Fi23Tw.TR) : (zT T)⁻¹ = zT T * zT T := by
  obtain ⟨hx, hy, -⟩ := TR_lt T hT
  obtain ⟨-, -, -, h4⟩ := trK_spec (allLL_spec (ch17340tri_ok : tri = true) T hT)
  have := prod_eq_one (u := [T.getD 0 0, T.getD 1 0, T.getD 0 0, T.getD 1 0, T.getD 0 0,
    T.getD 1 0]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with h | h | h | h | h | h <;> rw [h] <;> assumption) h4
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
  apply inv_eq_of_mul_eq_one_right
  unfold zT
  simpa [mul_assoc] using this

theorem pair_prod {T : List ℕ} (hT : T ∈ CFSG.KD.Fi23Tw.TR) {a b : ℕ} (h : pairIn T a b = true) :
    conjPt a * conjPt b = zT T ∨ conjPt a * conjPt b = (zT T)⁻¹ := by
  obtain ⟨hx, hy, hz⟩ := TR_lt T hT
  obtain ⟨hyz, hzx'⟩ := rot_prod hT
  have hinv : (zT T)⁻¹ = conjPt (T.getD 1 0) * conjPt (T.getD 0 0) := by
    unfold zT
    rw [mul_inv_rev, e_inv hx, e_inv hy]
  rcases pairIn_spec h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl hyz
  · exact Or.inl hzx'
  · exact Or.inr hinv.symm
  · right
    rw [← hyz, mul_inv_rev, e_inv hy, e_inv hz]
  · right
    rw [← hzx', mul_inv_rev, e_inv hx, e_inv hz]

theorem zT_comm {T T' : List ℕ} (hT : T ∈ CFSG.KD.Fi23Tw.TR) (hT' : T' ∈ CFSG.KD.Fi23Tw.TR) (h : cmTr G T T' = true) :
    zT T' * zT T = zT T * zT T' := by
  obtain ⟨hx, hy, hz⟩ := TR_lt T hT
  obtain ⟨hx', hy', -⟩ := TR_lt T' hT'
  have hg : ∀ m < 31671, conjPt (tA G (T'.getD 0 0) (tA G (T'.getD 1 0) m)) =
      zT T' * conjPt m * (zT T')⁻¹ := by
    intro m hm
    rw [e_conj hx' (CertificateChecks.KernelFi23R.tA_lt _ hm), e_conj hy' hm]
    unfold zT
    rw [mul_inv_rev, e_inv hx', e_inv hy']
    group
  have hrot : zT T' * zT T * (zT T')⁻¹ = zT T := by
    have e1 : zT T' * zT T * (zT T')⁻¹ =
        (zT T' * conjPt (T.getD 0 0) * (zT T')⁻¹) * (zT T' * conjPt (T.getD 1 0) * (zT T')⁻¹) := by
      unfold zT
      group
    rw [e1, ← hg _ hx, ← hg _ hy]
    obtain ⟨hyz, hzx⟩ := rot_prod hT
    rcases cmTr_spec h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      rfl
    · rw [h1, h2, hyz]
    · rw [h1, h2, hzx]
  calc zT T' * zT T = zT T' * zT T * (zT T')⁻¹ * zT T' := by group
    _ = zT T * zT T' := by rw [hrot]

theorem pw_or {α : Type} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R →
    ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b ∨ R b a
  | [], _, p1, hp1, _, _, _ => absurd hp1 List.not_mem_nil
  | q :: l, h, p1, hp1, p2, hp2, hne => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 hp1 with e1 | hm1
    · rcases List.mem_cons.1 hp2 with e2 | hm2
      · exact absurd (e1.trans e2.symm) hne
      · rw [e1]
        exact Or.inl (h.1 p2 hm2)
    · rcases List.mem_cons.1 hp2 with e2 | hm2
      · rw [e2]
        exact Or.inr (h.1 p1 hm1)
      · exact pw_or h.2 p1 hm1 p2 hm2 hne

theorem zT_commute : ∀ T ∈ CFSG.KD.Fi23Tw.TR, ∀ T' ∈ CFSG.KD.Fi23Tw.TR, Commute (zT T) (zT T') := by
  have hp := cmAll_spec (ch17340trCm_ok : trCm = true)
  intro T hT T' hT'
  by_cases e : T = T'
  · rw [e]
  · rcases pw_or hp T hT T' hT' e with h | h
    · exact (zT_comm hT hT' h).symm
    · exact zT_comm hT' hT h

theorem twin_zT {a b : Fin 31671} (h : Twin ePt (t3 2) a b) :
    ∃ T ∈ CFSG.KD.Fi23Tw.TR, ePt a * ePt b = zT T ∨ ePt a * ePt b = (zT T)⁻¹ := by
  obtain ⟨e, he, -, -, ha, hb⟩ := twin_pe h
  have h1 := allL_spec (ch17340pe_ok : pe = true) e he
  rw [bAnd_eq, Bool.and_eq_true] at h1
  obtain ⟨T, hT, hp⟩ := inTr_spec h1.2
  refine ⟨T, hT, ?_⟩
  have e1 : ePt a * ePt b = conjPt (L2.getD (e % 32768 / 135) 0) *
      conjPt (L2.getD (e % 32768 % 135) 0) := by
    unfold ePt
    rw [ha, hb]
  rw [e1]
  exact pair_prod hT hp

theorem hK3 : ∀ a b a' b', Twin ePt (t3 2) a b → Twin ePt (t3 2) a' b' →
    ePt a * ePt b * (ePt a' * ePt b') = ePt a' * ePt b' * (ePt a * ePt b) := by
  intro a b a' b' h h'
  obtain ⟨T, hT, hP⟩ := twin_zT h
  obtain ⟨T', hT', hP'⟩ := twin_zT h'
  have hc : zT T * zT T' = zT T' * zT T := zT_commute T hT T' hT'
  have hsq : ∀ {u v : CFSG.Sporadic.Fi23.J}, u * v = v * u → u * u * v = v * (u * u) := fun h => by
    rw [mul_assoc, h, ← mul_assoc, h, mul_assoc]
  have h1 := hsq hc
  have h2 := hsq hc.symm
  have h3 := hsq h1.symm
  rcases hP with hP | hP <;> rcases hP' with hP' | hP' <;>
    rw [hP, hP'] <;> (try rw [zT_inv hT]) <;> (try rw [zT_inv hT'])
  · exact hc
  · exact h2.symm
  · exact h1
  · exact h3.symm

end CertificateChecks.KernelFi23Tw

end
