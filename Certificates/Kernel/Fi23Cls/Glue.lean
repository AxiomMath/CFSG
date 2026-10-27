module

public import Certificates.Kernel.Fi23Cls.ChkDefs
public import Certificates.Kernel.Fi23Q.WordGlue
public import Certificates.Kernel.Fi23Five.Sound
public import CFSG.Certificates.Kernel.Fi23Cls.Sound
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23Pts
import Certificates.Kernel.Fi23Cls.Scan
import Certificates.Kernel.Fi23Cls.Scan1
import Certificates.Kernel.Fi23Cls.Chk

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi23Cls

open CFSG.Sporadic.Fi23 CFSG.KC.Fi23K CFSG.KD.Fi23K CFSG.KC.Fi23Five
  CFSG.KC.Fi23Cls CFSG.KD.Fi23Cls CertificateChecks.KernelFi23Q CertificateChecks.KernelFi23Five
  CFSG.HardMathSupport.Dickson.I271.TabFi23
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 (t3)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Sylow (eq_of_base)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem cmK_iff {i j : Nat} (hi : i < 31671) (hj : j < 31671) :
    cmK G i j = true ↔ conjPt j * conjPt i = conjPt i * conjPt j := by
  unfold cmK
  rw [← conjPt_acts hi j hj, Nat.beq_eq, CFSG.Sporadic.Fi23.idx_eq_iff hj hj, mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem cls_of {g : CFSG.Sporadic.Fi23.J} {w : List Nat} {p N V : Nat} {L S : List Nat} (hN : N ≠ 31671)
    (hact : ∀ x < 31671, wv G w x = idx 31671 g x) (hfix : fixK G w L = true)
    (hcls : clsK G w p N V L S = true) :
    orderOf g = 3 ∧ ∃ q : Fin 31671, g • q = q ∧ Nat.card {r : Fin 31671 // g • r = r} = N ∧
      Nat.card {r : Fin 31671 // r ≠ q ∧
        conjPt r.val * conjPt q.val = conjPt q.val * conjPt r.val ∧ g • r = r} = V ∧
      ∀ r : Fin 31671, g • r = r → ∃ h ∈ Subgroup.centralizer ({g} : Set CFSG.Sporadic.Fi23.J), h • q = r := by
  obtain ⟨h3, hp, hpf, hlen, hval, hdiam⟩ := clsK_spec hcls
  have hL := fixK_spec hfix
  have hfx : ∀ r : Fin 31671, Nat.beq (wv G w r.val) r.val = true ↔ g • r = r := by
    intro r
    rw [Nat.beq_eq, hact r.val r.2, idx_of_lt g r.2]
    exact Fin.ext_iff.symm
  have hmem : ∀ r : Fin 31671, r.val ∈ L ↔ g • r = r := by
    intro r
    rw [← hfx r, ← hL, List.mem_filter, List.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨r.2, h⟩⟩
  have hcard : Nat.card {r : Fin 31671 // g • r = r} = L.length := by
    rw [← hL, ← List.countP_eq_length_filter, ← card_fin_subtype_eq_countP']
    exact Nat.card_congr (Equiv.subtypeEquivRight fun r => (hfx r).symm)
  obtain ⟨q, rfl⟩ : ∃ q : Fin 31671, q.val = p := ⟨⟨p, hp⟩, rfl⟩
  have hq : g • q = q := (hfx q).1 (by rw [Nat.beq_eq]; exact hpf)
  have hlt : ∀ y < 31671, wv G w y < 31671 := fun y hy => by
    rw [hact y hy]
    exact idx_lt g hy
  refine ⟨?_, q, hq, by rw [hcard, hlen], ?_, ?_⟩
  · have hg3 : g ^ 3 = 1 := eq_of_base fun t ht => by
      have ht' : t < 31671 := by omega
      rw [pow_three, idx_mul, idx_mul, idx_one, ← hact t ht', ← hact _ (hlt t ht'),
        ← hact _ (hlt _ (hlt t ht'))]
      exact h3 t ht
    have hg1 : g ≠ 1 := by
      rintro rfl
      apply hN
      rw [← hlen, ← hcard]
      rw [Nat.card_congr (Equiv.subtypeUnivEquiv (fun r => one_smul CFSG.Sporadic.Fi23.J r)), Nat.card_eq_fintype_card,
        Fintype.card_fin]
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hg3 hg1
  · rw [← hval, ← hL, List.countP_filter, ← card_fin_subtype_eq_countP']
    refine Nat.card_congr (Equiv.subtypeEquivRight fun r => ?_)
    beta_reduce
    rw [Bool.and_eq_true, valF_iff, cmK_iff hp r.2, hfx r]
    constructor
    · rintro ⟨h1, h2, h4⟩
      exact ⟨⟨fun h => h1 (Fin.ext h), h2⟩, h4⟩
    · rintro ⟨⟨h1, h2⟩, h4⟩
      exact ⟨fun h => h1 (Fin.ext_iff.1 h), h2, h4⟩
  · intro r hr
    have hncm : ∀ {i j : Nat} (hi : i < 31671) (hj : j < 31671), cmK G i j = false →
        conjPt i * conjPt j ≠ conjPt j * conjPt i := by
      intro i j hi hj h e
      rw [(cmK_iff hi hj).2 e.symm] at h
      cases h
    rcases hdiam r.val ((hmem r).2 hr) with h1 | h1 | ⟨s, hs, hsf, hs1, hs2⟩
    · exact ⟨1, one_mem _, by rw [one_smul]; exact (Fin.ext h1).symm⟩
    · exact exists_cent_smul_of_noncomm hq hr (hncm hp r.2 h1)
    · let sF : Fin 31671 := ⟨s, hs⟩
      have hsx : g • sF = sF := (hfx sF).1 (by rw [Nat.beq_eq]; exact hsf)
      obtain ⟨g1, hg1, hg1p⟩ := exists_cent_smul_of_noncomm hq hsx (hncm hp hs hs1)
      obtain ⟨g2, hg2, hg2p⟩ := exists_cent_smul_of_noncomm hsx hr (hncm hs r.2 hs2)
      exact ⟨g2 * g1, Subgroup.mul_mem _ hg2 hg1, by rw [mul_smul, hg1p, hg2p]⟩

theorem w0_eq : CFSG.KD.Fi23Q.t3R 0 = w0 := by decide
theorem w1_eq : CFSG.KD.Fi23Q.t3R 1 = w1 := by decide
theorem w2_eq : CFSG.KD.Fi23Q.t3R 2 = w2 := by decide
theorem w3_eq : CFSG.KD.Fi23Q.t3R 3 = w3 := by decide

theorem act_t3 {c : Nat} (hc : c < 4) {w : List Nat} (hw : CFSG.KD.Fi23Q.t3R c = w) :
    ∀ x < 31671, wv G w x = idx 31671 (t3 ⟨c, hc⟩) x := by
  intro x hx
  rw [← hw, wvG_eq _ (t3R_ok hc) x hx, t3R_prod hc]

open Certificates in
open CFSG.Sporadic.Fi23 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 in
theorem classFacts : 
    (orderOf (t3 0) = 3 ∧ ∃ p : Fin 31671, t3 0 • p = p ∧
      Nat.card {r : Fin 31671 // t3 0 • r = r} = 351 ∧
      Nat.card {r : Fin 31671 // r ≠ p ∧
        conjPt r.val * conjPt p.val = conjPt p.val * conjPt r.val ∧ t3 0 • r = r} = 126 ∧
      ∀ r : Fin 31671, t3 0 • r = r →
        ∃ g ∈ Subgroup.centralizer ({t3 0} : Set CFSG.Sporadic.Fi23.J), g • p = r) ∧
    (orderOf (t3 1) = 3 ∧ ∃ p : Fin 31671, t3 1 • p = p ∧
      Nat.card {r : Fin 31671 // t3 1 • r = r} = 324 ∧
      Nat.card {r : Fin 31671 // r ≠ p ∧
        conjPt r.val * conjPt p.val = conjPt p.val * conjPt r.val ∧ t3 1 • r = r} = 27 ∧
      ∀ r : Fin 31671, t3 1 • r = r →
        ∃ g ∈ Subgroup.centralizer ({t3 1} : Set CFSG.Sporadic.Fi23.J), g • p = r) ∧
    (orderOf (t3 2) = 3 ∧ ∃ p : Fin 31671, t3 2 • p = p ∧
      Nat.card {r : Fin 31671 // t3 2 • r = r} = 135 ∧
      Nat.card {r : Fin 31671 // r ≠ p ∧
        conjPt r.val * conjPt p.val = conjPt p.val * conjPt r.val ∧ t3 2 • r = r} = 36 ∧
      ∀ r : Fin 31671, t3 2 • r = r →
        ∃ g ∈ Subgroup.centralizer ({t3 2} : Set CFSG.Sporadic.Fi23.J), g • p = r) ∧
    (orderOf (t3 3) = 3 ∧ ∃ p : Fin 31671, t3 3 • p = p ∧
      Nat.card {r : Fin 31671 // t3 3 • r = r} = 27 ∧
      Nat.card {r : Fin 31671 // r ≠ p ∧
        conjPt r.val * conjPt p.val = conjPt p.val * conjPt r.val ∧ t3 3 • r = r} = 0 ∧
      ∀ r : Fin 31671, t3 3 • r = r →
        ∃ g ∈ Subgroup.centralizer ({t3 3} : Set CFSG.Sporadic.Fi23.J), g • p = r) := by
  exact ⟨cls_of (by norm_num) (act_t3 (c := 0) (by norm_num) w0_eq) ch17338scan0_ok ch17338cls0_ok,
    cls_of (by norm_num) (act_t3 (c := 1) (by norm_num) w1_eq) ch17338scan1_ok ch17338cls1_ok,
    cls_of (by norm_num) (act_t3 (c := 2) (by norm_num) w2_eq) ch17338scan2_ok ch17338cls2_ok,
    cls_of (by norm_num) (act_t3 (c := 3) (by norm_num) w3_eq) ch17338scan3_ok ch17338cls3_ok⟩

end CertificateChecks.KernelFi23Cls

end
