
module

public import Certificates.Kernel.Sporadic.Fi24Fix.Group
import Certificates.Kernel.Sporadic.Fi24Fix.Orbit
import Certificates.Kernel.Sporadic.Fi24Fix.Rank0
import Certificates.Kernel.Sporadic.Fi24Fix.Rank1
import Certificates.Kernel.Sporadic.Fi24Fix.Rank2
import Certificates.Kernel.Sporadic.Fi24Fix.Rank3
import Certificates.Kernel.Sporadic.Fi24Fix.Rank4
import Certificates.Kernel.Sporadic.Fi24Fix.Rank5
import Certificates.Kernel.Sporadic.Fi24Fix.Rank6
import Certificates.Kernel.Sporadic.Fi24Fix.Rank7
public import Certificates.Kernel.Sporadic.Fi24Fix.Mats

public section

namespace CertificateChecks.KernelFi24Fix

open CertificateChecks.KernelFi24 CertificateChecks.KernelCo2 TauCeti TauCeti.Sporadic
  CFSG.Sporadic.Bridge CFSG.KC.Fi24FixC CFSG.KC.Fi24FixS CFSG.KC.Fi24FixK CFSG.KD.Fi24Fix
  CFSG.KS.Mat3

theorem S_facts : (∀ i < 31671, 1 ≤ S i ∧ S i < 306936) ∧
    ∀ i j, i < j → j < 31671 → S i < S j := by
  have h := orbit_asc
  unfold CFSG.KC.Fi24Fix.ascOK at h
  obtain ⟨h1, h2⟩ := andB_true3 h
  obtain ⟨h3, h4⟩ := andB_true3 h2
  have hinc := allBelow_spec h4 (by decide)
  have hstep : ∀ i, i + 1 < 31671 → S i < S (i + 1) := by
    intro i hi
    have := hinc i (by change i < 31671 - 1; omega)
    rwa [Nat.blt_eq] at this
  have hmono : ∀ d i, i + d + 1 < 31671 → S i < S (i + d + 1) := by
    intro d
    induction d with
    | zero => exact fun i hi => hstep i hi
    | succ d ih => exact fun i hi => lt_trans (ih i (by omega)) (hstep _ (by omega))
  have hlo : 1 ≤ S 0 := Nat.le_of_ble_eq_true h1
  have hhi : S 31670 < 306936 := by
    exact Nat.blt_eq.mp h3
  have hlt : ∀ i j, i < j → j < 31671 → S i < S j := by
    intro i j hij hj
    have := hmono (j - i - 1) i (by omega)
    rwa [show i + (j - i - 1) + 1 = j by omega] at this
  refine ⟨fun i hi => ⟨?_, ?_⟩, hlt⟩
  · rcases Nat.eq_zero_or_pos i with rfl | h0
    · exact hlo
    · exact le_trans hlo (le_of_lt (hlt 0 i h0 hi))
  · rcases Nat.lt_or_ge i 31670 with h0 | h0
    · exact lt_trans (hlt i 31670 h0 (by norm_num)) hhi
    · rw [show i = 31670 by omega]
      exact hhi

theorem S_inj {i j : ℕ} (hi : i < 31671) (hj : j < 31671) (h : S i = S j) : i = j := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hl | hl
  · exact absurd h (Nat.ne_of_lt (S_facts.2 i j hl hj))
  · exact absurd h (Nat.ne_of_gt (S_facts.2 j i hl hi))

theorem clos_all : ∀ i < 31671, ∀ g < 9, IX (9 * i + g) < 31671 ∧
    S (IX (9 * i + g)) = TG (hgen g) (TG 0 (S i)) := by
  have key : ∀ {lo m hi : ℕ}, closOK S IX TG 31671 lo m hi = true → m ≤ 64 * hi →
      ∀ i, lo ≤ i → i < lo + m → ∀ g < 9, IX (9 * i + g) < 31671 ∧
        S (IX (9 * i + g)) = TG (hgen g) (TG 0 (S i)) := by
    intro lo m hi h hm i h1 h2 g hg
    have := closOK_spec h hm (i - lo) (by omega) g hg
    rwa [Nat.add_sub_cancel' h1] at this
  have c0 : closOK S IX TG 31671 0 4096 64 = true := clos0
  have c1 : closOK S IX TG 31671 4096 4096 64 = true := clos1
  have c2 : closOK S IX TG 31671 8192 4096 64 = true := clos2
  have c3 : closOK S IX TG 31671 12288 4096 64 = true := clos3
  have c4 : closOK S IX TG 31671 16384 4096 64 = true := clos4
  have c5 : closOK S IX TG 31671 20480 4096 64 = true := clos5
  have c6 : closOK S IX TG 31671 24576 4096 64 = true := clos6
  have c7 : closOK S IX TG 31671 28672 2999 47 = true := clos7
  intro i hi
  by_cases h0 : i < 4096
  · exact key c0 (by norm_num) i (by omega) (by omega)
  by_cases h1 : i < 8192
  · exact key c1 (by norm_num) i (by omega) (by omega)
  by_cases h2 : i < 12288
  · exact key c2 (by norm_num) i (by omega) (by omega)
  by_cases h3 : i < 16384
  · exact key c3 (by norm_num) i (by omega) (by omega)
  by_cases h4 : i < 20480
  · exact key c4 (by norm_num) i (by omega) (by omega)
  by_cases h5 : i < 24576
  · exact key c5 (by norm_num) i (by omega) (by omega)
  by_cases h6 : i < 28672
  · exact key c6 (by norm_num) i (by omega) (by omega)
  · exact key c7 (by norm_num) i (by omega) (by omega)

@[expose] noncomputable def fixCnt (lo m : ℕ) : ℕ :=
  ((Finset.range m).filter fun t =>
    walk TG AW (walk TG PW (S (lo + t))) = walk TG PW (S (lo + t))).card

theorem fixCnt_split (lo a b n lo' : ℕ) (hn : a + b = n) (hlo : lo + a = lo') :
    fixCnt lo n = fixCnt lo a + fixCnt lo' b := by
  subst hn hlo
  unfold fixCnt
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.sum_range_add]
  simp only [Nat.add_assoc]

theorem fixCnt_eq {lo m hi c : ℕ} (hm : m ≤ 64 * hi)
    (h : Nat.beq (cntFix S TG PW AW lo m hi) c = true) : fixCnt lo m = c := by
  rw [← Nat.eq_of_beq_eq_true h, cntFix_eq _ _ _ _ _ _ _ hm]
  rfl

theorem cnt_all : ((Finset.range 31671).filter fun t =>
    walk TG AW (walk TG PW (S t)) = walk TG PW (S t)).card = 360 := by
  have e : ((Finset.range 31671).filter fun t =>
      walk TG AW (walk TG PW (S t)) = walk TG PW (S t)).card = fixCnt 0 31671 := by
    unfold fixCnt
    simp only [Nat.zero_add]
  rw [e, fixCnt_split 0 4096 27575 31671 4096 rfl rfl,
    fixCnt_split 4096 4096 23479 27575 8192 rfl rfl,
    fixCnt_split 8192 4096 19383 23479 12288 rfl rfl,
    fixCnt_split 12288 4096 15287 19383 16384 rfl rfl,
    fixCnt_split 16384 4096 11191 15287 20480 rfl rfl,
    fixCnt_split 20480 4096 7095 11191 24576 rfl rfl,
    fixCnt_split 24576 4096 2999 7095 28672 rfl rfl,
    fixCnt_eq (by norm_num) cnt0, fixCnt_eq (by norm_num) cnt1, fixCnt_eq (by norm_num) cnt2,
    fixCnt_eq (by norm_num) cnt3, fixCnt_eq (by norm_num) cnt4, fixCnt_eq (by norm_num) cnt5,
    fixCnt_eq (by norm_num) cnt6, fixCnt_eq (by norm_num) cnt7]

theorem wordProd_congr {G : Type*} [Group G] {x y : ℕ → G} :
    ∀ w : List (ℕ × Bool), (∀ l ∈ w, x l.1 = y l.1) → wordProd x w = wordProd y w
  | [], _ => rfl
  | l :: w, h => by
    simp only [wordProd, List.map_cons, List.prod_cons] at *
    rw [h l List.mem_cons_self]
    have := wordProd_congr w (fun l' hl' => h l' (List.mem_cons_of_mem l hl'))
    simp only [wordProd] at this
    rw [this]

noncomputable abbrev pE : E := fi24PrimeGroupMulEquivCommutator (wordProd (presGen fi24PrimePresentation) pv)

noncomputable abbrev eA : E := fi24PrimeGroupMulEquivCommutator
  (presGen fi24PrimePresentation 7 * presGen fi24PrimePresentation 10)

theorem coe_iso_wordProd (w : List (ℕ × Bool)) (hw : ∀ l ∈ w, l.1 < 11) :
    ((fi24PrimeGroupMulEquivCommutator (wordProd (presGen fi24PrimePresentation) w) : E) :
      Fi24AutomorphismGroup) = wordProd (fun k => g0 0 * g0 (k + 1)) w := by
  have h := map_wordProd (E.subtype.comp fi24PrimeGroupMulEquivCommutator.toMonoidHom)
    (presGen fi24PrimePresentation) w
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype] at h
  rw [h]
  exact wordProd_congr w fun l hl => iso_presGen (hw l hl)

theorem pE_eq : (pE : Fi24AutomorphismGroup) = (PW.map g0).prod := by
  rw [coe_iso_wordProd pv pv_lt]
  simp only [wordProd, pv, PW, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_inv_rev, g0_inv, if_true, if_false, Bool.false_eq_true, mul_assoc, g0_mul_self_mul, mul_one,
    Nat.reduceAdd]

theorem eA_inv_eq : ((eA : Fi24AutomorphismGroup))⁻¹ = (AW.map g0).prod := by
  have h7 := iso_presGen (k := 7) (by norm_num)
  have h10 := iso_presGen (k := 10) (by norm_num)
  rw [eA, map_mul, Subgroup.coe_mul, h7, h10]
  simp only [AW, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_inv_rev, g0_inv,
    mul_assoc, mul_one, Nat.reduceAdd]

theorem rel_trans {H : Subgroup Fi24AutomorphismGroup} {u v w : Fi24AutomorphismGroup}
    (h1 : u * v⁻¹ ∈ H) (h2 : v * w⁻¹ ∈ H) : u * w⁻¹ ∈ H := by
  have e : u * w⁻¹ = (u * v⁻¹) * (v * w⁻¹) := by group
  rw [e]
  exact H.mul_mem h1 h2

theorem rel_symm {H : Subgroup Fi24AutomorphismGroup} {u v : Fi24AutomorphismGroup}
    (h : u * v⁻¹ ∈ H) : v * u⁻¹ ∈ H := by
  have e : v * u⁻¹ = (u * v⁻¹)⁻¹ := by group
  rw [e]
  exact H.inv_mem h

theorem rel_mul {H : Subgroup Fi24AutomorphismGroup} {u v : Fi24AutomorphismGroup} (z : Fi24AutomorphismGroup)
    (h : u * v⁻¹ ∈ H) : (u * z) * (v * z)⁻¹ ∈ H := by
  have e : (u * z) * (v * z)⁻¹ = u * v⁻¹ := by group
  rw [e]
  exact h

theorem closY (R : ℕ → Fi24AutomorphismGroup)
    (hT : ∀ g < 12, ∀ i < 306936, TG g i < 306936 ∧ R i * g0 g * (R (TG g i))⁻¹ ∈ H1)
    (hrr : ∀ r r', r < 306936 → r' < 306936 → R r * (R r')⁻¹ ∈ H1 → r = r')
    {m : Fi24AutomorphismGroup} (hm : m ∈ H0) :
    ∀ i < 31671, ∃ i' < 31671, R (S i) * m * (R (S i'))⁻¹ ∈ H1 := by
  have hgen1 : ∀ j < 9, ∀ i < 31671, IX (9 * i + j) < 31671 ∧
      R (S i) * (g0 0 * g0 (hgen j)) * (R (S (IX (9 * i + j))))⁻¹ ∈ H1 := by
    intro j hj i hi
    obtain ⟨hc1, hc2⟩ := clos_all i hi j hj
    have hw := (walk_rel H1 R g0 TG hT [0, hgen j] (by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · norm_num
      · exact hgen_lt hj) (S i) (S_facts.1 i hi).2).2
    rw [walk_cons, walk_cons, walk_nil, ← hc2] at hw
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hw
    exact ⟨hc1, hw⟩
  induction hm using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    intro i hi
    exact ⟨IX (9 * i + j), (hgen1 j hj i hi).1, (hgen1 j hj i hi).2⟩
  | inv_mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    let f : Fin 31671 → Fin 31671 := fun i => ⟨IX (9 * i + j), (hgen1 j hj i i.isLt).1⟩
    have hf : Function.Injective f := by
      intro i1 i2 h12
      have e : IX (9 * i1 + j) = IX (9 * i2 + j) := congrArg Fin.val h12
      have a1 := (hgen1 j hj i1 i1.isLt).2
      have a2 := (hgen1 j hj i2 i2.isLt).2
      rw [e] at a1
      have := hrr _ _ (S_facts.1 i1 i1.isLt).2 (S_facts.1 i2 i2.isLt).2
        (by
          have e2 : R (S i1) * (R (S i2))⁻¹ = (R (S i1) * (g0 0 * g0 (hgen j)) *
              (R (S (IX (9 * i2 + j))))⁻¹) * (R (S i2) * (g0 0 * g0 (hgen j)) *
              (R (S (IX (9 * i2 + j))))⁻¹)⁻¹ := by group
          rw [e2]
          exact H1.mul_mem a1 (H1.inv_mem a2))
      exact Fin.ext (S_inj i1.isLt i2.isLt this)
    have hs := Finite.injective_iff_surjective.1 hf
    intro i hi
    obtain ⟨i0, hi0⟩ := hs ⟨i, hi⟩
    have a0 := (hgen1 j hj i0 i0.isLt).2
    have e : IX (9 * i0 + j) = i := congrArg Fin.val hi0
    rw [e] at a0
    refine ⟨i0, i0.isLt, ?_⟩
    have e2 : R (S i) * (g0 0 * g0 (hgen j))⁻¹ * (R (S i0))⁻¹ =
        (R (S i0) * (g0 0 * g0 (hgen j)) * (R (S i))⁻¹)⁻¹ := by group
    rw [e2]
    exact H1.inv_mem a0
  | one =>
    intro i hi
    exact ⟨i, hi, by rw [mul_one, mul_inv_cancel]; exact H1.one_mem⟩
  | mul x y _ _ hx hy =>
    intro i hi
    obtain ⟨i1, hi1, h1⟩ := hx i hi
    obtain ⟨i2, hi2, h2⟩ := hy i1 hi1
    refine ⟨i2, hi2, ?_⟩
    have e : R (S i) * (x * y) * (R (S i2))⁻¹ =
        (R (S i) * x * (R (S i1))⁻¹) * (R (S i1) * y * (R (S i2))⁻¹) := by group
    rw [e]
    exact H1.mul_mem h1 h2

theorem certificate1017_proof : ∃ Γ : Subgroup (GL (Fin 781) (ZMod 3)),
    (∀ g : GL (Fin 781) (ZMod 3), g.val = CFSG.Sporadic.Fi24.mA ∨ g.val = CFSG.Sporadic.Fi24.mB →
      g ∈ Γ) ∧
    ∀ P : Fin 306936 → Submodule (ZMod 3) (Fin 781 → ZMod 3), Function.Injective P →
      (∀ k, ∃ g ∈ Γ, P k = (CFSG.Sporadic.Fi24.pt 0).sp.map
        (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3)))) →
      ∃ Ψ : Finset (Fin 306936), Ψ.card = 31671 ∧ (∀ k ∈ Ψ, P k ≠ (CFSG.Sporadic.Fi24.pt 0).sp) ∧
        (∀ g ∈ Γ, (CFSG.Sporadic.Fi24.pt 0).sp.map
            (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3))) =
            (CFSG.Sporadic.Fi24.pt 0).sp →
          ∀ k ∈ Ψ, ∃ k' ∈ Ψ,
            (P k).map (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3))) = P k') ∧
        (Ψ.filter fun k => (P k).map (Matrix.mulVecLin CFSG.Sporadic.Fi24.mA) = P k).card = 360 := by
  obtain ⟨x, hx, -, hrel, hcl, hstab, hroot, hA⟩ := matFacts
  obtain ⟨R, hR0, hT, hcov⟩ := rankFacts
  set σ := presHom fi24PrimePresentation x hrel with hσdef
  let σE : E →* GL (Fin 781) (ZMod 3) :=
    σ.comp fi24PrimeGroupMulEquivCommutator.symm.toMonoidHom
  have hσE : ∀ u, σE (fi24PrimeGroupMulEquivCommutator u) = σ u := by
    intro u
    simp [σE]
  have hσgen : ∀ k < 11, σ (presGen fi24PrimePresentation k) = x k := fun k hk =>
    presHom_presGen _ _ _ (by rw [gcount]; exact hk)
  have hst0 : ∀ (h : Fi24AutomorphismGroup), h ∈ H0 → ∀ hh : h ∈ E, σE ⟨h, hh⟩ ∈ stab V0 := by
    intro h hm
    induction hm using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      intro hh
      have hk : hgen j - 1 < 11 := by have := hgen_lt hj; omega
      have hg1 : 1 ≤ hgen j := by
        by_cases h8 : j = 8 <;> simp [hgen, h8]
      have e : (⟨g0 0 * g0 (hgen j), hh⟩ : E) =
          fi24PrimeGroupMulEquivCommutator (presGen fi24PrimePresentation (hgen j - 1)) := by
        apply Subtype.ext
        rw [iso_presGen hk, Nat.sub_add_cancel hg1]
      rw [e, hσE, hσgen _ hk]
      apply hstab
      by_cases h8 : j = 8
      · subst h8
        right
        rfl
      · left
        have : hgen j = j + 1 := by simp [hgen, h8]
        have hj9 : j < 9 := hj
        omega
    | one =>
      intro hh
      have : (⟨1, hh⟩ : E) = 1 := rfl
      rw [this, map_one]
      exact (stab V0).one_mem
    | mul y z hy hz ihy ihz =>
      intro hh
      have : (⟨y * z, hh⟩ : E) = ⟨y, H0_le_E hy⟩ * ⟨z, H0_le_E hz⟩ := rfl
      rw [this, map_mul]
      exact (stab V0).mul_mem (ihy (H0_le_E hy)) (ihz (H0_le_E hz))
    | inv y hy ihy =>
      intro hh
      have : (⟨y⁻¹, hh⟩ : E) = (⟨y, H0_le_E hy⟩ : E)⁻¹ := rfl
      rw [this, map_inv]
      exact (stab V0).inv_mem (ihy (H0_le_E hy))
  have hst : ∀ (h : Fi24AutomorphismGroup) (hh : h ∈ E), h ∈ H1 → σE ⟨h, hh⟩ ∈ stab V0 :=
    fun h hh hH => hst0 h (H1_inf_E hH hh) hh
  set F : Fi24AutomorphismGroup → Submodule (ZMod 3) (Fin 781 → ZMod 3) :=
    subOf E (g0 0) mem_E_or σE V0 with hFdef
  have hF : ∀ u v, u * v⁻¹ ∈ H1 → F u = F v := fun u v huv => subOf_eq_of_rel a_mem_H1 hst huv
  have hact : ∀ q (e : E), act (σE e) (F q) = F (q * e⁻¹) := by
    intro q e
    rw [hFdef, subOf_mul q e⁻¹, map_inv, inv_inv]
  have hσp : σE pE = wordProd x pv := by
    rw [hσE, presHom_wordProd _ _ _ _ (fun l hl => by rw [gcount]; exact pv_lt l hl)]
  have hFp : F pE = (CFSG.Sporadic.Fi24.pt 0).sp := by
    rw [hFdef, subOf_eq_of_mem _ pE.2]
    change act (σE pE)⁻¹ V0 = _
    rw [hσp, ← hroot, act_inv_act]
  refine ⟨σ.range, fun g hg => ?_, fun P hP hPg => ?_⟩
  · have hc := hcl g hg
    refine (Subgroup.closure_le _).2 ?_ hc
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨_, hσgen k hk⟩
  have hΓ : ∀ g ∈ σ.range, ∃ e : E, σE e = g := by
    rintro g ⟨u, rfl⟩
    exact ⟨fi24PrimeGroupMulEquivCommutator u, hσE u⟩
  have hmap : ∀ (g : GL (Fin 781) (ZMod 3)) (W : Submodule (ZMod 3) (Fin 781 → ZMod 3)),
      W.map (Matrix.mulVecLin (g : Matrix (Fin 781) (Fin 781) (ZMod 3))) = act g W := fun _ _ => rfl
  have hPF : ∀ k, ∃ q, P k = F q := by
    intro k
    obtain ⟨g, hg, hk⟩ := hPg k
    obtain ⟨e, rfl⟩ := hΓ g hg
    refine ⟨(pE : Fi24AutomorphismGroup) * (e⁻¹ : E), ?_⟩
    rw [hk, hmap, ← hFp, hact]
  obtain ⟨hinj, hsep, hsurj⟩ := rel_of_eq R hcov F hF P hP hPF
  have hrr : ∀ r r', r < 306936 → r' < 306936 → R r * (R r')⁻¹ ∈ H1 → r = r' := by
    intro r r' hr hr' h
    have := @hinj ⟨r, hr⟩ ⟨r', hr'⟩ (hF _ _ h)
    exact congrArg Fin.val this
  choose kOf hkOf using hsurj
  have hW := walk_rel H1 R g0 TG hT
  have hPW : ∀ g ∈ PW, g < 12 := by decide
  have hAW : ∀ g ∈ AW, g < 12 := by decide
  have hψ : ∀ j < 31671, walk TG PW (S j) < 306936 ∧
      R (S j) * (pE : Fi24AutomorphismGroup) * (R (walk TG PW (S j)))⁻¹ ∈ H1 := by
    intro j hj
    rw [pE_eq]
    exact hW PW hPW (S j) (S_facts.1 j hj).2
  let kψ : ℕ → Fin 306936 := fun j =>
    if h : walk TG PW (S j) < 306936 then kOf ⟨walk TG PW (S j), h⟩ else 0
  have hkψ : ∀ j < 31671, P (kψ j) = F (R (walk TG PW (S j))) := by
    intro j hj
    have h := (hψ j hj).1
    simp only [kψ, dif_pos h]
    exact hkOf _
  have hkinj : Set.InjOn kψ (Finset.range 31671 : Set ℕ) := by
    intro j hj j' hj' h
    simp only [Finset.coe_range, Set.mem_Iio] at hj hj'
    have e1 : F (R (walk TG PW (S j))) = F (R (walk TG PW (S j'))) := by
      rw [← hkψ j hj, ← hkψ j' hj', h]
    have e2 := @hinj ⟨_, (hψ j hj).1⟩ ⟨_, (hψ j' hj').1⟩ e1
    have e3 : walk TG PW (S j) = walk TG PW (S j') := congrArg Fin.val e2
    have a1 := (hψ j hj).2
    have a2 := (hψ j' hj').2
    rw [e3] at a1
    have e4 : R (S j) * (R (S j'))⁻¹ = (R (S j) * (pE : Fi24AutomorphismGroup) *
        (R (walk TG PW (S j')))⁻¹) * (R (S j') * (pE : Fi24AutomorphismGroup) *
        (R (walk TG PW (S j')))⁻¹)⁻¹ := by group
    have := hrr _ _ (S_facts.1 j hj).2 (S_facts.1 j' hj').2
      (by rw [e4]; exact H1.mul_mem a1 (H1.inv_mem a2))
    exact S_inj hj hj' this
  have hPk : ∀ j < 31671, P (kψ j) = F (R (S j) * (pE : Fi24AutomorphismGroup)) := by
    intro j hj
    rw [hkψ j hj]
    exact (hF _ _ (hψ j hj).2).symm
  have hmemΨ : ∀ k ∈ (Finset.range 31671).image kψ, ∃ j < 31671, k = kψ j := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hk
    exact ⟨j, Finset.mem_range.1 hj, rfl⟩
  refine ⟨(Finset.range 31671).image kψ, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hkinj, Finset.card_range]
  · intro k hk h
    obtain ⟨j, hj, rfl⟩ := hmemΨ k hk
    rw [hPk j hj, ← hFp] at h
    have h2 := hsep _ _ h
    have e : R (S j) * (pE : Fi24AutomorphismGroup) * (pE : Fi24AutomorphismGroup)⁻¹ =
        R (S j) * (R 0)⁻¹ := by rw [hR0]; group
    rw [e] at h2
    have := hrr _ _ (S_facts.1 j hj).2 (by norm_num) h2
    have := (S_facts.1 j hj).1
    omega
  · intro g hg hfix k hk
    obtain ⟨e, rfl⟩ := hΓ g hg
    obtain ⟨j, hj, rfl⟩ := hmemΨ k hk
    rw [hmap, ← hFp, hact] at hfix
    have h1 := hsep _ _ hfix
    set m : Fi24AutomorphismGroup :=
      (pE : Fi24AutomorphismGroup) * ((e⁻¹ : E) : Fi24AutomorphismGroup) * (pE : Fi24AutomorphismGroup)⁻¹
    have hmE : m ∈ E := E.mul_mem (E.mul_mem pE.2 (e⁻¹).2) (E.inv_mem pE.2)
    have hm : m ∈ H0 := H1_inf_E h1 hmE
    obtain ⟨i', hi', hr⟩ := closY R hT hrr hm j hj
    refine ⟨kψ i', Finset.mem_image.2 ⟨i', Finset.mem_range.2 hi', rfl⟩, ?_⟩
    rw [hmap, hPk j hj, hact, hPk i' hi']
    apply hF
    have e2 : R (S j) * (pE : Fi24AutomorphismGroup) * ((e⁻¹ : E) : Fi24AutomorphismGroup) *
        (R (S i') * (pE : Fi24AutomorphismGroup))⁻¹ = R (S j) * m * (R (S i'))⁻¹ := by
      simp only [m]
      group
    rw [e2]
    exact hr
  ·
    have hσA : σE eA = x 7 * x 10 := by
      rw [hσE, map_mul, hσgen 7 (by norm_num), hσgen 10 (by norm_num)]
    have hmA : CFSG.Sporadic.Fi24.mA = ((σE eA : GL (Fin 781) (ZMod 3)) : Matrix (Fin 781) (Fin 781) (ZMod 3)) := by
      rw [hσA, hA]
    have key : ∀ j < 31671, ((P (kψ j)).map (Matrix.mulVecLin CFSG.Sporadic.Fi24.mA) = P (kψ j) ↔
        walk TG AW (walk TG PW (S j)) = walk TG PW (S j)) := by
      intro j hj
      rw [hmA, hmap, hkψ j hj, hact]
      set y := walk TG PW (S j)
      have hy := (hψ j hj).1
      obtain ⟨hwy, hwr⟩ := hW AW hAW y hy
      rw [← eA_inv_eq] at hwr
      constructor
      · intro h
        have h2 := hsep _ _ h
        apply hrr _ _ hwy hy
        have e2 : R (walk TG AW y) * (R y)⁻¹ = (R y * ((eA : Fi24AutomorphismGroup))⁻¹ *
            (R (walk TG AW y))⁻¹)⁻¹ * (R y * ((eA⁻¹ : E) : Fi24AutomorphismGroup) * (R y)⁻¹) := by
          rw [Subgroup.coe_inv]
          group
        rw [e2]
        exact H1.mul_mem (H1.inv_mem hwr) h2
      · intro h
        apply hF
        rw [Subgroup.coe_inv]
        rw [h] at hwr
        exact hwr
    have hfilt : ((Finset.range 31671).image kψ).filter
        (fun k => (P k).map (Matrix.mulVecLin CFSG.Sporadic.Fi24.mA) = P k) =
        ((Finset.range 31671).filter fun t =>
          walk TG AW (walk TG PW (S t)) = walk TG PW (S t)).image kψ := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨⟨j, hj, rfl⟩, h⟩
        exact ⟨j, ⟨hj, (key j hj).1 h⟩, rfl⟩
      · rintro ⟨j, ⟨hj, h⟩, rfl⟩
        exact ⟨⟨j, hj, rfl⟩, (key j hj).2 h⟩
    rw [hfilt, Finset.card_image_of_injOn (hkinj.mono
      (Finset.coe_subset.2 (Finset.filter_subset _ _))), cnt_all]

end CertificateChecks.KernelFi24Fix

end
