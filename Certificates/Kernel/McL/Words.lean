module

public import Certificates.Kernel.Ru.Words
public import CFSG.Certificates.Kernel.McLSubSound
public import CFSG.Certificates.Kernel.McLDceSound
public import CFSG.Certificates.Kernel.McL.TCBind
public import CFSG.Certificates.Kernel.McL.Rels
import Mathlib.Tactic.IntervalCases

public section

namespace CertificateChecks.KernelMcL

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE CFSG.Certificates.McLS
  CFSG.Certificates.McLD TauCeti
open CertificateChecks.KernelHe CertificateChecks.KernelRu

theorem rec_acc_sound (f : Nat → Bool) : ∀ {n},
    Nat.rec (motive := fun _ => Bool) true (fun i acc => andB acc (f i)) n = true →
      ∀ i < n, f i = true
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, hr, i, hi => by
    have hr' : andB (Nat.rec (motive := fun _ => Bool) true (fun i acc => andB acc (f i)) n)
      (f n) = true := hr
    rw [andB_true_iff] at hr'
    rcases Nat.lt_or_ge i n with hn | hn
    · exact rec_acc_sound f hr'.1 i hn
    · have : i = n := by omega
      subst this
      exact hr'.2

set_option maxRecDepth 20000 in
theorem smallTab_of {F : Nat → Nat} (h : McL.RangeX.smallTabB F = true) : smallTab F := by
  unfold smallTab
  intro c hc
  have h1 := rec_acc_sound (fun c => andB (Nat.blt (McL.Sub.pn (F c)) (nat_lit 16))
    (Nat.blt (McL.Sub.pw (F c)) (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8)
      (McL.Sub.pn (F c)))))) (n := nat_lit 256) h c hc
  rw [andB_true_iff, Nat.blt_eq, Nat.blt_eq] at h1
  refine ⟨h1.1, ?_⟩
  have e : Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) (McL.Sub.pn (F c))) =
      2 ^ (8 * McL.Sub.pn (F c)) := (Nat.shiftLeft_eq _ _).trans (Nat.one_mul _)
  rw [← e]
  exact h1.2

theorem entsBelow_sound {T : Nat → Nat} {nE b : Nat} (h : McL.RangeX.entsBelow T nE b = true) :
    ∀ r < nE, ∀ i < LceS.wLen (T r), wLet (LceS.wWord (T r)) i < b := by
  intro r hr i hi
  have h1 := rec_acc_sound _ h r hr
  have h2 := rec_acc_sound _ h1 i hi
  rw [Nat.blt_eq] at h2
  exact h2

theorem relsNorm_sound {RT : Nat → Nat} {n : Nat} (h : relsNorm RT n = true) :
    ∀ r < n, LceS.wWord (RT r) < 2 ^ (8 * LceS.wLen (RT r)) := by
  intro r hr
  have h1 := rec_andB_sound _ h r hr
  rw [Nat.blt_eq] at h1
  have e : Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) (LceS.wLen (RT r))) =
      2 ^ (8 * LceS.wLen (RT r)) := (Nat.shiftLeft_eq _ _).trans (Nat.one_mul _)
  rw [← e]
  exact h1

theorem relsOK_sound {RR : Nat → Nat} {NL NR : Nat} (h : McL.Dce.relsOK RR NL NR = true) :
    ∀ r < NR, ∀ i < LceS.wLen (RR r), wLet (LceS.wWord (RR r)) i < NL := by
  intro r hr i hi
  have h1 := rec_acc_sound _ h r hr
  have h2 := rec_acc_sound _ h1 i hi
  rw [Nat.blt_eq] at h2
  exact h2

set_option maxRecDepth 20000 in
theorem epWrap_sound {EP ED : Nat → Nat} {nE P : Nat} (h : McL.RangeX.epWrap EP ED nE P = true) :
    ∀ e < 4096, EP e = 0 ∨ ∃ e' < nE, EP e = EP e' ∧ ED e = ED e' := by
  intro e he
  have hk1 : e / 64 < 64 := Nat.div_lt_of_lt_mul he
  have hk2 : e % 64 < 64 := Nat.mod_lt e (by norm_num)
  let g : Nat → Bool := fun e => orB (Nat.beq (EP e) (nat_lit 0))
    (andB (Nat.blt (Nat.mod e P) nE) (andB (Nat.beq (EP e) (EP (Nat.mod e P)))
      (Nat.beq (ED e) (ED (Nat.mod e P)))))
  let F : Nat → Bool := fun h => Nat.rec (motive := fun _ => Bool) true
    (fun l ih2 => andB (g (Nat.add (Nat.shiftLeft h (nat_lit 6)) l)) ih2) (nat_lit 64)
  have h0 : Nat.rec (motive := fun _ => Bool) true (fun h ih => andB (F h) ih) (nat_lit 64) =
    true := h
  have h1 := rec_andB_sound F h0 (e / 64) hk1
  have h2 := rec_andB_sound (fun l => g (Nat.add (Nat.shiftLeft (e / 64) (nat_lit 6)) l)) h1
    (e % 64) hk2
  have sl : Nat.shiftLeft (e / 64) (nat_lit 6) = e / 64 * 2 ^ 6 := Nat.shiftLeft_eq _ _
  have he' : Nat.add (Nat.shiftLeft (e / 64) (nat_lit 6)) (e % 64) = e := by
    rw [sl, Nat.add_eq]
    omega
  have h3 : g (Nat.add (Nat.shiftLeft (e / 64) (nat_lit 6)) (e % 64)) = true := h2
  rw [he'] at h3
  have h4 : orB (Nat.beq (EP e) 0) (andB (Nat.blt (Nat.mod e P) nE)
      (andB (Nat.beq (EP e) (EP (Nat.mod e P))) (Nat.beq (ED e) (ED (Nat.mod e P))))) = true := h3
  cases hb : Nat.beq (EP e) 0
  · rw [hb] at h4
    have h5 : andB (Nat.blt (Nat.mod e P) nE)
        (andB (Nat.beq (EP e) (EP (Nat.mod e P))) (Nat.beq (ED e) (ED (Nat.mod e P)))) = true := h4
    rw [andB_true_iff, andB_true_iff, Nat.blt_eq, Nat.beq_eq, Nat.beq_eq] at h5
    exact Or.inr ⟨e % P, h5.1, h5.2.1, h5.2.2⟩
  · exact Or.inl (Nat.eq_of_beq_eq_true hb)

theorem bval_eq_list {G : Type*} [Group G] (y : ℕ → G) (W n : ℕ) (L : List ℕ)
    (hL : (List.range n).map (wLet W) = L) : bval y W n = (L.map (letV y)).prod := by
  rw [← hL, List.map_map]
  rfl

theorem ival_eq_list {G : Type*} [Group G] (y : ℕ → G) (W n : ℕ) (L : List ℕ)
    (hL : (List.range n).map (wLet W) = L) :
    ival y W n = (L.map fun c => if c = 255 then 1 else y c).prod := by
  rw [← hL, List.map_map]
  rfl

theorem pval_eq_list {G : Type*} [Group G] (y : ℕ → G) (v : ℕ) (L : List ℕ)
    (hL : (List.range (McL.Sub.pn v)).map (wLet (McL.Sub.pw v)) = L) :
    pval y v = (L.map (letV y)).prod :=
  bval_eq_list y _ _ L hL

@[expose] noncomputable def yv {G : Type*} [Group G] (gen : ℕ → G) (g : ℕ) : G :=
  pval gen (McL.Rels.XT (2 * g))

theorem yv_eq {G : Type*} [Group G] (gen : ℕ → G) :
    yv gen 0 = gen 0 ∧ yv gen 1 = (gen 1)⁻¹ * gen 0 * gen 1 ∧
      yv gen 2 = gen 1 * gen 1 * gen 0 * (gen 1)⁻¹ * (gen 1)⁻¹ ∧
      yv gen 3 = gen 1 * gen 0 * (gen 1)⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [yv, pval_eq_list gen _ [0] (by decide)]
    simp [letV]
  · rw [yv, pval_eq_list gen _ [3, 0, 2] (by decide)]
    simp [letV, mul_assoc]
  · rw [yv, pval_eq_list gen _ [2, 2, 0, 3, 3] (by decide)]
    simp [letV, mul_assoc]
  · rw [yv, pval_eq_list gen _ [2, 0, 3] (by decide)]
    simp [letV, mul_assoc]

theorem pval_XT {G : Type*} [Group G] (gen : ℕ → G) : ∀ c < 8,
    pval gen (McL.Rels.XT c) = letV (yv gen) c := by
  obtain ⟨h0, h1, h2, h3⟩ := yv_eq gen
  intro c hc
  interval_cases c
  · rw [pval_eq_list gen _ [0] (by decide)]
    simp [letV, h0]
  · rw [pval_eq_list gen _ [1] (by decide)]
    simp [letV, h0]
  · rw [pval_eq_list gen _ [3, 0, 2] (by decide)]
    simp [letV, h1, mul_assoc]
  · rw [pval_eq_list gen _ [3, 1, 2] (by decide)]
    simp [letV, h1, mul_assoc]
  · rw [pval_eq_list gen _ [2, 2, 0, 3, 3] (by decide)]
    simp [letV, h2, mul_assoc]
  · rw [pval_eq_list gen _ [2, 2, 1, 3, 3] (by decide)]
    simp [letV, h2, mul_assoc]
  · rw [pval_eq_list gen _ [2, 0, 3] (by decide)]
    simp [letV, h3, mul_assoc]
  · rw [pval_eq_list gen _ [2, 1, 3] (by decide)]
    simp [letV, h3, mul_assoc]

theorem pval_XT_inv {G : Type*} [Group G] (gen : ℕ → G) : ∀ c < 8,
    pval gen (McL.Rels.XT (c ^^^ 1)) = (pval gen (McL.Rels.XT c))⁻¹ := by
  intro c hc
  have hc' : c ^^^ 1 < 8 := by interval_cases c <;> decide
  rw [pval_XT gen _ hc', pval_XT gen _ hc]
  interval_cases c <;> simp [letV]

theorem fval_XT {G : Type*} [Group G] (gen : ℕ → G) {W n : ℕ} (h : ∀ i < n, wLet W i < 8) :
    fval gen McL.Rels.XT W n = bval (yv gen) W n := by
  unfold fval bval
  congr 1
  apply List.map_congr_left
  intro i hi
  exact pval_XT gen _ (h i (List.mem_range.mp hi))

theorem fval_XD {G : Type*} [Group G] (gen : ℕ → G) {W n : ℕ} (h : ∀ i < n, wLet W i < 4) :
    fval gen McL.Rels.XD W n = ival (yv gen) W n := by
  unfold fval ival
  congr 1
  apply List.map_congr_left
  intro i hi
  have hl := h i (List.mem_range.mp hi)
  split_ifs with h255
  · omega
  · rfl

theorem tc_sel_eq (r : ℕ) (hr : r < 15) : McL.TC.sel r = McL.TC.list.getD r 0 := by
  interval_cases r <;> rfl

theorem tc_wordNat_eq : ∀ w : List (ℕ × Bool), McL.TC.wordNat w = HeB.wordNat w
  | [] => rfl
  | l :: w => by
    rw [McL.TC.wordNat, HeB.wordNat, tc_wordNat_eq w]
    rfl

theorem tc_ent_eq (w : List (ℕ × Bool)) : McL.TC.ent w = HeB.ent w := by
  rw [McL.TC.ent, HeB.ent, tc_wordNat_eq]

theorem tc_letters_small : ∀ w ∈ Sporadic.mclPresentation.relatorLetters,
    w.length < 1024 ∧ ∀ l ∈ w, l.1 < 127 := by
  intro w hw
  rw [GroupPresentation.relatorLetters_def, List.mem_map] at hw
  obtain ⟨r, hr, rfl⟩ := hw
  have hgc : Sporadic.mclPresentation.generatorCount = 2 := by
    simp [GroupPresentation.generatorCount, Sporadic.mclPresentation_generatorNames]
  refine ⟨?_, ?_⟩
  · rw [List.length_map]
    have hlen := List.mem_map_of_mem (f := List.length) hr
    rw [Sporadic.mclPresentation_map_length_relators] at hlen
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hlen
    omega
  · intro l hl
    rw [List.mem_map] at hl
    obtain ⟨l', -, rfl⟩ := hl
    have := l'.1.isLt
    omega

theorem tc_ok (r : ℕ) (hr : r < 15) :
    LceS.wWord (McL.TC.sel r) < 2 ^ (8 * LceS.wLen (McL.TC.sel r)) ∧
      bval (KB.tcGen Sporadic.mclPresentation) (LceS.wWord (McL.TC.sel r))
        (LceS.wLen (McL.TC.sel r)) = 1 := by
  rw [tc_sel_eq r hr, ← McL.TC.relators_eq, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases hw : Sporadic.mclPresentation.relatorLetters[r]? with _ | w
  · exact ⟨by decide, rfl⟩
  · have hmem := List.mem_of_getElem? hw
    obtain ⟨hlen, hl⟩ := tc_letters_small w hmem
    simp only [Option.map_some, Option.getD_some, tc_ent_eq]
    rw [wWord_ent w hlen, wLen_ent w hlen]
    exact ⟨wordNat_lt w hl, (bval_wordNat _ w hl).trans (KB.sword_relatorLetters _ w hmem)⟩

end CertificateChecks.KernelMcL

end
