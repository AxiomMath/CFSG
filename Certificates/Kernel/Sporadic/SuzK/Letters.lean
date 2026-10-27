module

public import Certificates.Kernel.Sporadic.SuzK.Conj
public import CFSG.Certificates.Kernel.Spor.TabWords
public import CFSG.Certificates.Kernel.Spor.VOrbSound
import Certificates.Kernel.Sporadic.SuzK.Rules
import Certificates.Kernel.Sporadic.SuzK.W0
import Certificates.Kernel.Sporadic.SuzK.W1
import Certificates.Kernel.Sporadic.SuzK.W2
import Certificates.Kernel.Sporadic.SuzK.W3
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelSpor.SuzK.ruleAll CertificateChecks.KernelSpor.SuzK.ruleK 16
#kon_join CertificateChecks.KernelSpor.SuzK.invAll CertificateChecks.KernelSpor.SuzK.invSl 14
#kon_join CertificateChecks.KernelSpor.SuzK.wordsAll CertificateChecks.KernelSpor.SuzK.wordsSl 322

namespace CertificateChecks.KernelSpor.SuzK

open CFSG.KC.Enum CFSG.KS.PEnum CFSG.KS.TW CFSG.Sporadic.Suz.Native CFSG.Sporadic.Th.Native
  CFSG.Perm.Native

theorem tab_TR (F : Nat → Nat) (hr : ∀ x < 22880, r32 F x < 22880) : TR 22880 (tabOf F) (r32 F) :=
  ⟨tabOf_size F, fun i hi => ⟨ap_tabOf F hi, hr i hi⟩⟩

theorem alpha_TR : TR 22880 orbLit.alpha (r32 AL) := tab_TR AL fun _ hx => al_lt hx

theorem beta_TR : TR 22880 orbLit.beta (r32 BE) := tab_TR BE fun _ hx => be_lt hx

theorem binv_TR : TR 22880 (invT 22880 orbLit.beta) (fun x => r32 BE (r32 BE x)) :=
  invT_TR (by norm_num) beta_TR fun i hi => ⟨be_lt (be_lt hi), beta_ord hi, beta_ord hi⟩

@[expose] noncomputable def gfun (z : Int) (x : Nat) : Nat :=
  if z = 1 ∨ z = -1 then r32 AL x else if z = 2 then r32 BE x else r32 BE (r32 BE x)

theorem gen_TR (z : Int) : TR 22880 (genTables orbLit z) (gfun z) := by
  unfold genTables gfun
  split_ifs
  · exact alpha_TR
  · exact beta_TR
  · exact binv_TR

@[expose] noncomputable def ruleA (r : Nat) : Nat := RULES.getD (2 * r) 0

@[expose] noncomputable def ruleB (r : Nat) : Nat := RULES.getD (2 * r + 1) 0

@[expose] noncomputable def expS : Nat → Nat → List Nat
  | 0, s => [s]
  | f + 1, s => if s < 3 then [s] else expS f (ruleA (s - 3)) ++ expS f (ruleB (s - 3))

@[expose] def symOfK (z : Int) : Nat := if z = 2 then 1 else if z = -2 then 2 else 0

theorem words_data : (chainWords ()).size = 14 ∧ (∀ r < 16, ruleA r < 3 + r ∧ ruleB r < 3 + r) ∧
    ∀ j < 14, (∀ z ∈ (chainWords ())[j]!, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) ∧
      (∀ s ∈ cwAt CW j, s < 19) ∧
      (cwAt CW j).flatMap (expS 16) = ((chainWords ())[j]!).map symOfK := by
  decide +kernel

theorem rule_pt {r : Nat} (hr : r < 16) {x : Nat} (hx : x < 22880) :
    symK (ruleB r) x < 22880 ∧ symK (3 + r) x = symK (ruleA r) (symK (ruleB r) x) := by
  have h := ruleAll r hr
  unfold ruleK at h
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq] at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h x hx
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at h'
  exact ⟨h'.1, Nat.eq_of_beq_eq_true h'.2⟩

theorem symK_small {s x : Nat} (hs : s < 3) (hx : x < 22880) : symK s x < 22880 := by
  rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2) with rfl | rfl | rfl
  · exact al_lt hx
  · exact be_lt hx
  · exact be_lt (be_lt hx)

theorem symK_lt : ∀ s, s < 19 → ∀ x < 22880, symK s x < 22880 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs x hx
    rcases Nat.lt_or_ge s 3 with h3 | h3
    · exact symK_small h3 hx
    · obtain ⟨hA, hB⟩ := words_data.2.1 (s - 3) (by omega)
      have e : s = 3 + (s - 3) := by omega
      obtain ⟨hb, hab⟩ := rule_pt (r := s - 3) (by omega) hx
      rw [e, hab]
      exact ih _ (by omega) (by omega) _ hb

theorem foldr_expS : ∀ f s, s < 3 + f → s < 19 → ∀ x < 22880,
    List.foldr symK x (expS f s) = symK s x
  | 0, s, _, _, x, _ => rfl
  | f + 1, s, hs, hs19, x, hx => by
    unfold expS
    split_ifs with h3
    · rfl
    · obtain ⟨hA, hB⟩ := words_data.2.1 (s - 3) (by omega)
      obtain ⟨hb, hab⟩ := rule_pt (r := s - 3) (by omega) hx
      have e : s = 3 + (s - 3) := by omega
      rw [List.foldr_append, foldr_expS f _ (by omega) (by omega) x hx,
        foldr_expS f _ (by omega) (by omega) _ hb, e, hab]
      rw [← e]

theorem foldr_lt (l : List Nat) (hl : ∀ s ∈ l, s < 19) {x : Nat} (hx : x < 22880) :
    List.foldr symK x l < 22880 := by
  induction l with
  | nil => exact hx
  | cons s l ih =>
    rw [List.foldr_cons]
    exact symK_lt s (hl s List.mem_cons_self) _ (ih fun t ht => hl t (List.mem_cons_of_mem s ht))

theorem foldr_flatMap (l : List Nat) (hl : ∀ s ∈ l, s < 19) {x : Nat} (hx : x < 22880) :
    List.foldr symK x (l.flatMap (expS 16)) = List.foldr symK x l := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    have hl' : ∀ t ∈ l, t < 19 := fun t ht => hl t (List.mem_cons_of_mem s ht)
    have hs := hl s List.mem_cons_self
    rw [List.flatMap_cons, List.foldr_append, ih hl', List.foldr_cons,
      foldr_expS 16 s (by omega) hs _ (foldr_lt l hl' hx)]

theorem foldr_map_sym (w : List Int) (hw : ∀ z ∈ w, z = 1 ∨ z = -1 ∨ z = 2 ∨ z = -2) (x : Nat) :
    List.foldr symK x (w.map symOfK) = List.foldr gfun x w := by
  induction w with
  | nil => rfl
  | cons z w ih =>
    rw [List.map_cons, List.foldr_cons, List.foldr_cons,
      ih fun t ht => hw t (List.mem_cons_of_mem z ht)]
    rcases hw z List.mem_cons_self with rfl | rfl | rfl | rfl <;> rfl

theorem word_pt {j x : Nat} (hj : j < 14) (hx : x < 22880) :
    LJ (2 * j) x = List.foldr symK x (cwAt CW j) := by
  have hs : 23 * j + x / 1000 < 322 := by omega
  have h := wordsAll (23 * j + x / 1000) hs
  unfold wordsSl at h
  have e1 : Nat.div (23 * j + x / 1000) 23 = j := by
    change (23 * j + x / 1000) / 23 = j
    omega
  have e2 : Nat.mul (Nat.mod (23 * j + x / 1000) 23) 1000 = x / 1000 * 1000 := by
    change (23 * j + x / 1000) % 23 * 1000 = x / 1000 * 1000
    congr 1
    omega
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.strictB_eq, e1, e2] at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h (x % 1000) (Nat.mod_lt _ (by norm_num))
  have e3 : Nat.add (x / 1000 * 1000) (x % 1000) = x := by
    change x / 1000 * 1000 + x % 1000 = x
    omega
  rw [CFSG.KS.Raw.Orb.strictB_eq, e3, CFSG.KS.Raw.Orb.bIf_eq, if_pos (Nat.blt_eq.mpr hx)] at h'
  exact Nat.eq_of_beq_eq_true h'

theorem word_eq {j x : Nat} (hj : j < 14) (hx : x < 22880) :
    LJ (2 * j) x = List.foldr gfun x (chainWords ())[j]! := by
  obtain ⟨-, -, hw⟩ := words_data
  obtain ⟨hz, hs, he⟩ := hw j hj
  rw [word_pt hj hx, ← foldr_flatMap _ hs hx, he, foldr_map_sym _ hz]

theorem inv_pt {j x : Nat} (hj : j < 14) (hx : x < 22880) : LJ (2 * j) x < 22880 ∧
    LJ (2 * j + 1) x < 22880 ∧ LJ (2 * j + 1) (LJ (2 * j) x) = x := by
  have h := invAll j hj
  unfold invSl at h
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h x hx
  rw [CFSG.KS.Raw.Orb.strictB_eq, CFSG.KS.Raw.Orb.bAnd_eq, CFSG.KS.Raw.Orb.bAnd_eq,
    Bool.and_eq_true, Bool.and_eq_true, Nat.blt_eq, Nat.blt_eq] at h'
  exact ⟨h'.1, h'.2.1, Nat.eq_of_beq_eq_true h'.2.2⟩

theorem chainLetters_eq : chainLetters orbLit = buildLetters 22880 (genTables orbLit) (chainWords ()) :=
  rfl

theorem letters_TR : (chainLetters orbLit).size = 28 ∧
    ∀ l < 28, ∀ x < 22880, ap (chainLetters orbLit)[l]! x = LJ l x ∧ LJ l x < 22880 := by
  have hws := words_data.1
  have hb := CFSG.KS.VO.buildLetters_get (n := 22880) (gens := genTables orbLit)
    (words := chainWords ()) (G := gfun) (H := fun j => LJ (2 * j + 1)) (by norm_num)
    (fun z x hx => (gen_TR z).2 x hx)
    (fun j hj x hx => by
      rw [hws] at hj
      rw [← word_eq hj hx]
      exact (inv_pt hj hx).2.2)
  rw [hws] at hb
  rw [chainLetters_eq]
  refine ⟨hb.1, fun l hl x hx => ?_⟩
  rcases Nat.even_or_odd' l with ⟨j, rfl | rfl⟩
  · rw [(hb.2 j (by omega) x hx).1, ← word_eq (by omega) hx]
    exact ⟨rfl, (inv_pt (by omega) hx).1⟩
  · rw [(hb.2 j (by omega) x hx).2]
    exact ⟨rfl, (inv_pt (by omega) hx).2.1⟩

end CertificateChecks.KernelSpor.SuzK

end
