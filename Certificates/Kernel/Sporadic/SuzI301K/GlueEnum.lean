module

public import Certificates.Kernel.Sporadic.SuzI301K.GlueQ
public import Certificates.Kernel.Sporadic.SuzI301K.Rep

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.SuzI301K

open CFSG.KC.Enum CFSG.KC.LinRep CFSG.KC.LinRepSound CFSG.KC.LinRepCheck CFSG.KC.SuzI301Lin
open CFSG.KC.SuzI301K CFSG.KD.SuzI301 CFSG.PSL3Four.Native CFSG.Sporadic.SuzI301
  CFSG.ComponentClassification.AS81.SuzB0

@[expose] noncomputable def mT (i : Nat) : Nat := J 3 i / 2

theorem mT_lt : ∀ i < 6, mT i < 64 := fun i hi => by
  have := J_lt (c := 3) (by norm_num) hi
  unfold mT
  omega

theorem lenN_eq : ∀ L : List Nat, lenN L = L.length
  | [] => rfl
  | _ :: L => by
    change Nat.succ (lenN L) = _
    rw [lenN_eq L]
    rfl

theorem gwK_spec {A : Nat → Nat → Nat} {G C : List Nat} (k : gwK A G C = true) :
    Nat.beq (lenN G) 11 = true ∧ Nat.beq (nthN G 10) (nthN C 3) = true ∧
      (allN 10 fun k => allN 6 fun i => Nat.beq (c6 (nthN G k) i) (A k i)) = true := by
  unfold gwK at k
  obtain ⟨k1, k⟩ := band k
  obtain ⟨k2, k3⟩ := band k
  exact ⟨k1, k2, k3⟩

theorem gw_facts : GW.length = 11 ∧ ∀ j < 11, ∀ i < 6, col (nthN GW j) i = genCols mT j i := by
  obtain ⟨k1, k2, k3⟩ := gwK_spec kGW
  refine ⟨by rw [← lenN_eq]; exact Nat.eq_of_beq_eq_true k1, fun j hj i hi => ?_⟩
  by_cases h10 : j < 10
  · have e := CFSG.KS.allN_spec (CFSG.KS.allN_spec k3 j h10) i hi
    beta_reduce at e
    rw [← c6_eq_col, Nat.eq_of_beq_eq_true e]
    simp [genCols, h10]
  · have e : j = 10 := by omega
    subst e
    rw [Nat.eq_of_beq_eq_true k2, cw_col (by norm_num) hi]
    simp [genCols, mT]

theorem gt_len : GT.length = 11 := rfl

theorem n_eq : N = 51840 := rfl

theorem rows_ok : ∀ h < N, rowK TB GT 11 N (row (RW (h / 1024)) (h % 1024)) h = true := by
  intro h hh
  rw [n_eq] at hh
  have hs : h / 1024 < 51 := by omega
  have e := segAll (h / 1024) hs
  unfold ch810302seg segK at e
  have hl : h % 1024 < segLen (h / 1024) := by
    unfold segLen
    by_cases h50 : h / 1024 < 50
    · rw [Nat.blt_eq.mpr h50]
      exact Nat.mod_lt _ (by norm_num)
    · have hb : Nat.blt (h / 1024) 50 = false := by
        cases hc : Nat.blt (h / 1024) 50
        · rfl
        · exact absurd (Nat.blt_eq.mp hc) h50
      rw [hb]
      change h % 1024 < 640
      omega
  have e2 := CFSG.KS.allN_spec e _ hl
  beta_reduce at e2
  have hh' : Nat.add (Nat.shiftLeft (h / 1024) 10) (h % 1024) = h := by
    change (h / 1024) <<< 10 + h % 1024 = h
    rw [Nat.shiftLeft_eq]
    omega
  rw [hh'] at e2
  exact e2

theorem enum_facts :
    enumOK 64 (matTabs.push (linTab mT)) (enumBFS 64 (matTabs.push (linTab mT)) 51840) = true ∧
      (enumBFS 64 (matTabs.push (linTab mT)) 51840).tabs.size = 51840 ∧
      ∀ i < 51840, (enumBFS 64 (matTabs.push (linTab mT)) 51840).tabs[i]! =
        linTab (col (key (slot TB i))) := by
  obtain ⟨hgl, hgt, hpos, h0, hp0, hl0, hinj, htree, horder, hclose⟩ :=
    rec_of_checks (k := 11) gt_len kHead kOrd rows_ok
  have hsz := gens_size (linTab mT)
  rw [n_eq] at hpos hinj htree horder hclose
  refine enum_of_words (gc := genCols mT) (step := fun j w => mulT (nthN GT j) w)
    (M := fun i => key (slot TB i)) (par := fun i => spar (slot TB i))
    (lab := fun i => slab (slot TB i)) (pos := fun h j => pos16 (row (RW (h / 1024)) (h % 1024)) j)
    (gens_lin mT_lt) ?_ hpos h0 hp0 hl0 (fun a _ => key_lt _) hinj ?_ horder ?_ (Nat.le_refl _)
  · intro j hj w i hi
    rw [hsz] at hj
    beta_reduce
    rw [hgt j hj, col_mulT_tabW _ _ hi]
    exact ev_congr (fun i' hi' => gw_facts.2 j hj i' hi') _
  · intro i hi hc
    obtain ⟨a, b, c⟩ := htree i hi hc
    exact ⟨a, by rw [hsz]; exact b, c⟩
  · intro h hh j hj
    rw [hsz] at hj
    exact hclose h hh j hj

end CertificateChecks.KernelSpor.SuzI301K

end
