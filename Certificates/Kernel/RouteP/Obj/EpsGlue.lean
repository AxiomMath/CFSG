module

public import Certificates.Kernel.RouteP.Obj.Eps
public import Certificates.Kernel.RouteP.Cocode.Glue
public import CFSG.Certificates.Kernel.Spor.Fi24NetPtSound

public section

namespace CertificateChecks.KernelRouteP

open Equiv CFSG.KC CFSG.KC.RouteP CFSG.KS.RouteP CFSG.KD.RouteP CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native CFSG.KC.Fi24Net CFSG.KS.Fi24Net

#kc_forall_tree epsCk_all (fun k => CFSG.KD.RouteP.epsCk k = true) 2048 CFSG.KD.RouteP.ObjCk.e
#kc_forall_tree epsSorted_all (fun i => CFSG.KD.RouteP.epsSorted i = true) 2047 CFSG.KD.RouteP.ObjCk.s

theorem kvB_eq (a b q : Nat) : kvB a b q = kv a b q := by
  unfold kvB kv
  cases a.testBit q <;> cases b.testBit q <;> rfl

theorem ptT_eq {r x : Nat} (hr : r < 58) (hx : x < 920808) : ptT r x = (gO r ⟨x, hx⟩).val := by
  rw [gT_apply (lokO (by simp; omega))]
  unfold ptT eL
  beta_reduce
  rw [if_pos hx, CFSG.KS.Fi24NetPt.ptR_eq, kvB_eq]
  rfl

theorem epsK_eq {tabs : Array Table} (hR : ∀ r < 58, Rep 920808 tabs[r]! (gO r)) {p : Nat} (hp : p < 920808) :
    ∀ f k, k ≤ f → k < 2048 → epsPt tabs p k = epsK f k p ∧ epsK f k p < 920808 := by
  intro f
  induction f with
  | zero =>
    intro k hk _
    have : k = 0 := by omega
    subst this
    exact ⟨epsPt_zero tabs p, hp⟩
  | succ f ih =>
    intro k hk hk2
    by_cases h0 : k = 0
    · subst h0
      refine ⟨epsPt_zero tabs p, ?_⟩
      unfold epsK
      rw [if_pos rfl]
      exact hp
    · have hk0 : 0 < k := Nat.pos_of_ne_zero h0
      have hl := sub_lowBit_lt hk0
      obtain ⟨e1, e2⟩ := ih (k - 1 <<< lowBit k) (by omega) (by omega)
      have hlb := lowBit_lt k
      have hr : epsReg (lowBit k) < 58 := by unfold epsReg; omega
      have e3 : epsK (f + 1) k p = ptT (epsReg (lowBit k)) (epsK f (k - 1 <<< lowBit k) p) := by
        rw [epsK.eq_2, if_neg h0]
      have h := hR _ hr (epsK f (k - 1 <<< lowBit k) p) e2
      rw [idx_of_lt _ e2, Perm.smul_def] at h
      have e4 : epsPt tabs p k = (gO (epsReg (lowBit k)) ⟨_, e2⟩).val := by
        rw [epsPt_pos tabs p hk0, e1]
        exact h
      have e5 : epsK (f + 1) k p = (gO (epsReg (lowBit k)) ⟨_, e2⟩).val := by
        rw [e3, ptT_eq hr e2]
      rw [e4, e5]
      exact ⟨rfl, (gO _ ⟨_, e2⟩).isLt⟩

theorem epsTreeOK_of_rep {tabs : Array Table} (hR : ∀ r < 58, Rep 920808 tabs[r]! (gO r)) :
    epsTreeOK tabs = true := by
  refine epsTreeOK_of tabs (fun j hj x hx => ?_) ?_
  · have hr : epsReg j < 58 := by unfold epsReg; omega
    rw [hR _ hr x hx, idx_of_lt _ hx]
    exact (_ : Fin 920808).isLt
  · have hpos : ∀ k < 2048, epsPt tabs 3 k = epsK k k 3 ∧ epsPt tabs 6 k = epsK k k 6 ∧
        epsK k k 6 < 920808 := fun k hk =>
      ⟨(epsK_eq hR (by decide) k k le_rfl hk).1, (epsK_eq hR (by decide) k k le_rfl hk).1,
        (epsK_eq hR (by decide) k k le_rfl hk).2⟩
    have hsort : ∀ a b, a < b → b < 2048 → epC a < epC b := by
      intro a b hab hb
      induction b with
      | zero => omega
      | succ b ih =>
        have hb' : b < 2047 := by omega
        have h1 := Nat.blt_eq.mp (epsSorted_all b hb')
        rcases Nat.lt_or_ge a b with h | h
        · exact (ih h (by omega)).trans h1
        · have : a = b := by omega
          subst this
          exact h1
    intro i hi j hj
    by_contra hc
    rw [not_or, not_not, not_not] at hc
    obtain ⟨hx, hy⟩ := hc
    have hj' : j < 2048 := by omega
    obtain ⟨ci, ei⟩ := CFSG.KC.Benes.andB_true (epsCk_all i hi)
    obtain ⟨cj, ej⟩ := CFSG.KC.Benes.andB_true (epsCk_all j hj')
    have hci := Nat.eq_of_beq_eq_true ci
    have hcj := Nat.eq_of_beq_eq_true cj
    have hei := Nat.eq_of_beq_eq_true ei
    have hej := Nat.eq_of_beq_eq_true ej
    obtain ⟨xi, yi, yli⟩ := hpos i hi
    obtain ⟨xj, yj, ylj⟩ := hpos j (by omega)
    have hcode : epsCode i = epsCode j := by
      unfold epsCode
      rw [← xi, ← yi, ← xj, ← yj, hx, hy]
    have hpi : epPos i < 2048 := by unfold epPos; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have hpj : epPos j < 2048 := by unfold epPos; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have hpeq : epPos i = epPos j := by
      rcases Nat.lt_trichotomy (epPos i) (epPos j) with h | h | h
      · have := hsort _ _ h hpj
        rw [← hci, ← hcj, hcode] at this
        omega
      · exact h
      · have := hsort _ _ h hpi
        rw [← hci, ← hcj, hcode] at this
        omega
    have : i = j := by rw [← hei, ← hej, hpeq]
    omega

end CertificateChecks.KernelRouteP

end
