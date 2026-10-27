
module

public import Certificates.Kernel.Sporadic.ON3.Strong
public import Certificates.Kernel.Sporadic.ON4.Defs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON4K

open CFSG.KC.Enum CFSG.KS CFSG.KS.TW CertificateChecks.KernelSpor.ON3

theorem fold_X {N k : Nat} {X : Nat → Nat} {G GI Gi GIi : Nat → Nat → Nat}
    (h : ∀ j < k, ∀ i < N, G j (X i) = X (Gi j i) ∧ Gi j i < N ∧ GI j (X i) = X (GIi j i) ∧
      GIi j i < N) :
    ∀ w : List Int, LetM k w → ∀ i < N,
      w.foldr (GZ G GI) (X i) = X (w.foldr (GZ Gi GIi) i) ∧ w.foldr (GZ Gi GIi) i < N
  | [], _, i, hi => ⟨rfl, hi⟩
  | l :: w, hw, i, hi => by
    obtain ⟨e, hlt⟩ := fold_X h w (fun z hz => hw z (List.mem_cons_of_mem l hz)) i hi
    obtain ⟨h1, h2⟩ := hw l List.mem_cons_self
    simp only [List.foldr_cons]
    rw [e]
    unfold GZ
    by_cases hp : 0 < l
    · simp only [hp, ite_true]
      have := h (l.toNat - 1) (by omega) _ hlt
      exact ⟨this.1, this.2.1⟩
    · simp only [hp, ite_false]
      have := h ((-l).toNat - 1) (by omega) _ hlt
      exact ⟨this.2.2.1, this.2.2.2⟩

theorem blt_false {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  rw [Bool.eq_false_iff]
  intro e
  have : a < b := by simpa using e
  omega

theorem xAt_spec {N s m i : Nat} {X P : Nat → Nat} {I II O D : Nat → Nat → Nat}
    (h : xAt N s m X P I II O D i = true) : X i < 245520 ∧ P (X i) = i ∧ ∀ j < s,
      I j i < N ∧ II j i < N ∧ I j (II j i) = i ∧ (j < m → X (I j i) = O j (X i)) ∧
      (m ≤ j → I j i = D j i) := by
  unfold xAt at h
  simp only [strictB_eq'', bAnd_iff, Nat.beq_eq] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simpa using h1, h2, fun j hj => ?_⟩
  have h4 := allN_spec h3 j hj
  simp only [bAnd_iff, Nat.beq_eq] at h4
  obtain ⟨a1, a2, a3, a4⟩ := h4
  refine ⟨by simpa using a1, by simpa using a2, a3, fun hjm => ?_, fun hjm => ?_⟩
  · have hb : Nat.blt j m = true := by simpa using hjm
    rw [hb] at a4
    simpa using a4
  · have hb : Nat.blt j m = false := blt_false hjm
    rw [hb] at a4
    simpa using a4

theorem pxAt_spec {N x : Nat} {X P : Nat → Nat} (h : pxAt N X P x = true) (hp : P x < N) :
    X (P x) = x := by
  unfold pxAt at h
  simp only [strictB_eq''] at h
  have hb : Nat.blt (P x) N = true := by simpa using hp
  rw [hb] at h
  simpa using h

theorem fastX_eq {N s m : Nat} {X P : Nat → Nat} {I II O D F FI : Nat → Nat → Nat}
    {W : Nat → List Int}
    (hpair : InvPair 245520 s F FI)
    (hxat : ∀ i < N, xAt N s m X P I II O D i = true)
    (hpx : ∀ x < 245520, pxAt N X P x = true)
    (hO : ∀ j < m, ∀ y < 245520, O j y = F j y)
    (hD : ∀ j, m ≤ j → j < s → LetM j (W j) ∧ (∀ x < 245520, F j x = (W j).foldr (GZ F FI) x) ∧
      ∀ i, D j i = (W j).foldr (GZ I II) i) :
    fastX N s X P I F = F ∧ fastX N s X P II FI = FI := by
  have hA : ∀ j < s, ∀ i < N, F j (X i) = X (I j i) ∧ I j i < N ∧
      FI j (X i) = X (II j i) ∧ II j i < N := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have hF : ∀ i < N, F j (X i) = X (I j i) := by
        intro i hi
        obtain ⟨hX, -, hs⟩ := xAt_spec (hxat i hi)
        obtain ⟨-, -, -, ho, hd⟩ := hs j hj
        rcases Nat.lt_or_ge j m with hjm | hjm
        · rw [← hO j hjm _ hX, ho hjm]
        · obtain ⟨hw, hf, hdd⟩ := hD j hjm hj
          rw [hf _ hX, hd hjm, hdd]
          exact (fold_X (k := j) (fun j' hj' i' hi' => ih j' hj' (by omega) i' hi') _ hw i hi).1
      intro i hi
      obtain ⟨-, -, hs⟩ := xAt_spec (hxat i hi)
      obtain ⟨a1, a2, a3, -, -⟩ := hs j hj
      refine ⟨hF i hi, a1, ?_, a2⟩
      obtain ⟨hX', -, -⟩ := xAt_spec (hxat _ a2)
      have e : F j (X (II j i)) = X i := by rw [hF _ a2, a3]
      rw [← e, (hpair j hj _ hX').2.2.1]
  have key : ∀ (T Tslow : Nat → Nat → Nat),
      (∀ j < s, ∀ i < N, Tslow j (X i) = X (T j i)) → fastX N s X P T Tslow = Tslow := by
    intro T Tslow hT
    funext j x
    unfold fastX
    rw [strictN_eq']
    by_cases hc : j < s ∧ x < 245520 ∧ P x < N
    · obtain ⟨c1, c2, c3⟩ := hc
      have hb : bAnd(Nat.blt j s, bAnd(Nat.blt x 245520, Nat.blt (P x) N)) = true := by
        simp only [bAnd_iff]
        exact ⟨by simpa using c1, by simpa using c2, by simpa using c3⟩
      rw [hb]
      have e := pxAt_spec (hpx x c2) c3
      have e2 : X (T j (P x)) = Tslow j x := by rw [← hT j c1 _ c3, e]
      exact e2
    · have hb : bAnd(Nat.blt j s, bAnd(Nat.blt x 245520, Nat.blt (P x) N)) = false := by
        rw [Bool.eq_false_iff]
        intro hb
        simp only [bAnd_iff] at hb
        exact hc ⟨by simpa using hb.1, by simpa using hb.2.1, by simpa using hb.2.2⟩
      rw [hb]
  exact ⟨key I F fun j hj i hi => (hA j hj i hi).1, key II FI fun j hj i hi => (hA j hj i hi).2.2.1⟩

end CertificateChecks.KernelSpor.ON4K

end
