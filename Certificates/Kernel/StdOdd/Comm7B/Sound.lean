module

public import Certificates.Data.Kernel.Misc.E6ConjOrb
public import Certificates.Kernel.Misc.E6StdBridge

public section

namespace CFSG.KC.Misc.E6Std

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

attribute [local irreducible] mulB

theorem snocN_eq (l : List ℕ) (y : ℕ) : snocN l y = l ++ [y] := by
  induction l with
  | nil => rfl
  | cons x l ih => exact congrArg (List.cons x) ih

theorem memN_eq_true_iff (y : ℕ) (l : List ℕ) : memN y l = true ↔ y ∈ l := by
  unfold memN
  rw [letB_eq']
  induction l with
  | nil => simp
  | cons x l ih =>
    have e : List.rec (motive := fun _ => Bool) false (fun z _ ih => orB (Nat.beq y z) ih)
        (x :: l) = orB (Nat.beq y x)
          (List.rec (motive := fun _ => Bool) false (fun z _ ih => orB (Nat.beq y z) ih) l) := rfl
    rw [e, List.mem_cons, ← ih]
    cases h : Nat.beq y x
    · have hne : y ≠ x := fun hyx => by
        rw [hyx, Nat.beq_refl] at h
        cases h
      exact ⟨fun h' => Or.inr h', fun h' => h'.resolve_left hne⟩
    · exact ⟨fun _ => Or.inl (Nat.eq_of_beq_eq_true h), fun _ => rfl⟩

theorem conjStepK_sound (P : ℕ → Prop) (G Gi : ℕ → ℕ)
    (hP : ∀ N j, P N → P (mulB (mulB (G j) N) (Gi j))) :
    ∀ (steps : List (ℕ × ℕ)) (acc : List ℕ), (∀ N ∈ acc, P N) → acc.Nodup →
      conjStepK G Gi steps acc = true →
        ∃ L : List ℕ, L.Nodup ∧ L.length = acc.length + steps.length ∧ ∀ N ∈ L, P N := by
  intro steps
  induction steps with
  | nil => exact fun acc hacc hnd _ => ⟨acc, hnd, rfl, hacc⟩
  | cons s steps ih =>
    intro acc hacc hnd h
    obtain ⟨p, j⟩ := s
    have e : conjStepK G Gi ((p, j) :: steps) acc = andB (Nat.blt p (lenN acc))
        (letB (mulB (mulB (G j) (nthV acc p)) (Gi j)) fun y =>
          andB (notB (memN y acc)) (conjStepK G Gi steps (snocN acc y))) := rfl
    rw [e, letB_eq', andB_eq', andB_eq', Bool.and_eq_true, Bool.and_eq_true, notB_eq',
      Bool.not_eq_true', Nat.blt_eq, lenN_eq_length] at h
    obtain ⟨hp, hmem, hrest⟩ := h
    have hy : mulB (mulB (G j) (nthV acc p)) (Gi j) ∉ acc := by
      rw [← memN_eq_true_iff, hmem]
      exact Bool.false_ne_true
    have hPy : P (mulB (mulB (G j) (nthV acc p)) (Gi j)) := by
      refine hP _ j (hacc _ ?_)
      rw [nthV_eq_getD, List.getD_eq_getElem _ _ hp]
      exact List.getElem_mem hp
    rw [snocN_eq] at hrest
    obtain ⟨L, hL, hlen, hPL⟩ := ih (acc ++ [mulB (mulB (G j) (nthV acc p)) (Gi j)])
      (fun N hN => by
        rcases List.mem_append.1 hN with hN | hN
        · exact hacc N hN
        · rw [List.mem_singleton.1 hN]
          exact hPy)
      (List.nodup_append.2 ⟨hnd, List.nodup_singleton _, fun a ha b hb => by
        rw [List.mem_singleton.1 hb]
        rintro rfl
        exact hy ha⟩) hrest
    refine ⟨L, hL, ?_, hPL⟩
    rw [hlen, List.length_append, List.length_singleton, List.length_cons]
    omega

theorem conjOrbK_sound (P : ℕ → Prop) {a ai b bi z : ℕ} {steps : List (ℕ × ℕ)}
    (hz : P z) (ha : ∀ N, P N → P (mulB (mulB a N) ai))
    (hb : ∀ N, P N → P (mulB (mulB b N) bi)) (h : conjOrbK a ai b bi steps z = true) :
    ∃ L : List ℕ, L.Nodup ∧ L.length = 1 + steps.length ∧ ∀ N ∈ L, P N := by
  unfold conjOrbK at h
  rw [letB_eq', letB_eq', letB_eq', letB_eq', letB_eq'] at h
  have hP : ∀ N j, P N → P (mulB (mulB (Bool.rec (motive := fun _ => ℕ) b a (Nat.beq j 0)) N)
      (Bool.rec (motive := fun _ => ℕ) bi ai (Nat.beq j 0))) := by
    intro N j hN
    cases Nat.beq j 0
    · exact hb N hN
    · exact ha N hN
  have := conjStepK_sound P _ _ hP steps [z] (fun N hN => by
    rw [List.mem_singleton.1 hN]
    exact hz) (List.nodup_singleton z) h
  simpa only [List.length_singleton] using this

end CFSG.KC.Misc.E6Std

end
