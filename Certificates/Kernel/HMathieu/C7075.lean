module

public import Certificates.Kernel.HMathieu.T24
public import Certificates.Data.Kernel.HMathieu.Pred24F
public import Certificates.Kernel.SporSch.Ru.RowsGen

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelHMathieu.C7075

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu

@[expose] noncomputable def gRowR {σ : Type} (m : Nat) (upd : σ → Nat → σ)
    (pred : List Nat → List Nat → σ → Bool) (k : Nat) (l S : List Nat) (c : Nat) (st : σ)
    (rs : List (Nat × Nat)) (x i : Nat) : Bool :=
  match rs.drop i with
  | [] => true
  | r :: rest => bIf(candR m c (x + i) r.2 S,
      gAllR m upd pred k ((x + i) :: l) (appMapR S S fun s => nIf(Nat.beq s m, x + i,
        Nat.land (Nat.shiftRight r.2 (Nat.mul 8 s)) 255)) (Nat.land c r.1) (upd st (x + i)) rest
        (Nat.succ (x + i)), true)

theorem gAllR_succ_of_rows {σ : Type} (m : Nat) (upd : σ → Nat → σ)
    (pred : List Nat → List Nat → σ → Bool) (k : Nat) (l S : List Nat) (c : Nat) (st : σ)
    (rs : List (Nat × Nat)) (x : Nat) (h0 : pred l S st = true)
    (h : ∀ i < rs.length, gRowR m upd pred k l S c st rs x i = true) :
    gAllR m upd pred (k + 1) l S c st rs x = true := by
  induction rs generalizing x with
  | nil =>
    change bAnd(pred l S st, true) = true
    rw [h0]
  | cons r rest ih =>
    have h1 := ih (x + 1) fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [gRowR, Nat.add_assoc, Nat.add_comm 1 i] using this
    have hr := h 0 (by simp)
    simp only [gRowR, List.drop_zero, Nat.add_zero] at hr
    change bAnd(pred l S st, _) = true at h1
    rw [h0] at h1
    change bAnd(pred l S st, bAnd(_, _)) = true
    rw [h0]
    change bAnd(_, _) = true
    have hand : ∀ a b : Bool, bAnd(a, b) = (a && b) := fun a b => by cases a <;> rfl
    rw [hand, Bool.and_eq_true]
    exact ⟨hr, h1⟩

@[expose] noncomputable def gRowP {σ : Type} (m : Nat) (upd : σ → Nat → σ)
    (pred : List Nat → List Nat → σ → Bool) (l S : List Nat) (c : Nat) (st : σ)
    (rs : List (Nat × Nat)) (x i : Nat) : Bool :=
  match rs.drop i with
  | [] => true
  | r :: _ => bIf(candR m c (x + i) r.2 S,
      pred ((x + i) :: l) (appMapR S S fun s => nIf(Nat.beq s m, x + i,
        Nat.land (Nat.shiftRight r.2 (Nat.mul 8 s)) 255)) (upd st (x + i)), true)

@[expose] noncomputable def gRowR2 {σ : Type} (m : Nat) (upd : σ → Nat → σ)
    (pred : List Nat → List Nat → σ → Bool) (k : Nat) (l S : List Nat) (c : Nat) (st : σ)
    (rs : List (Nat × Nat)) (x i j : Nat) : Bool :=
  match rs.drop i with
  | [] => true
  | r :: rest => bIf(candR m c (x + i) r.2 S,
      gRowR m upd pred k ((x + i) :: l) (appMapR S S fun s => nIf(Nat.beq s m, x + i,
        Nat.land (Nat.shiftRight r.2 (Nat.mul 8 s)) 255)) (Nat.land c r.1) (upd st (x + i)) rest
        (Nat.succ (x + i)) j, true)

theorem gRowR_succ {σ : Type} (m : Nat) (upd : σ → Nat → σ)
    (pred : List Nat → List Nat → σ → Bool) (k : Nat) (l S : List Nat) (c : Nat) (st : σ)
    (rs : List (Nat × Nat)) (x i : Nat) (h0 : gRowP m upd pred l S c st rs x i = true)
    (h : ∀ j < rs.length, gRowR2 m upd pred k l S c st rs x i j = true) :
    gRowR m upd pred (k + 1) l S c st rs x i = true := by
  unfold gRowP at h0
  unfold gRowR2 at h
  unfold gRowR
  rcases hd : rs.drop i with _ | ⟨r, rest⟩
  · rfl
  · simp only [hd] at h0 h
    dsimp only
    have hl : rest.length < rs.length := by
      have := congrArg List.length hd
      simp at this
      omega
    cases hc : candR m c (x + i) r.2 S
    · rfl
    · simp only [hc] at h0 h
      exact gAllR_succ_of_rows _ _ _ _ _ _ _ _ _ _ h0 fun j hj => h j (by omega)

@[expose] noncomputable def c7test (t : Nat) : Bool :=
  gRowP 191 (fun st y => (T24.Mc.getD y [] :: st.1, fixLstQ (T24.Mc.getD y []) st.2))
    (pred24FK T24.Mc) [] [191] (2 ^ 191 - 1) ([], List.range (2 ^ 11)) T24.rows 0 (2 * t)

@[expose] noncomputable def c7pair (n : Nat) : Bool :=
  gRowR2 191 (fun st y => (T24.Mc.getD y [] :: st.1, fixLstQ (T24.Mc.getD y []) st.2))
    (pred24FK T24.Mc) 5 [] [191] (2 ^ 191 - 1) ([], List.range (2 ^ 11)) T24.rows 0
    (2 * (n / 191)) (n % 191)

@[expose] noncomputable def blk (i : Nat) : Bool :=
  (i == 0 || i == 2) ||
  gRowR 191 (fun st y => (T24.Mc.getD y [] :: st.1, fixLstQ (T24.Mc.getD y []) st.2))
    (pred24FK T24.Mc) 6 [] [191] (2 ^ 191 - 1) ([], List.range (2 ^ 11)) T24.rows 0 i

end CertificateChecks.KernelHMathieu.C7075

end

set_option maxHeartbeats 0

#kss_each CertificateChecks.KernelHMathieu.C7075.T CertificateChecks.KernelHMathieu.C7075.c7test 2

#kss_each CertificateChecks.KernelHMathieu.C7075.J CertificateChecks.KernelHMathieu.C7075.c7pair 382

#kss_each CertificateChecks.KernelHMathieu.C7075.B CertificateChecks.KernelHMathieu.C7075.blk 191

public section

namespace CertificateChecks.KernelHMathieu.C7075

open CFSG.KC.HMathieu CFSG.Quasithin.H.Mathieu CertificateChecks.KernelHMathieu

theorem search : gAllR 191 (fun st y => (T24.Mc.getD y [] :: st.1,
      fixLstQ (T24.Mc.getD y []) st.2)) (pred24FK T24.Mc) 7 [] [191]
    (2 ^ 191 - 1) ([], List.range (2 ^ 11)) T24.rows 0 = true :=
  gAllR_succ_of_rows _ _ _ 6 _ _ _ _ _ _ (by decide +kernel) fun i hi => by
    have hi' : i < 191 := by rw [← T24.lenOK.2]; exact hi
    by_cases hh : i = 0 ∨ i = 2
    · obtain ⟨t, ht, rfl⟩ : ∃ t, t < 2 ∧ i = 2 * t := by
        rcases hh with h | h
        exacts [⟨0, by omega, by omega⟩, ⟨1, by omega, by omega⟩]
      refine gRowR_succ _ _ _ 5 _ _ _ _ _ _ (2 * t) (T.all t ht) fun j hj => ?_
      have hj' : j < 191 := by rw [← T24.lenOK.2]; exact hj
      have hp := J.all (t * 191 + j) (by change t * 191 + j < 382; omega)
      have e1 : (t * 191 + j) / 191 = t := by omega
      have e2 : (t * 191 + j) % 191 = j := by omega
      unfold c7pair at hp
      rw [e1, e2] at hp
      exact hp
    · have hp := B.all i hi'
      have hf : (i == 0 || i == 2) = false := by
        simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
        omega
      unfold blk at hp
      rw [hf, Bool.false_or] at hp
      exact hp

end CertificateChecks.KernelHMathieu.C7075

end
