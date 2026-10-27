module

public import Certificates.Kernel.J4Q.QTBase
public import CFSG.Certificates.Kernel.J4Q.RepQT2B
public import CFSG.Sporadic.J4.QT2LocNative

public section

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KC.Loop CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT
  CFSG.Sporadic.J4.QT2

theorem pathVecFrom_enc : ∀ (p : List Nat) (v : V2), v.wf = true →
    (pathVecFrom p v).wf = true ∧ v2N (pathVecFrom p v) = pathVK rm one [A, B] p (v2N v)
  | [], _, hv => ⟨hv, rfl⟩
  | l :: p, v, hv => by
    have hb := base_gens (l - 1)
    obtain ⟨h1, h2⟩ := pathVecFrom_enc p _ (wf_frApply hb.1 v)
    rw [pathVecFrom]
    refine ⟨h1, h2.trans ?_⟩
    change _ = strictN (vecJ rm (v2N v) (getN one [A, B] (l - 1))) (pathVK rm one [A, B] p)
    rw [strictN_eq, ← hb.2, ← v2N_frApply hK hb.1 hv]

theorem pathVec_enc (p : List Nat) :
    (pathVec p).wf = true ∧ v2N (pathVec p) = pathVK rm one [A, B] p (v2N rootV) :=
  pathVecFrom_enc p rootV (by decide)

theorem pathRows_enc : ∀ p : List Nat, WfA (pathRows p) ∧ encR (pathRows p) = pathRK c rm one [A, B] p
  | [] => id_enc hK
  | l :: p => by
    rw [pathRows]
    exact mul_enc hK (base_gens (l - 1)) (pathRows_enc p)

theorem etaVec_enc {v : V2} (hv : v.wf = true) (m : Nat) :
    (frApply (frTable (etaRows (uTab (locMats ()) (locInvs ())) 11 m)) v).wf = true ∧
      v2N (frApply (frTable (etaRows (uTab (locMats ()) (locInvs ())) 11 m)) v) =
        vecEtaK rm Us m (v2N v) :=
  v2N_etaRows hK uTab_enc hv m

theorem getN_mem (d : Nat) : ∀ (l : List Nat) (k : Nat), k < l.length → getN d l k ∈ l
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => List.mem_cons_self
  | _ :: l, k + 1, h => List.mem_cons_of_mem _ (getN_mem d l k (by simp at h; omega))

theorem getN_of_mem (d : Nat) {x : Nat} : ∀ {l : List Nat}, x ∈ l → ∃ j < l.length, getN d l j = x
  | [], h => absurd h List.not_mem_nil
  | y :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, by simp, rfl⟩
    · obtain ⟨j, hj, he⟩ := getN_of_mem d h
      exact ⟨j + 1, by simp; omega, he⟩

theorem eqLK_spec : ∀ {l₁ l₂ : List Nat}, eqLK l₁ l₂ = true → l₁ = l₂
  | [], [], _ => rfl
  | [], _ :: _, h => (Bool.false_ne_true h).elim
  | _ :: _, [], h => (Bool.false_ne_true h).elim
  | x :: l₁, y :: l₂, h => by
    change andB (Nat.beq x y) (eqLK l₁ l₂) = true at h
    rw [andB_eq, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, eqLK_spec h.2]

end CertificateChecks.KernelJ4Q

end
