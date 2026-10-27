module

public import CFSG.Certificates.Kernel.Spor.PWord
public import CFSG.Sporadic.Schreier.ONPermArr
public import CFSG.Sporadic.ONOddCore.SeedOrdersCheckInputs

public section

namespace CertificateChecks.KernelSpor.ONOrd

open CFSG.ONSchreier.Native CFSG.KS.PW

variable {n : Nat} {t u : Array Nat} {F G : Nat → Nat}

@[expose] def Rd (n : Nat) (t : Array Nat) (F : Nat → Nat) : Prop :=
  t.size = n ∧ ∀ x < n, t[x]! = F x ∧ F x < n

@[expose] def powN (F : Nat → Nat) (k x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ acc => F acc) k

theorem Rd.congr (h : Rd n t F) (e : ∀ x < n, F x = G x) : Rd n t G :=
  ⟨h.1, fun x hx => by rw [← e x hx]; exact h.2 x hx⟩

theorem Rd.eq (h : Rd n t F) : t = Array.ofFn (n := n) fun i => F i.val :=
  arr_ext h.1 fun x hx => (h.2 x hx).1

theorem rd_pid : Rd n (pid n) fun x => x :=
  ⟨by simp [pid], fun _ hx => ⟨pid_get' hx, hx⟩⟩

theorem rd_pcomp (ht : Rd n t F) (hu : Rd n u G) : Rd n (pcomp n t u) fun x => F (G x) := by
  refine ⟨by simp [pcomp], fun x hx => ?_⟩
  obtain ⟨e, hl⟩ := hu.2 x hx
  obtain ⟨e', hl'⟩ := ht.2 _ hl
  exact ⟨by rw [pcomp_get' hx, e, e'], hl'⟩

theorem rd_ppow {a : Array Nat} (ha : Rd CFSG.Sporadic.ON.Native.nPts a F) :
    ∀ k, Rd CFSG.Sporadic.ON.Native.nPts (CFSG.Sporadic.ONOddCore.ppow a k) (powN F k)
  | 0 => rd_pid
  | k + 1 => by
    rw [CFSG.Sporadic.ONOddCore.ppow]
    exact (rd_pcomp ha (rd_ppow ha k)).congr fun _ _ => rfl

theorem pinvCand_size (n : Nat) (t : Array Nat) : (pinvCand n t).size = n := by
  have heq : pinvCand n t =
      (List.range' 0 n).foldl (fun p i => p.set! t[i]! i) (Array.replicate n 0) := by
    unfold pinvCand
    simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      List.forIn_pure_yield_eq_foldl]
  rw [heq]
  have : ∀ (l : List Nat) (p : Array Nat), (l.foldl (fun p i => p.set! t[i]! i) p).size = p.size := by
    intro l
    induction l with
    | nil => intro p; rfl
    | cons a l ih => intro p; rw [List.foldl_cons, ih]; simp
  rw [this]
  simp

theorem rd_pinvCand (ht : Rd n t F) (hG : ∀ x < n, G x < n) (hGF : ∀ x < n, G (F x) = x) :
    Rd n (pinvCand n t) G := by
  refine ⟨pinvCand_size n t, fun x hx => ⟨?_, hG x hx⟩⟩
  rw [ht.eq]
  exact CFSG.KS.CB.pinvCand_get (fun y hy => (ht.2 y hy).2) hGF hx

theorem peq_iff (ht : Rd n t F) (hu : Rd n u G) : peq n t u = true ↔ ∀ x < n, F x = G x := by
  unfold peq
  rw [CFSG.ONSchreier.allBelowN_iff]
  refine forall₂_congr fun x hx => ?_
  rw [(ht.2 x hx).1, (hu.2 x hx).1, beq_iff_eq]

theorem peq_true (ht : Rd n t F) (hu : Rd n u G) (h : ∀ x < n, F x = G x) : peq n t u = true :=
  (peq_iff ht hu).2 h

theorem peq_false (ht : Rd n t F) (hu : Rd n u G) {x : Nat} (hx : x < n) (h : F x ≠ G x) :
    peq n t u = false :=
  Bool.eq_false_iff.2 fun e => h ((peq_iff ht hu).1 e x hx)

theorem pisInv_of (ht : Rd n t F) (hu : Rd n u G) (h : ∀ x < n, G (F x) = x) :
    pisInv n t u = true := by
  unfold pisInv
  refine CFSG.ONSchreier.allBelowN_iff.2 fun x hx => ?_
  obtain ⟨e, hl⟩ := ht.2 x hx
  rw [e, (hu.2 _ hl).1, h x hx]
  simp [hl]

end CertificateChecks.KernelSpor.ONOrd

end
