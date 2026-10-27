module

public import Certificates.Kernel.Fi22S0.ParseL
public import CFSG.Certificates.Kernel.Fi22S0.Parse

public section

namespace CertificateChecks.KernelFi22S0

open CFSG.Sporadic.Fi22.S0 CFSG.KS.Fi22S0Parse

theorem opsRec_pair (t : Nat) :
    (opsRec (2 * t), opsRec (2 * t + 1)) = (oi (t + 3), oj (t + 3)) := by
  have h : Nat.sub (t + 3) (nat_lit 3) = t := Nat.add_sub_cancel t 3
  unfold opsRec oi oj
  rw [h]
  rfl

theorem parRec_pair (i : Nat) : (parRec (2 * i), parRec (2 * i + 1)) = (pp i, pj i) := by
  have a0 : Nat.land (2 * i) (nat_lit 1) = 0 := by
    change (2 * i) &&& 1 = 0
    rw [Nat.and_one_is_mod]
    omega
  have a1 : Nat.land (2 * i + 1) (nat_lit 1) = 1 := by
    change (2 * i + 1) &&& 1 = 1
    rw [Nat.and_one_is_mod]
    omega
  have s0 : Nat.shiftRight (2 * i) (nat_lit 1) = i := by
    change (2 * i) >>> 1 = i
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have s1 : Nat.shiftRight (2 * i + 1) (nat_lit 1) = i := by
    change (2 * i + 1) >>> 1 = i
    rw [Nat.shiftRight_eq_div_pow]
    omega
  unfold parRec
  rw [a0, a1, s0, s1]
  rfl

theorem LRec_eq (j i : Nat) (hi : i < 19683) : LRec (19683 * j + i) = lt j i := by
  have d : Nat.div (19683 * j + i) (nat_lit 19683) = j := by
    change (19683 * j + i) / 19683 = j
    omega
  have m : Nat.mod (19683 * j + i) (nat_lit 19683) = i := by
    change (19683 * j + i) % 19683 = i
    omega
  unfold LRec
  rw [d, m]

theorem ops_eq : ops () = Array.ofFn (n := 567) fun t => (oi (t.val + 3), oj (t.val + 3)) := by
  exact (ops_of OS.eq ch131101pOps).trans
    (congrArg Array.ofFn (funext fun t => opsRec_pair t.val))

theorem par_eq : par () = Array.ofFn (n := 19683) fun i => (pp i.val, pj i.val) := by
  exact (par_of PS.eq ch131101pPar).trans
    (congrArg Array.ofFn (funext fun i => parRec_pair i.val))

theorem L_eq : L () = Array.ofFn (n := 3) fun j => Array.ofFn (n := 19683) fun i =>
    lt j.val i.val := by
  exact (L_of LS.eq ch131101pL).trans (congrArg Array.ofFn (funext fun j =>
    congrArg Array.ofFn (funext fun i => LRec_eq j.val i.val i.isLt)))

end CertificateChecks.KernelFi22S0

end
