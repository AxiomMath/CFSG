
module

public import Certificates.Kernel.SporSch.Th.Plane2320Base

public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CertificateChecks.KernelSporSch.ThPlane

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch CFSG.Sporadic.Th.Native CFSG.Sporadic.ThSchreier
open CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.ThRow (sh1)
open CertificateChecks.KernelSporSch.ThUA (all8 UB ltUB block_eq rowsA_eq un)
open CertificateChecks.KernelSporSch.ThKey (C1 C2)

theorem chain {Ls : List (Array V4)} {n : Nat} {SS : Nat → Nat} {LT : Nat → Nat → Nat}
    (hn : Ls.length = n) (hn0 : 0 < n) (hL : ∀ k < n, Ls[k]! = rowsV (LT k))
    (hbL : ∀ k < n, ∀ i < 248, LT k i < 2 ^ 248) (hbS : ∀ k < n, ∀ i < 248, slice SS k i < 2 ^ 248)
    (hlast : ∀ i < 248, slice SS (n - 1) i = LT (n - 1) i)
    (hstep : ∀ k, k + 1 < n → ∀ i < 248, vmT (slice SS (k + 1)) (LT k i) = slice SS k i) :
    CFSG.Sporadic.Th.Max3.prodRows Ls = rowsV (slice SS 0) := by
  have key : ∀ d m, m + d + 1 = n →
      CFSG.Sporadic.Th.Max3.prodRows (Ls.drop m) = rowsV (slice SS m) := by
    intro d
    induction d with
    | zero =>
      intro m hm
      have hlt : m < Ls.length := by omega
      rw [List.drop_eq_getElem_cons hlt, List.drop_eq_nil_of_le (by omega),
        CFSG.Sporadic.Th.Max3.prodRows_cons, CFSG.Sporadic.Th.Max3.prodRows_nil,
        ← getElem!_pos Ls m hlt, hL m (by omega), mulRowsId_sound (hbL m (by omega))]
      have hm' : m = n - 1 := by omega
      exact rowsV_congr fun i hi => by
        rw [hm']
        exact (hlast i hi).symm
    | succ d ih =>
      intro m hm
      have hlt : m < Ls.length := by omega
      rw [List.drop_eq_getElem_cons hlt, CFSG.Sporadic.Th.Max3.prodRows_cons, ih (m + 1) (by omega),
        ← getElem!_pos Ls m hlt, hL m (by omega)]
      exact mulRows_sound (hbL m (by omega)) (hbS (m + 1) (by omega)) (hstep m (by omega))
  have := key (n - 1) 0 (by omega)
  rwa [List.drop_zero] at this

theorem vinv_eq : rowsVInv = rowsV (slice ThVI.SS 0) := by
  rw [rowsVInv, abRows, signedRows]
  refine chain (n := 35) (LT := letRow ThVI.LC ThA ThBB) (by simp [len_w]) (by omega) letters
    (fun k _ i hi => ?_) (fun k hk i hi => bnd (allN_spec ltSS (k * 248 + i) (by omega)))
    (fun i hi => Nat.eq_of_beq_eq_true (allN_spec last i hi)) (fun k hk i hi => ?_)
  · unfold letRow
    rcases Bool.eq_false_or_eq_true (Nat.beq (ThVI.LC k) 0) with h | h
    · rw [h]
      exact bA i hi
    · rw [h]
      exact bBB i hi
  · have hk' : k < 34 := by omega
    have h8 : i / 31 < 8 := by omega
    have := allBlk_spec (ThVI.hc k hk' (i / 31) h8) (i % 31) (Nat.mod_lt _ (by omega))
    have e : Nat.add (Nat.mul 31 (i / 31)) (i % 31) = i := by
      rw [Nat.add_eq, Nat.mul_eq]
      exact Nat.div_add_mod i 31
    rw [e] at this
    exact Nat.eq_of_beq_eq_true this

theorem facts : inUA starKey.u = true ∧ inUA starKey.v = true := by
  have hrow : wKeyRow = canon (v4OfNat C1) (v4OfNat C2) := rfl
  have hk : starKey = ⟨v4OfNat SU, v4OfNat SV⟩ := by
    rw [starKey, vinv_eq, hrow, canonN_sound (bnd kC1) (bnd kC2), imageKey]
    dsimp only
    have hS0 : ∀ i < 248, slice ThVI.SS 0 i < 2 ^ 248 :=
      fun i hi => bnd (allN_spec ltSS (0 * 248 + i) (by omega))
    rw [frApply_sound (R := slice ThVI.SS 0) (x := canonN C1 C2 % 2 ^ 256) hS0 (bnd kA),
      frApply_sound (R := slice ThVI.SS 0) (x := canonN C1 C2 / 2 ^ 256) hS0 (bnd kB),
      canonN_sound (a := vmT (slice ThVI.SS 0) (canonN C1 C2 % 2 ^ 256))
        (b := vmT (slice ThVI.SS 0) (canonN C1 C2 / 2 ^ 256)) (bnd kIA) (bnd kIB)]
    rfl
  rw [hk, inUA, inUA, rowsUAQ, block_eq 1 (by omega)]
  exact ⟨inUAT_sound (ltUB 1 (by omega)) (bnd kSU) (Nat.eq_of_beq_eq_true uU),
    inUAT_sound (ltUB 1 (by omega)) (bnd kSV) (Nat.eq_of_beq_eq_true uV)⟩

end CertificateChecks.KernelSporSch.ThPlane

end
