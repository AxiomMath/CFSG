module

public import CFSG.Sporadic.J4.QTOutNative
public import CFSG.Sporadic.J4.QTRankNative
public import Certificates.Kernel.J4Q.MaskU
public import CFSG.Sporadic.J4.QTOutNative
import Certificates.Kernel.J4Q.AllN
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Q

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.QT

@[expose] def mkStep (L L' : List Nat) : Bool :=
  (L'.all fun c => mkTL.all fun t => L.contains (c ^^^ actT t c)) &&
    ((List.range 2048).all fun c => L'.contains c || mkTL.any fun t => !L.contains (c ^^^ actT t c)) &&
    (mkTL.all fun t => t == idT || (List.range 11).any fun j => !L.contains (actT t (2 ^ j) ^^^ 2 ^ j))

theorem ucsStep_eq (L L' : List Nat) : ucsStep L L' = mkStep L L' := by
  unfold ucsStep stepIn stepOut stepFaithful mkStep
  rw [tabL_eq]

@[expose] def mkZ (k : Nat) : List Nat := ucsMasks.getD k []

@[expose] def mkIn (x : Nat) : Bool :=
  (mkZ (x / 1024 + 1)).all fun c => (mkZ (x / 1024)).contains (c ^^^ actT (mkTL.getD (x % 1024) []) c)

@[expose] def mkOut (x : Nat) : Bool :=
  (mkZ (x / 2048 + 1)).contains (x % 2048) ||
    mkTL.any fun t => !(mkZ (x / 2048)).contains (x % 2048 ^^^ actT t (x % 2048))

@[expose] def mkFa (x : Nat) : Bool :=
  mkTL.getD (x % 1024) [] == idT || (List.range 11).any fun j =>
    !(mkZ (x / 1024)).contains (actT (mkTL.getD (x % 1024) []) (2 ^ j) ^^^ 2 ^ j)

@[expose] noncomputable def mkInc (q : Nat) : Bool := CFSG.KC.Enum.allN 32 fun j => mkIn (32 * q + j)

@[expose] noncomputable def mkOutc (q : Nat) : Bool := CFSG.KC.Enum.allN 32 fun j => mkOut (32 * q + j)

@[expose] noncomputable def mkFac (q : Nat) : Bool := CFSG.KC.Enum.allN 32 fun j => mkFa (32 * q + j)

#j4q_all CFSG.KD.J4Q.UIN CertificateChecks.KernelJ4Q.mkInc 128
#j4q_all CFSG.KD.J4Q.UOT CertificateChecks.KernelJ4Q.mkOutc 256
#j4q_all CFSG.KD.J4Q.UFA CertificateChecks.KernelJ4Q.mkFac 128

theorem at_idx {f : Nat → Bool} {n : Nat} (h : ∀ q < n, CFSG.KC.Enum.allN 32 (fun j => f (32 * q + j)) = true)
    {x : Nat} (hx : x < 32 * n) : f x = true := by
  have := mkChunkW (w := 32) (n := n) (f := fun q j => f (32 * q + j)) h hx
  simp only [mkSplitW] at this
  exact this

theorem step_ok {k : Nat} (hk : k < 4) : mkStep (mkZ k) (mkZ (k + 1)) = true := by
  unfold mkStep
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨fun c hc t ht => ?_, fun c hc => ?_⟩, fun t ht => ?_⟩
  · obtain ⟨e, he, rfl⟩ := mem_mkTL ht
    have h := at_idx (f := mkIn) (n := 128) UIN.all (x := 1024 * k + e) (by omega)
    unfold mkIn at h
    have h1 : (1024 * k + e) / 1024 = k := by omega
    have h2 : (1024 * k + e) % 1024 = e := by omega
    rw [h1, h2, List.all_eq_true] at h
    exact h c hc
  · have hc' := List.mem_range.1 hc
    have h := at_idx (f := mkOut) (n := 256) UOT.all (x := 2048 * k + c) (by omega)
    unfold mkOut at h
    have h1 : (2048 * k + c) / 2048 = k := by omega
    have h2 : (2048 * k + c) % 2048 = c := by omega
    rw [h1, h2] at h
    exact h
  · obtain ⟨e, he, rfl⟩ := mem_mkTL ht
    have h := at_idx (f := mkFa) (n := 128) UFA.all (x := 1024 * k + e) (by omega)
    unfold mkFa at h
    have h1 : (1024 * k + e) / 1024 = k := by omega
    have h2 : (1024 * k + e) % 1024 = e := by omega
    rw [h1, h2] at h
    exact h

theorem tET_eq : tET = mkTL.getD 576 [] := tab_eq (by decide)

@[expose] def mkZ4 (e : Nat) : Bool :=
  !fixesZ4 (mkTL.getD e []) || mkTL.getD e [] == idT || mkTL.getD e [] == mkTL.getD 576 []

@[expose] noncomputable def mkZ4c (q : Nat) : Bool := CFSG.KC.Enum.allN 32 fun j => mkZ4 (32 * q + j)

#j4q_all CFSG.KD.J4Q.UZ4 CertificateChecks.KernelJ4Q.mkZ4c 32

theorem tET_chk : decide (compT (mkTL.getD 576 []) (mkTL.getD 576 []) = idT ∧
    mkTL.getD 576 [] ≠ idT ∧ fixesZ4 (mkTL.getD 576 []) = true) = true := by
  quickRfl

theorem ucs_chk : decide ((∀ L ∈ ucsMasks, ∀ c ∈ L, c < 2 ^ 11) ∧ ucsMasks.getD 0 [] = [0] ∧
    ucsMasks.length = 5) = true := by
  quickRfl

open CFSG CFSG.Sporadic CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT in
theorem c4019 : (∀ L ∈ ucsMasks, ∀ c ∈ L, c < 2 ^ 11)
    ∧ (ucsMasks.getD 0 [] = [0])
    ∧ (ucsMasks.length = 5)
    ∧ (∀ k < 4, ucsStep (ucsMasks.getD k []) (ucsMasks.getD (k + 1) []) = true)
    ∧ (∀ t ∈ tabL, fixesZ4 t = true → t = idT ∨ t = tET)
    ∧ (tET ∈ tabL ∧ compT tET tET = idT ∧ tET ≠ idT)
    ∧ (fixesZ4 tET = true)
    ∧ (eT < 1024) := by
  obtain ⟨h1, h2, h3⟩ := of_decide_eq_true ucs_chk
  obtain ⟨t1, t2, t3⟩ := of_decide_eq_true tET_chk
  refine ⟨h1, h2, h3, fun k hk => ?_, ?_, ?_, ?_, by decide⟩
  · rw [ucsStep_eq]
    exact step_ok hk
  · rw [tabL_eq, tET_eq]
    intro t ht hf
    obtain ⟨e, he, rfl⟩ := mem_mkTL ht
    have h := at_idx (f := mkZ4) (n := 32) UZ4.all (x := e) (by omega)
    unfold mkZ4 at h
    rw [hf] at h
    simpa using h
  · rw [tabL_eq, tET_eq]
    exact ⟨getD_mem_mkTL (by decide), t1, t2⟩
  · rw [tET_eq]
    exact t3

end CertificateChecks.KernelJ4Q

end
