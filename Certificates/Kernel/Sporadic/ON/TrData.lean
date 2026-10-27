module

public import Certificates.Kernel.Sporadic.ON.Data
public import Certificates.Kernel.Sporadic.FLGen
public import CFSG.Certificates.Kernel.Spor.TabWords
import Certificates.Kernel.Sporadic.OrbRecGen
public meta import Certificates.Kernel.Sporadic.ON.Data
public meta import CFSG.Sporadic.Schreier.ONActionData
public meta import Lean

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.ON

meta def bigT (h : Nat) (u : Bool) : Array Nat :=
  let t := strongM[h]!
  CFSG.KS.ONGen.leaves 18 9 (if u then CFSG.KS.RawGen.inv t.size t else t)

meta def bT0 : Array Nat := bigT 0 false
meta def bT1 : Array Nat := bigT 1 false
meta def bT2 : Array Nat := bigT 2 false
meta def bT3 : Array Nat := bigT 3 false
meta def bT4 : Array Nat := bigT 4 false
meta def bT5 : Array Nat := bigT 5 false
meta def bT6 : Array Nat := bigT 6 false
meta def bU0 : Array Nat := bigT 0 true
meta def bU1 : Array Nat := bigT 1 true
meta def bU2 : Array Nat := bigT 2 true
meta def bU3 : Array Nat := bigT 3 true
meta def bU4 : Array Nat := bigT 4 true
meta def bU5 : Array Nat := bigT 5 true
meta def bU6 : Array Nat := bigT 6 true

end CertificateChecks.KernelSpor.ON

#kc_nattree CertificateChecks.KernelSpor.ONB.A CertificateChecks.KernelSpor.ON.bT0
#kc_nattree CertificateChecks.KernelSpor.ONB.U0 CertificateChecks.KernelSpor.ON.bU0
#kc_nattree CertificateChecks.KernelSpor.ONB.B CertificateChecks.KernelSpor.ON.bT1
#kc_nattree CertificateChecks.KernelSpor.ONB.U1 CertificateChecks.KernelSpor.ON.bU1
#kc_nattree CertificateChecks.KernelSpor.ONB.T2 CertificateChecks.KernelSpor.ON.bT2
#kc_nattree CertificateChecks.KernelSpor.ONB.U2 CertificateChecks.KernelSpor.ON.bU2
#kc_nattree CertificateChecks.KernelSpor.ONB.T3 CertificateChecks.KernelSpor.ON.bT3
#kc_nattree CertificateChecks.KernelSpor.ONB.U3 CertificateChecks.KernelSpor.ON.bU3
#kc_nattree CertificateChecks.KernelSpor.ONB.T4 CertificateChecks.KernelSpor.ON.bT4
#kc_nattree CertificateChecks.KernelSpor.ONB.U4 CertificateChecks.KernelSpor.ON.bU4
#kc_nattree CertificateChecks.KernelSpor.ONB.T5 CertificateChecks.KernelSpor.ON.bT5
#kc_nattree CertificateChecks.KernelSpor.ONB.U5 CertificateChecks.KernelSpor.ON.bU5
#kc_nattree CertificateChecks.KernelSpor.ONB.T6 CertificateChecks.KernelSpor.ON.bT6
#kc_nattree CertificateChecks.KernelSpor.ONB.U6 CertificateChecks.KernelSpor.ON.bU6

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.TW CFSG.KS.Words CFSG.KS.FLGen

@[expose] noncomputable def tb (T : Nat → Nat) (i : Nat) : Nat :=
  rget T (nat_lit 9) (nat_lit 511) (nat_lit 18) (mask (nat_lit 18)) i

@[expose] noncomputable def TB (h i : Nat) : Nat :=
  nIf(Nat.beq h 0, tb ONB.A i, nIf(Nat.beq h 1, tb ONB.B i, nIf(Nat.beq h 2, tb ONB.T2 i,
    nIf(Nat.beq h 3, tb ONB.T3 i, nIf(Nat.beq h 4, tb ONB.T4 i, nIf(Nat.beq h 5, tb ONB.T5 i,
      tb ONB.T6 i))))))

@[expose] noncomputable def UB (h i : Nat) : Nat :=
  nIf(Nat.beq h 0, tb ONB.U0 i, nIf(Nat.beq h 1, tb ONB.U1 i, nIf(Nat.beq h 2, tb ONB.U2 i,
    nIf(Nat.beq h 3, tb ONB.U3 i, nIf(Nat.beq h 4, tb ONB.U4 i, nIf(Nat.beq h 5, tb ONB.U5 i,
      tb ONB.U6 i))))))

end CertificateChecks.KernelSpor.ON

#kon_flists CertificateChecks.KernelSpor.ON.tb CertificateChecks.KernelSpor.ONB
  CertificateChecks.KernelSpor.ONB.FL CFSG.ONSchreier.Data.strongWords 2 7

#kon_nests CertificateChecks.KernelSpor.ON.tb CertificateChecks.KernelSpor.ONB
  CertificateChecks.KernelSpor.ONB.NE CFSG.ONSchreier.Data.strongWords 2 7

namespace CertificateChecks.KernelSpor.ON

open CFSG.KC.Enum CFSG.KS CFSG.KS.ON CFSG.KS.TW CFSG.KS.Words CFSG.KS.FLGen

@[expose] noncomputable def FL (j : Nat) : List (Nat → Nat) :=
  cond (Nat.beq j 2) ONB.FL2 (cond (Nat.beq j 3) ONB.FL3 (cond (Nat.beq j 4) ONB.FL4
    (cond (Nat.beq j 5) ONB.FL5 ONB.FL6)))

@[expose] noncomputable def NE (j : Nat) : Nat → Nat :=
  cond (Nat.beq j 2) ONB.NE2 (cond (Nat.beq j 3) ONB.NE3 (cond (Nat.beq j 4) ONB.NE4
    (cond (Nat.beq j 5) ONB.NE5 ONB.NE6)))

@[expose] noncomputable def trAtF (x : Nat) : Bool :=
  bAnd(allBlk (nat_lit 0) (fun h => strictB (TT h x) fun y => bAnd(Nat.blt y (nat_lit 245520),
      bAnd(Nat.blt (UU h x) (nat_lit 245520), Nat.beq (UU h y) x))) (nat_lit 7),
    bAnd(allBlk (nat_lit 0) (fun h => bAnd(Nat.beq (TB h x) (TT h x), Nat.beq (UB h x) (UU h x)))
        (nat_lit 7),
      allBlk (nat_lit 2) (fun j => Nat.beq (TT j x) (NE j x)) (nat_lit 5)))

@[expose] noncomputable def trF (s : Nat) : Bool :=
  allBlk (Nat.mul s (nat_lit 240)) trAtF (nat_lit 240)

theorem FL2_eq : ONB.FL2 = (decW (ONV.WC 2) (ONV.WL 2)).map (GZ TB UB) := by kernelRfl
theorem FL3_eq : ONB.FL3 = (decW (ONV.WC 3) (ONV.WL 3)).map (GZ TB UB) := by kernelRfl
theorem FL4_eq : ONB.FL4 = (decW (ONV.WC 4) (ONV.WL 4)).map (GZ TB UB) := by kernelRfl
theorem FL5_eq : ONB.FL5 = (decW (ONV.WC 5) (ONV.WL 5)).map (GZ TB UB) := by kernelRfl
theorem FL6_eq : ONB.FL6 = (decW (ONV.WC 6) (ONV.WL 6)).map (GZ TB UB) := by kernelRfl

theorem FL_eq : ∀ j, 2 ≤ j → j < 7 → FL j = (decW (ONV.WC j) (ONV.WL j)).map (GZ TB UB) := by
  intro j h2 h7
  obtain rfl | rfl | rfl | rfl | rfl : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  · exact FL2_eq
  · exact FL3_eq
  · exact FL4_eq
  · exact FL5_eq
  · exact FL6_eq

theorem NE_eq : ∀ j, 2 ≤ j → j < 7 → ∀ x, NE j x = traceR (FL j) x := by
  intro j h2 h7 x
  obtain rfl | rfl | rfl | rfl | rfl : j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  all_goals kernelRfl

theorem strictB_eq (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

section

variable (hx : ∀ x < 245520, trAtF x = true)

include hx in
theorem agree_lt : ∀ h < 7, ∀ v < 245520, TB h v = TT h v ∧ UB h v = UU h v ∧
    TT h v < 245520 ∧ UU h v < 245520 := by
  intro h hh v hv
  have e := hx v hv
  unfold trAtF at e
  obtain ⟨hp, hr⟩ := bAnd_iff.1 e
  obtain ⟨ha, -⟩ := bAnd_iff.1 hr
  have h1 := allBlk_spec hp h hh
  have h2 := allBlk_spec ha h hh
  rw [Nat.add_eq, Nat.zero_add] at h1 h2
  rw [strictB_eq] at h1
  obtain ⟨a1, h4⟩ := bAnd_iff.1 h1
  obtain ⟨a2, -⟩ := bAnd_iff.1 h4
  obtain ⟨b1, b2⟩ := bAnd_iff.1 h2
  exact ⟨Nat.eq_of_beq_eq_true b1, Nat.eq_of_beq_eq_true b2, Nat.blt_eq.mp a1, Nat.blt_eq.mp a2⟩

include hx in
theorem agree_all : ∀ h, ∀ v < 245520, TB h v = TT h v ∧ UB h v = UU h v ∧
    TT h v < 245520 ∧ UU h v < 245520 := by
  intro h v hv
  rcases Nat.lt_or_ge h 7 with hh | hh
  · exact agree_lt hx h hh v hv
  · obtain ⟨k, rfl⟩ : ∃ k, h = k + 7 := ⟨h - 7, by omega⟩
    exact agree_lt hx 6 (by omega) v hv

include hx in
theorem foldr_agree : ∀ (L : List Int), ∀ v < 245520,
    L.foldr (GZ TB UB) v = L.foldr (GZ TT UU) v ∧ L.foldr (GZ TT UU) v < 245520
  | [], v, hv => ⟨rfl, hv⟩
  | z :: L, v, hv => by
    obtain ⟨e, hw⟩ := foldr_agree L v hv
    simp only [List.foldr_cons]
    rw [e]
    obtain ⟨a1, a2, a3, a4⟩ := agree_all hx (if 0 < z then z.toNat - 1 else (-z).toNat - 1) _ hw
    unfold GZ
    by_cases hz : 0 < z
    · simp only [hz, ite_true] at a1 a3 ⊢
      exact ⟨a1, a3⟩
    · simp only [hz, ite_false] at a2 a4 ⊢
      exact ⟨a2, a4⟩

include hx in
theorem word_eq : ∀ j, 2 ≤ j → j < 7 → ∀ v < 245520,
    TT j v = trace TT UU (ONV.WC j) (ONV.WL j) v := by
  intro j h2 h7 v hv
  have e := hx v hv
  unfold trAtF at e
  obtain ⟨-, hr⟩ := bAnd_iff.1 e
  obtain ⟨-, hw⟩ := bAnd_iff.1 hr
  have h1 := allBlk_spec hw (j - 2) (by change j - 2 < 5; omega)
  rw [Nat.add_eq, show 2 + (j - 2) = j by omega] at h1
  rw [Nat.eq_of_beq_eq_true h1, NE_eq j h2 h7, FL_eq j h2 h7, traceR_map, trace_eq]
  exact (foldr_agree hx _ v hv).1

end

theorem trS_of_trF (hF : ∀ s < 1023, trF s = true) : ∀ s < 1023, trS s = true := by
  have hx : ∀ x < 245520, trAtF x = true := by
    intro x hx
    have := allBlk_spec (hF (x / 240) (by omega)) (x % 240) (Nat.mod_lt _ (by omega))
    have e : Nat.add (Nat.mul (x / 240) 240) (x % 240) = x := by
      simp only [Nat.add_eq, Nat.mul_eq]
      omega
    rwa [e] at this
  intro s hs
  unfold trS trRange
  refine allBlk_of fun l hl => ?_
  have hl' : l < 240 := hl
  have hxl : Nat.add (Nat.mul s 240) l < 245520 := by
    simp only [Nat.add_eq, Nat.mul_eq]
    omega
  have e := hx _ hxl
  unfold trAtF at e
  obtain ⟨hp, -⟩ := bAnd_iff.1 e
  unfold trAt
  refine bAnd_iff.2 ⟨hp, allBlk_of fun k hk => ?_⟩
  have hk' : k < 5 := hk
  rw [word_eq hx (Nat.add 2 k) (by change 2 ≤ 2 + k; omega) (by change 2 + k < 7; omega) _ hxl]
  exact Nat.beq_refl _

end CertificateChecks.KernelSpor.ON

end
