module

public import Certificates.Data.Kernel.J4SlpB
public import CFSG.Certificates.Kernel.J4SlpSound
public import Certificates.Kernel.J4M2.C12607
public import Certificates.Kernel.SporSch.J4S.InvP
public import Certificates.Kernel.J4M2.C12611Checks
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4SlpPrefixData
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4Gam

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.KS.SporSch.J4B CFSG.KS.SporSch.J4E CFSG.Sporadic.J4Schreier
  CertificateChecks.KernelSporSch.J4E7 CFSG.AGLEmbeddingD2.Wilson.NormalizerAction CFSG.KC.J4Slp
  CFSG.Sporadic.GLQ

theorem slpB_forceB_eq : ∀ (l : List Nat) (k : List Nat → Bool), forceB l k = k l
  | [], _ => rfl
  | x :: l, k => by
    change CFSG.KC.J4Slp.strictB x (fun a => forceB l fun t => k (a :: t)) = _
    rw [CFSG.KC.J4Slp.strictB_eq]
    exact slpB_forceB_eq l fun t => k (x :: t)

theorem slpB_getN (d : Nat) : ∀ (l : List Nat) (i : Nat), getN d l i = l.getD i d
  | [], _ => rfl
  | x :: l, 0 => by rw [List.getD_cons_zero]; rfl
  | x :: l, i + 1 => by rw [List.getD_cons_succ]; exact slpB_getN d l i

theorem slpB_initKN_get {n i : Nat} (hi : 6 ≤ i) (hn : i < 2 * n) :
    (initKN one A A B Bi n).getD i 0 = one := by
  unfold initKN
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_replicate]
  simp only [List.length_cons, List.length_nil]
  rw [if_pos (by omega)]
  rfl

theorem slpB_init_ok {n : Nat} (hn : 3 ≤ n) :
    RegsOK n (initRegsN O n An Bn) (initKN one A A B Bi n) := by
  refine ⟨Array.size_ofFn, by simp [initKN]; omega, fun r hr => ?_⟩
  have e : (initRegsN O n An Bn)[r]! = if r = 1 then An else if r = 2 then Bn else (O.one, O.one) := by
    rw [getElem!_pos _ r (by simp [initRegsN, hr])]
    simp [initRegsN]
  rw [e]
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ 3 ≤ r) with h | h | h | h
  · subst h
    exact oneP_ok CertificateChecks.KernelSporSch.J4Real.hK
  · subst h
    exact CertificateChecks.KernelSporSch.J4InvP.pA
  · subst h
    exact CertificateChecks.KernelSporSch.J4InvP.pB
  · rw [if_neg (by omega), if_neg (by omega)]
    have h1 : regM (initKN one A A B Bi n) r = one := by
      unfold regM
      rw [slpB_getN]
      exact slpB_initKN_get (by simp; omega) (by simp; omega)
    have h2 : regI (initKN one A A B Bi n) r = one := by
      unfold regI
      rw [slpB_getN]
      exact slpB_initKN_get (by simp; omega) (by simp; omega)
    rw [h1, h2]
    exact oneP_ok CertificateChecks.KernelSporSch.J4Real.hK

theorem slpB_neOK {X Y : Array Nat} (hX : WfN X) (hY : WfN Y) :
    neOK X Y = neK rm (encN X) (encN Y) := by
  have e1 : ∀ t, O.vmul (O.unit t) X = vecJ rm (1 <<< t) (encN X) := fun t =>
    vec_enc CertificateChecks.KernelSporSch.J4Real.hK hX _
  have e2 : ∀ t, O.vmul (O.unit t) Y = vecJ rm (1 <<< t) (encN Y) := fun t =>
    vec_enc CertificateChecks.KernelSporSch.J4Real.hK hY _
  unfold neOK
  simp only [e1, e2]
  rfl

theorem slpB_eq {X Y : Array Nat} (hX : WfN X) (hY : WfN Y) (h : Nat.beq (encN X) (encN Y) = true) :
    O.eq X Y = true := by
  have e : X = Y := enc_inj hX hY (Nat.eq_of_beq_eq_true h)
  change (X == Y) = true
  rw [e]
  exact beq_self_eq_true _

theorem slpB_pow_eq {X Y : Array Nat} (hX : WfN X) (hY : WfN Y) {e : Nat}
    (h : Nat.beq (powJ c rm one (encN X) e) (encN Y) = true) : O.eq (O.pow X e) Y = true := by
  have m := pow_enc CertificateChecks.KernelSporSch.J4Real.hK hX e
  exact slpB_eq m.1 hY (by rw [m.2]; exact h)

theorem cE_parts : rowsOK cEr = true ∧ Nat.beq CE CertificateChecks.KernelJ4M2.cK = true ∧
    Nat.beq (mulJ c rm CE (mulJ c rm CE CE)) one = true := by
  have h := c12611cE
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem wfN_cE : WfN cEr := wfN_of cE_parts.1

theorem cEOK_ok : cEOK = true := by
  have hw := wfN_cE
  have hn := CertificateChecks.KernelJ4M2.natRows_enc cEr cE_parts.1
  have e1 : CertificateChecks.KernelJ4M2.encN cEr = CertificateChecks.KernelJ4M2.cK := by
    have e : CertificateChecks.KernelJ4M2.encN cEr = pk cEr := by
      unfold CertificateChecks.KernelJ4M2.encN pk
      congr 1
      funext i acc
      simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
    rw [e]
    exact Nat.eq_of_beq_eq_true cE_parts.2.1
  have hz : CFSG.Quasithin.J4M2.cMat = cEr.map natV2 :=
    CFSG.Sporadic.J4.eqRows_iff.1 (by
      rw [eqRows_eq CertificateChecks.KernelJ4M2.cMat_encK.1 hn.1,
        CertificateChecks.KernelJ4M2.cMat_encK.2, hn.2, e1]
      exact Nat.beq_refl _)
  have m := CFSG.KS.SporSch.J4B.mul_enc CertificateChecks.KernelSporSch.J4Real.hK hw hw
  have h3 : O.eq (O.mul cEr (O.mul cEr cEr)) O.one = true :=
    eq_one_sound CertificateChecks.KernelSporSch.J4Real.hK hw m.1 (by rw [m.2]; exact cE_parts.2.2)
  unfold cEOK
  rw [hz, Array.size_map, hw.1, h3]
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_true, List.all_eq_true]
  intro i hi
  rw [CertificateChecks.KernelJ4M2.get!_map natV2 cEr (by rw [hw.1]; exact List.mem_range.1 hi)]
  exact CFSG.Sporadic.J4.Native.V2.beq_iff.2 rfl

end CertificateChecks.KernelJ4Gam

end
