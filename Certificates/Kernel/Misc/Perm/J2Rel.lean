module

public import Certificates.Kernel.Misc.Perm.J2Fam
public import CFSG.Certificates.Kernel.Misc.ArrEnumOps
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check45Inputs
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelMisc.J2Fam

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
open CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Monster.B.Mathieu
open CertificateChecks.KernelMisc.J2C3 (hw cm I hI pI)

@[expose] noncomputable def iv (p : ℕ) : ℕ := pinvS 315 9 (mask 9) p

@[expose] noncomputable def pw (p e : ℕ) : ℕ := ppow 315 9 (mask 9) (pidn 315 9) p e

@[expose] def R (a : Array ℕ) (p : ℕ) : Prop := a = unpack 315 9 p ∧ permB 315 9 p = true

variable {a b t : Array ℕ} {p q r : ℕ}

theorem R.id : R (idA 315) I := ⟨hI.symm, pI⟩

theorem R.comp (ha : R a p) (hb : R b q) : R (compA 315 a b) (cm p q) :=
  ⟨by rw [ha.1, hb.1, comp_unpack hw ha.2 hb.2]; rfl, permB_pcomp hw ha.2 hb.2⟩

theorem R.inv (ha : R a p) : R (invCand 315 a) (iv p) :=
  ⟨by rw [ha.1, inv_unpack hw ha.2]; rfl, permB_pinvS hw ha.2⟩

theorem R.conj (ha : R a p) (hb : R b q) : R (conjA 315 a b) (cm p (cm q (iv p))) :=
  ha.comp (hb.comp ha.inv)

theorem R.conjInv (ha : R a p) (hb : R b q) : R (conjInvA 315 a b) (cm (iv p) (cm q p)) :=
  ha.inv.comp (hb.comp ha)

theorem R.pow (ha : R a p) (e : ℕ) : R (powArr 315 a e) (pw p e) :=
  ⟨by rw [ha.1, pow_unpack hw ha.2]; rfl, permB_ppow hw ha.2 e⟩

theorem R.eq (ha : R a p) (hb : R b q) : eqA 315 a b = Nat.beq p q := by
  rw [ha.1, hb.1, eqA_unpack hw ha.2 hb.2]

theorem R.commA (ha : R a p) (hb : R b q) :
    CFSG.ComponentClassification.J2Cover.commA a b = Nat.beq (cm p q) (cm q p) :=
  (ha.comp hb).eq (hb.comp ha)

theorem R.valid (ha : R a p) : validA 315 a = true := by
  rw [ha.1]
  exact CFSG.KC.BfsPin.validA_unpack ha.2

theorem R.ok (ha : R a p) (hz : Nat.beq (Nat.shiftRight p (315 * 9)) 0 = true)
    (hs : siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) J2M5.C.LR J2M5.C.TRI J2M5.C.BP 3 0 p = true) :
    okA a = true :=
  J2M5.okA_of ha.1 ha.2 hz hs

theorem R.foldl {gs : Array (Array ℕ)} {G : ℕ → ℕ} {m : ℕ} (hg : ∀ l < m, R gs[l]! (G l)) :
    ∀ (w : List ℕ), w.all (· < m) = true → ∀ {a p}, R a p →
      R (w.foldl (fun t l => compA 315 t gs[l]!) a) (w.foldl (fun p l => cm p (G l)) p)
  | [], _, _, _, ha => ha
  | l :: w, hw, _, _, ha => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    rw [List.foldl_cons, List.foldl_cons]
    exact R.foldl hg w hw.2 (ha.comp (hg l hw.1))

theorem R.foldr {gs : Array (Array ℕ)} {G : ℕ → ℕ} {m : ℕ} (hg : ∀ l < m, R gs[l]! (G l)) :
    ∀ (w : List ℕ), w.all (· < m) = true →
      R (w.foldr (fun l t => compA 315 gs[l]! t) (idA 315)) (w.foldr (fun l p => cm (G l) p) I)
  | [], _ => R.id
  | l :: w, hw => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    exact (hg l hw.1).comp (R.foldr hg w hw.2)

theorem R.arr4 {a0 a1 a2 a3 : Array ℕ} {p0 p1 p2 p3 : ℕ} (h0 : R a0 p0) (h1 : R a1 p1)
    (h2 : R a2 p2) (h3 : R a3 p3) : ∀ l < 4, R #[a0, a1, a2, a3][l]! ([p0, p1, p2, p3].getD l 0) := by
  intro l hl
  interval_cases l
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem R.arr6 {a0 a1 a2 a3 a4 a5 : Array ℕ} {p0 p1 p2 p3 p4 p5 : ℕ} (h0 : R a0 p0)
    (h1 : R a1 p1) (h2 : R a2 p2) (h3 : R a3 p3) (h4 : R a4 p4) (h5 : R a5 p5) :
    ∀ l < 6, R #[a0, a1, a2, a3, a4, a5][l]! ([p0, p1, p2, p3, p4, p5].getD l 0) := by
  intro l hl
  interval_cases l
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5

theorem rX : R xArr J2C3.X := ⟨J2C3.hx, J2C3.pX⟩
theorem rY : R yArr J2C3.Y := ⟨J2C3.hy, J2C3.pY⟩
theorem rZ : R zArr J2C3.Z := ⟨J2C3.hz, J2C3.pZ⟩
theorem rV1 : R v1Arr V1 := ⟨hv1, pV1⟩
theorem rV2 : R v2Arr V2 := ⟨hv2, pV2⟩
theorem rAB {k : ℕ} (hk : k < 2) : R autStrong[k]! (J2C3.AB k) :=
  ⟨J2C3.hab k hk, by interval_cases k <;> quickRfl⟩
theorem rCC {k : ℕ} (hk : k < 3) : R cConj[k]! (CC k) := ⟨hcc k hk, pCC k hk⟩
theorem rWG {k : ℕ} (hk : k < 6) : R wGens[k]! (WG k) := ⟨hwg k hk, pWG k hk⟩

theorem rwg {i j : ℕ} (h : 2 * i + j < 6) : R (wg i j) (WG (2 * i + j)) := rWG h

@[expose] noncomputable def VK (k i : ℕ) : ℕ :=
  cm (CC k) (cm (if i = 1 then V1 else V2) (iv (CC k)))

theorem rVK {k : ℕ} (hk : k < 3) (i : ℕ) : R (vkArr k i) (VK k i) := by
  unfold vkArr VK
  split_ifs
  · exact (rCC hk).conj rV1
  · exact (rCC hk).conj rV2

@[expose] noncomputable def VG (l : ℕ) : ℕ :=
  [VK 0 1, VK 0 2, VK 1 1, VK 1 2, VK 2 1, VK 2 2].getD l 0

theorem R.vk6 : ∀ l < 6,
    R #[vkArr 0 1, vkArr 0 2, vkArr 1 1, vkArr 1 2, vkArr 2 1, vkArr 2 2][l]! (VG l) :=
  R.arr6 (rVK (k := 0) (by norm_num) 1) (rVK (k := 0) (by norm_num) 2)
    (rVK (k := 1) (by norm_num) 1) (rVK (k := 1) (by norm_num) 2)
    (rVK (k := 2) (by norm_num) 1) (rVK (k := 2) (by norm_num) 2)

theorem rwg0 {i : ℕ} (hi : i < 3) : R (wg i 0) (WG (2 * i)) := rWG (by omega)
theorem rwg1 {i : ℕ} (hi : i < 3) : R (wg i 1) (WG (2 * i + 1)) := rWG (by omega)

@[expose] noncomputable def GWV (i l : ℕ) : ℕ :=
  [WG (2 * i), WG (2 * i + 1), VK ((i + 2) % 3) 1, VK ((i + 2) % 3) 2].getD l 0

theorem R.wv {i : ℕ} (hi : i < 3) : ∀ l < 4,
    R #[wg i 0, wg i 1, vkArr ((i + 2) % 3) 1, vkArr ((i + 2) % 3) 2][l]! (GWV i l) :=
  R.arr4 (rwg0 hi) (rwg1 hi) (rVK (Nat.mod_lt _ (by norm_num)) 1)
    (rVK (Nat.mod_lt _ (by norm_num)) 2)

@[expose] noncomputable def memE0K (r : ℕ) : Bool :=
  (List.range 3).any fun e => (List.range 3).any fun c =>
    Nat.beq r (cm (pw J2C3.Z e) (pw J2C3.X c))

@[expose] noncomputable def memWK (i r : ℕ) : Bool :=
  Nat.beq r I || (Nat.beq r (WG (2 * i)) || (Nat.beq r (WG (2 * i + 1)) ||
    Nat.beq r (cm (WG (2 * i)) (WG (2 * i + 1)))))

@[expose] noncomputable def memVK (r : ℕ) : Bool :=
  Nat.beq r I || Nat.beq r V1 || Nat.beq r V2 || Nat.beq r (cm V1 V2)

@[expose] noncomputable def memVkK (k r : ℕ) : Bool := memVK (cm (iv (CC k)) (cm r (CC k)))

theorem R.memE0 (ht : R t r) : inE 0 t = memE0K r := by
  unfold inE memE0K
  congr 1
  funext e
  congr 1
  funext c
  exact ht.eq ((rZ.pow e).comp (rX.pow c))

theorem R.memW {i : ℕ} (hi : i < 3) (ht : R t r) : inW i t = memWK i r := by
  have h0 : R (wg i 0) (WG (2 * i)) := rwg (by omega)
  have h1 : R (wg i 1) (WG (2 * i + 1)) := rwg (by omega)
  unfold inW wElts memWK
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  rw [ht.eq R.id, ht.eq h0, ht.eq h1, ht.eq (h0.comp h1)]

theorem R.memV (ht : R t r) : inV t = memVK r := by
  unfold inV memVK
  rw [ht.eq R.id, ht.eq rV1, ht.eq rV2, ht.eq (rV1.comp rV2)]

theorem R.memVk {k : ℕ} (hk : k < 3) (ht : R t r) : inVk k t = memVkK k r := by
  unfold inVk memVkK
  exact ((rCC hk).conjInv ht).memV

end CertificateChecks.KernelMisc.J2Fam

end
