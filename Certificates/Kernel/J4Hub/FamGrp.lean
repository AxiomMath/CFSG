module

public import Certificates.Kernel.J4Hub.Fam
public import Certificates.Kernel.J4.Bridge
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelJ4Hub

open CFSG.KC.Ord CFSG.KS.Ord CFSG.KS.J4Hub CFSG.Sporadic.J4 CFSG.Certificates CFSG.Certificates.J4R

@[expose] noncomputable def φJ : J →* Matrix (Fin 112) (Fin 112) (ZMod 2) :=
  (Units.coeHom _).comp J.subtype

theorem φJ_apply (g : J) :
    φJ g = ((g : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) := rfl

theorem φJ_injective : Function.Injective φJ := fun _ _ h => Subtype.ext (Units.ext h)

@[expose] noncomputable def X : J := feJ 22

@[expose] noncomputable def Y : J := feJ 26

@[expose] noncomputable def T : J := feJ 35

@[expose] noncomputable def gen (g : ℕ) : J := if g = 0 then X else if g = 1 then Y else T

@[expose] noncomputable def letJ (x : ℕ × Bool) : J := if x.2 then gen x.1 else (gen x.1)⁻¹

theorem gr0 : at16 GRxyt 0 = 22 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem gr1 : at16 GRxyt 1 = 26 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem gr2 : at16 GRxyt 2 = 35 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem ir0 : at16 IRxyt 0 = 36 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem ir1 : at16 IRxyt 1 = 37 := Nat.eq_of_beq_eq_true (by quickRfl)
theorem ir2 : at16 IRxyt 2 = 38 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem gen_reg {g : ℕ} (hg : g < 3) : gen g = feJ (at16 GRxyt g) := by
  obtain rfl | rfl | rfl : g = 0 ∨ g = 1 ∨ g = 2 := by omega
  · simp [gen, X, gr0]
  · simp [gen, Y, gr1]
  · simp [gen, T, gr2]

theorem gr_lt {g : ℕ} (hg : g < 3) : 0 < at16 GRxyt g ∧ at16 GRxyt g < 239 := by
  obtain rfl | rfl | rfl : g = 0 ∨ g = 1 ∨ g = 2 := by omega
  · rw [gr0]; omega
  · rw [gr1]; omega
  · rw [gr2]; omega

theorem ir_lt {g : ℕ} (hg : g < 3) : 0 < at16 IRxyt g ∧ at16 IRxyt g < 239 := by
  obtain rfl | rfl | rfl : g = 0 ∨ g = 1 ∨ g = 2 := by omega
  · rw [ir0]; omega
  · rw [ir1]; omega
  · rw [ir2]; omega

theorem inv_pairs {g : ℕ} (hg : g < 3) :
    FM (CFSG.KD.FamJ4.RW (at16 GRxyt g)) * FM (CFSG.KD.FamJ4.RW (at16 IRxyt g)) = 1 :=
  ((invPairs_sound' (hnb := rfl) CFSG.KD.FamJ4.consts CFSG.KD.FamJ4.rinv) g hg).2.2.2.2
    (fe_spec (gr_lt hg).1 (gr_lt hg).2).2.2 (fe_spec (ir_lt hg).1 (ir_lt hg).2).2.2

theorem letJ_val {x : ℕ × Bool} (hx : x.1 < 3) :
    φJ (letJ x) = FM (CFSG.KC.Fam.letL CFSG.KD.FamJ4.RW GRxyt IRxyt x) := by
  obtain ⟨g, s⟩ := x
  have hg : g < 3 := hx
  have hv := feJ_val (gr_lt hg).1 (gr_lt hg).2
  cases s
  · change φJ ((gen g)⁻¹) = FM (CFSG.KD.FamJ4.RW (at16 IRxyt g))
    rw [φJ_apply, InvMemClass.coe_inv, Matrix.coe_units_inv, gen_reg hg, hv]
    exact Matrix.inv_eq_right_inv (inv_pairs hg)
  · change φJ (gen g) = FM (CFSG.KD.FamJ4.RW (at16 GRxyt g))
    rw [gen_reg hg, φJ_apply, hv]

theorem letL_valid {x : ℕ × Bool} (hx : x.1 < 3) :
    FV (CFSG.KC.Fam.letL CFSG.KD.FamJ4.RW GRxyt IRxyt x) = true := by
  obtain ⟨g, s⟩ := x
  have hg : g < 3 := hx
  cases s
  · exact (fe_spec (ir_lt hg).1 (ir_lt hg).2).2.2
  · exact (fe_spec (gr_lt hg).1 (gr_lt hg).2).2.2

theorem word_val {l : List (ℕ × Bool)} (hl : ∀ x ∈ l, x.1 < 3) :
    φJ (l.map letJ).prod =
      FM (CFSG.KC.Fam.wordProd CFSG.KD.FamJ4.RW FMUL CFSG.KD.FamJ4.ONE GRxyt IRxyt l CFSG.KD.FamJ4.ONE) := by
  refine Eq.trans ?_ (wordProd_sound' (hnb := rfl) CFSG.KD.FamJ4.consts
    fun x hx => letL_valid (hl x hx)).2.symm
  rw [map_list_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun x hx => letJ_val (hl x hx)

theorem word_eq_feJ {l : List (ℕ × Bool)} (hl : ∀ x ∈ l, x.1 < 3) {r : ℕ} (h0 : 0 < r) (h1 : r < 239)
    (h : Nat.beq (CFSG.KC.Fam.wordProd CFSG.KD.FamJ4.RW FMUL CFSG.KD.FamJ4.ONE GRxyt IRxyt l
      CFSG.KD.FamJ4.ONE) (CFSG.KD.FamJ4.RW r) = true) : (l.map letJ).prod = feJ r := by
  apply φJ_injective
  rw [word_val hl, Nat.eq_of_beq_eq_true h, φJ_apply, feJ_val h0 h1]

theorem nthRel_eq : ∀ (l : List (List (ℕ × Bool))) (k : ℕ) (hk : k < l.length),
    nthRel l k = l[k]
  | [], _, hk => absurd hk (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | _ :: l, k + 1, hk => nthRel_eq l k (by simpa using hk)

theorem fam_rels_eq : CertificateChecks.KernelBounds.J4.rels = CFSG.KD.FamJ4.rels :=
  CertificateChecks.KernelBounds.J4.rels_eq.symm.trans CFSG.KD.FamJ4.rels_eq

theorem fam_rels_len : CFSG.KD.FamJ4.rels.length = 12 := by
  rw [← fam_rels_eq]
  rfl

theorem rel_holds {r : ℕ} (hr : r < 12)
    (h : CFSG.KC.Fam.relOKL CFSG.KD.FamJ4.RW FMUL CFSG.KD.FamJ4.rels CFSG.KD.FamJ4.ONE GRxyt IRxyt r =
      true) : ((CFSG.KD.FamJ4.rels[r]'(by rw [fam_rels_len]; exact hr)).map letJ).prod = 1 := by
  have hl : ∀ x ∈ CFSG.KD.FamJ4.rels[r]'(by rw [fam_rels_len]; exact hr), x.1 < 3 := by
    have := CertificateChecks.KernelBounds.rels_lt r hr
    simpa [fam_rels_eq] using this
  apply φJ_injective
  rw [word_val hl, map_one]
  have h2 := (andB_true h).2
  rw [nthRel_eq _ _ (by rw [fam_rels_len]; exact hr)] at h2
  rw [Nat.eq_of_beq_eq_true h2]
  exact (one_sound' (hnb := rfl) CFSG.KD.FamJ4.consts).2

open CFSG.KD.FamJ4 in
theorem rels_XYT : ∀ w ∈ CertificateChecks.KernelBounds.J4.rels, KB.sword gen w = 1 := by
  intro w hw
  rw [fam_rels_eq] at hw
  obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hw
  rw [fam_rels_len] at hr
  change ((CFSG.KD.FamJ4.rels[r]).map letJ).prod = 1
  exact rel_holds hr (R.all r hr)

theorem T_inv : T⁻¹ = T := by
  have h7 := rels_XYT (CertificateChecks.KernelBounds.J4.rels[7]) (List.getElem_mem _)
  simp only [CertificateChecks.KernelBounds.J4.rels, List.getElem_cons_succ, List.getElem_cons_zero,
    KB.sword, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, ite_true, mul_one, gen] at h7
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one] at h7
  exact inv_eq_of_mul_eq_one_right h7

open CertificateChecks.KernelBounds CertificateChecks.KernelBounds.J4 CFSG.KJ4 CFSG.KJ4.R CFSG.KJ4.S in
theorem hR_XYT : ∀ r < 12, wval (lets X Y T) (wW (CFSG.KJ4.RUN.kd.RT r)) (wN (CFSG.KJ4.RUN.kd.RT r)) = 1 := by
  intro r hr
  change wval _ (wW (CFSG.KJ4.KRS.RT r)) (wN (CFSG.KJ4.KRS.RT r)) = 1
  rw [wval_rt _ _ _ T_inv r hr]
  have hw := rels_XYT _ (List.getElem_mem (by simpa [rels] using hr))
  rw [← hw, KB.sword, KB.sword]
  rfl

theorem zList_lt : ∀ x ∈ zList, x.1 < 3 := by decide
theorem apList_lt : ∀ x ∈ apList, x.1 < 3 := by decide
theorem bpList_lt : ∀ x ∈ bpList, x.1 < 3 := by decide

theorem Z_eq : zElt X Y T = feJ 47 := by
  rw [← word_eq_feJ zList_lt (by norm_num) (by norm_num) z_word]
  simp only [zElt, dElt, pow_succ, pow_zero, one_mul, mul_inv_rev, inv_inv, zList, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, letJ, gen]
  simp only [↓reduceIte, Bool.false_eq_true, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, one_ne_zero]
  group

theorem ap_val : (apList.map letJ).prod = feJ 206 := word_eq_feJ apList_lt (by norm_num) (by norm_num) ap_word

theorem bp_val : (bpList.map letJ).prod = feJ 238 := word_eq_feJ bpList_lt (by norm_num) (by norm_num) bp_word

end CertificateChecks.KernelJ4Hub

end
