module

public import Certificates.Kernel.Sporadic.Co1Row26683.GlueD
public import Certificates.Kernel.Sporadic.Co1Row26683.GlueM
public import Certificates.Kernel.Sporadic.Co1Row26683.ChecksS

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.Co1Row26683

open CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier CFSG.KS.Co1Row26683 CFSG.KS.Raw.Orb
  CertificateChecks.KernelCo1B.Tri2045 CertificateChecks.KernelSpor

theorem chG_of {k : Nat} (h : ch26683G k = true) :
    genSl (TB.P (nat_lit 10)) (TB.P (nat_lit 11)) (TB.PI (nat_lit 10)) (TB.PI (nat_lit 11)) G
      C26683.WS (Nat.shiftRight k (nat_lit 2)) (Nat.land k (nat_lit 3)) = true := by
  simp only [ch26683G, withXY, CFSG.KC.Pack.strictB_eq] at h
  exact h

theorem chG_all : ∀ k < 16, ch26683G k = true := by
  intro k hk
  interval_cases k
  exacts [ch26683G0, ch26683G1, ch26683G2, ch26683G3, ch26683G4, ch26683G5, ch26683G6, ch26683G7,
    ch26683G8, ch26683G9, ch26683G10, ch26683G11, ch26683G12, ch26683G13, ch26683G14, ch26683G15]

theorem chS_all' : ∀ s < 16, ch26683S s = true := by
  intro s hs
  interval_cases s
  exacts [ch26683S0, ch26683S1, ch26683S2, ch26683S3, ch26683S4, ch26683S5, ch26683S6, ch26683S7,
    ch26683S8, ch26683S9, ch26683S10, ch26683S11, ch26683S12, ch26683S13, ch26683S14, ch26683S15]

theorem chS_all : ∀ n < 4096, nodeK G C26683.RP C26683.QP C26683.QIP C26683.NC n = true ∧
    ordK C26683.RP C26683.NOP n = true := by
  intro n hn
  have h := sSl_sound (chS_all' (n / 256) (by omega)) (n % 256) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul 256 (n / 256)) (n % 256) = n := Nat.div_add_mod n 256
  rw [e] at h
  exact h

theorem base_parts : (∀ b < 3, lane C26683.QP b = b) ∧
    (∀ j < 4, ∀ b < 3, qi C26683.QIP j b < 13 ∧ lane C26683.QP (qi C26683.QIP j b) = ap (G j) b) ∧
    ∀ k < 4, ncOne C26683.RP C26683.ZQ (nthN C26683.NC k) (nthN C26683.NCW k) = true :=
  baseK_sound ch26683B

theorem nc_eq : C26683.NC = [0, 12, 16, 107] := by rfl

theorem ncw_eq : C26683.NCW = [0, 1, 3, 2] := by rfl

theorem nc1 : nthN C26683.NC 1 = 12 := by rw [nc_eq]; rfl
theorem nc2 : nthN C26683.NC 2 = 16 := by rw [nc_eq]; rfl
theorem nc3 : nthN C26683.NC 3 = 107 := by rw [nc_eq]; rfl
theorem ncw1 : nthN C26683.NCW 1 = 1 := by rw [ncw_eq]; rfl
theorem ncw2 : nthN C26683.NCW 2 = 3 := by rw [ncw_eq]; rfl
theorem ncw3 : nthN C26683.NCW 3 = 2 := by rw [ncw_eq]; rfl


theorem xBar_mem : xBar ∈ twoBD := Subgroup.subset_closure (Set.mem_insert _ _)

theorem yBar_mem : yBar ∈ twoBD := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

abbrev gS (j : Nat) : Equiv.Perm (Fin 1365) := wP xBar yBar (nthW C26683.WS j)

theorem gS_mem (j : Nat) : gS j ∈ twoBD := wP_mem xBar_mem yBar_mem _

theorem G_prep {j : Nat} (hj : j < 4) : PRep 1365 11 (G j) (gS j) := by
  intro q
  have hq := q.2
  have hk : 4 * j + q / 342 < 16 := by omega
  have h := genSl_sound (chG_of (chG_all _ hk)) (q % 342) (Nat.mod_lt _ (by norm_num))
  have e1 : Nat.shiftRight (4 * j + q / 342) (nat_lit 2) = j := by
    change (4 * j + q / 342) >>> 2 = j
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have e2 : Nat.land (4 * j + q / 342) (nat_lit 3) = q / 342 := by
    change (4 * j + q / 342) &&& (2 ^ 2 - 1) = _
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have e3 : Nat.add (Nat.mul 342 (q / 342)) (q % 342) = q := Nat.div_add_mod q 342
  rw [e1, e2, e3] at h
  have h' := h hq
  rw [mask11]
  exact h'.trans (wv_eq prep_x prep_y prep_xi prep_yi _ q)

abbrev Sg : Subgroup (Equiv.Perm (Fin 1365)) := Subgroup.closure (Set.range fun j : Fin 4 => gS j)

theorem gen_memS {j : Nat} (hj : j < 4) : gS j ∈ Sg := Subgroup.subset_closure ⟨⟨j, hj⟩, rfl⟩

theorem Sg_le : Sg ≤ twoBD := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact gS_mem j

theorem node_exists : ∀ n < 4096, ∃ s ∈ Sg, ∀ i < 13, ∀ hq : lane C26683.QP i < 1365,
    (s ⟨_, hq⟩ : Nat) = lane (nrec C26683.RP n) i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  obtain ⟨h1, -, -⟩ := nodeK_sound (chS_all n hn).1
  obtain ⟨h0, hs⟩ := treeK_sound h1
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact ⟨1, Sg.one_mem, fun i hi hq => by rw [h0 rfl i hi]; rfl⟩
  · obtain ⟨p, g, hp, hg, hl⟩ := hs (by omega)
    obtain ⟨s, hsS, hsl⟩ := ih p hp (by omega)
    refine ⟨gS g * s, Sg.mul_mem (gen_memS hg) hsS, fun i hi hq => ?_⟩
    rw [hl i hi, ← hsl i hi hq, Equiv.Perm.mul_apply]
    exact (ap_prep (G_prep hg) _).symm

@[expose] def sN (n : Nat) : Equiv.Perm (Fin 1365) :=
  if h : n < 4096 then Classical.choose (node_exists n h) else 1

theorem sN_spec {n : Nat} (h : n < 4096) : sN n ∈ Sg ∧ ∀ i < 13, ∀ hq : lane C26683.QP i < 1365,
    (sN n ⟨_, hq⟩ : Nat) = lane (nrec C26683.RP n) i := by
  rw [sN, dif_pos h]
  exact Classical.choose_spec (node_exists n h)

theorem sN_D {n : Nat} (h : n < 4096) : sN n ∈ twoBD := Sg_le (sN_spec h).1

theorem sN_base {n : Nat} (h : n < 4096) {b : Nat} (hb : b < 3) :
    (sN n ⟨b, by omega⟩ : Nat) = lane (nrec C26683.RP n) b := by
  have e := base_parts.1 b hb
  have hq : lane C26683.QP b < 1365 := by rw [e]; omega
  have h2 := (sN_spec h).2 b (by omega) hq
  have e' : (⟨lane C26683.QP b, hq⟩ : Fin 1365) = ⟨b, by omega⟩ := Fin.ext e
  rw [e'] at h2
  exact h2

theorem eqD {g h : Equiv.Perm (Fin 1365)} (hg : g ∈ twoBD) (hh : h ∈ twoBD)
    (e : ∀ b (hb : b < 3), (g ⟨b, by omega⟩ : Nat) = h ⟨b, by omega⟩) : g = h :=
  twoBD_eq_of_base hg hh (Fin.ext (e 0 (by norm_num))) (Fin.ext (e 1 (by norm_num)))
    (Fin.ext (e 2 (by norm_num)))

theorem sN_zero : sN 0 = 1 := by
  refine eqD (sN_D (by norm_num)) (Subgroup.one_mem _) fun b hb => ?_
  obtain ⟨h1, -, -⟩ := nodeK_sound (chS_all 0 (by norm_num)).1
  rw [sN_base (by norm_num) hb, (treeK_sound h1).1 rfl b (by omega), base_parts.1 b hb]
  rfl

theorem sN_step {n j : Nat} (hn : n < 4096) (hj : j < 4) : ∃ m < 4096, sN m = gS j * sN n := by
  obtain ⟨-, h2, -⟩ := nodeK_sound (chS_all n hn).1
  obtain ⟨m, hm, hl⟩ := closK_sound h2 j hj
  refine ⟨m, hm, eqD (sN_D hm) (Subgroup.mul_mem _ (gS_mem j) (sN_D hn)) fun b hb => ?_⟩
  rw [sN_base hm hb, hl b hb, ← sN_base hn hb, Equiv.Perm.mul_apply]
  exact ap_prep (G_prep hj) _

theorem sN_pow {n j : Nat} (hn : n < 4096) (hj : j < 4) :
    ∀ k : Nat, ∃ m < 4096, sN m = gS j ^ k * sN n
  | 0 => ⟨n, hn, by rw [pow_zero, one_mul]⟩
  | k + 1 => by
    obtain ⟨m, hm, e⟩ := sN_pow hn hj k
    obtain ⟨m', hm', e'⟩ := sN_step hm hj
    exact ⟨m', hm', by rw [e', e, pow_succ', mul_assoc]⟩

theorem mem_nodes {x : Equiv.Perm (Fin 1365)} (hx : x ∈ Sg) : ∃ n < 4096, sN n = x := by
  refine Subgroup.closure_induction_left (p := fun x _ => ∃ n < 4096, sN n = x) ?_ ?_ ?_ hx
  · exact ⟨0, by norm_num, sN_zero⟩
  · rintro _ ⟨j, rfl⟩ y - ⟨n, hn, rfl⟩
    exact sN_step hn j.2
  · rintro _ ⟨j, rfl⟩ y - ⟨n, hn, rfl⟩
    have hpos : 0 < orderOf (gS j) := orderOf_pos _
    obtain ⟨m, hm, e⟩ := sN_pow hn j.2 (orderOf (gS j) - 1)
    refine ⟨m, hm, ?_⟩
    rw [e]
    congr 1
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]

theorem ord_parts {i : Nat} (hi : i < 4096) : noA C26683.NOP i < 4096 ∧
    (i ≠ 0 → key (nrec C26683.RP (noA C26683.NOP (i - 1))) <
      key (nrec C26683.RP (noA C26683.NOP i))) :=
  ordK_sound (chS_all i hi).2

theorem key_mono : ∀ {i i' : Nat}, i < i' → i' < 4096 →
    key (nrec C26683.RP (noA C26683.NOP i)) < key (nrec C26683.RP (noA C26683.NOP i'))
  | _, 0, h, _ => absurd h (Nat.not_lt_zero _)
  | i, i' + 1, h, h' => by
    have h2 := (ord_parts h').2 (by omega)
    rw [Nat.add_sub_cancel] at h2
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h3 | rfl
    · exact (key_mono h3 (by omega)).trans h2
    · exact h2

theorem key_eq_of {n m : Nat} (hn : n < 4096) (hm : m < 4096) (e : sN n = sN m) :
    key (nrec C26683.RP n) = key (nrec C26683.RP m) := by
  have h : ∀ b (hb : b < 3), lane (nrec C26683.RP n) b = lane (nrec C26683.RP m) b :=
    fun b hb => by rw [← sN_base hn hb, ← sN_base hm hb, e]
  unfold key
  rw [h (nat_lit 0) (by decide), h (nat_lit 1) (by decide), h (nat_lit 2) (by decide)]

theorem noA_surj : ∀ n < 4096, ∃ i < 4096, noA C26683.NOP i = n := by
  have hinj : Set.InjOn (noA C26683.NOP) (Finset.range 4096 : Set Nat) := by
    intro i hi i' hi' e
    simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact absurd (congrArg (fun a => key (nrec C26683.RP a)) e) (key_mono h hi').ne
    · exact absurd (congrArg (fun a => key (nrec C26683.RP a)) e).symm (key_mono h hi).ne
  have hsub : (Finset.range 4096).image (noA C26683.NOP) ⊆ Finset.range 4096 := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 ha
    exact Finset.mem_range.2 (ord_parts (Finset.mem_range.1 hi)).1
  have heq := Finset.eq_of_subset_of_card_le hsub (Finset.card_image_of_injOn hinj).ge
  intro n hn
  have : n ∈ (Finset.range 4096).image (noA C26683.NOP) := by
    rw [heq]
    exact Finset.mem_range.2 hn
  obtain ⟨i, hi, e⟩ := Finset.mem_image.1 this
  exact ⟨i, Finset.mem_range.1 hi, e⟩

theorem sN_inj {n m : Nat} (hn : n < 4096) (hm : m < 4096) (e : sN n = sN m) : n = m := by
  obtain ⟨i, hi, rfl⟩ := noA_surj n hn
  obtain ⟨i', hi', rfl⟩ := noA_surj m hm
  have hk := key_eq_of hn hm e
  by_contra hne
  have hne' : i ≠ i' := fun h => hne (by rw [h])
  rcases Nat.lt_or_gt_of_ne hne' with h | h
  · exact absurd hk (key_mono h hi').ne
  · exact absurd hk.symm (key_mono h hi).ne

theorem card_Sg : Nat.card Sg = 4096 := by
  have hset : (Sg : Set (Equiv.Perm (Fin 1365))) = ↑((Finset.range 4096).image sN) := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn, rfl⟩ := mem_nodes hx
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, Finset.mem_range.2 hn, rfl⟩)
    · intro hx
      obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      exact (sN_spec (Finset.mem_range.1 hn)).1
  have e : Nat.card Sg = Nat.card (Sg : Set (Equiv.Perm (Fin 1365))) := rfl
  rw [e, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    Finset.card_image_of_injOn fun n hn m hm e => sN_inj (Finset.mem_range.1 hn)
      (Finset.mem_range.1 hm) e, Finset.card_range]

theorem sN_comm_iff {n : Nat} (hn : n < 4096) :
    (∀ j < 4, gS j * sN n = sN n * gS j) ↔ n ∈ C26683.NC := by
  obtain ⟨-, -, hc⟩ := nodeK_sound (chS_all n hn).1
  rw [← inL_iff, ← hc, commK_iff]
  have key : ∀ j < 4, ∀ b (hb : b < 3), ap (G j) (lane (nrec C26683.RP n) b) =
      (gS j * sN n) ⟨b, by omega⟩ := by
    intro j hj b hb
    rw [← sN_base hn hb, Equiv.Perm.mul_apply]
    exact ap_prep (G_prep hj) _
  have key2 : ∀ j < 4, ∀ b (hb : b < 3), lane (nrec C26683.RP n) (qi C26683.QIP j b) =
      (sN n * gS j) ⟨b, by omega⟩ := by
    intro j hj b hb
    obtain ⟨h1, h2⟩ := base_parts.2.1 j hj b hb
    have hap : ap (G j) b = (gS j ⟨b, by omega⟩ : Nat) := ap_prep (G_prep hj) ⟨b, by omega⟩
    have hq : lane C26683.QP (qi C26683.QIP j b) < 1365 := by
      rw [h2, hap]
      exact Fin.isLt _
    rw [← (sN_spec hn).2 _ h1 hq, Equiv.Perm.mul_apply]
    congr 2
    exact Fin.ext (h2.trans hap)
  constructor
  · intro h j hj b hb
    rw [key j hj b hb, key2 j hj b hb, h j hj]
  · intro h j hj
    refine eqD (Subgroup.mul_mem _ (gS_mem j) (sN_D hn)) (Subgroup.mul_mem _ (sN_D hn) (gS_mem j))
      fun b hb => ?_
    rw [← key j hj b hb, ← key2 j hj b hb, h j hj b hb]

variable {ζ : Equiv.Perm (Fin 1365)}

abbrev cW (i : Nat) : Equiv.Perm (Fin 1365) := wP xBar yBar (nthW C26683.WC i)

theorem zq_parts (hζ : PRep 1365 11 C26683Z.PZ ζ) :
    (∀ b (hb : b < 3), nthN (nthW C26683.ZQ 0) b = ζ ⟨b, by omega⟩) ∧
      ∀ i < 2, ∀ b (hb : b < 3), nthN (nthW C26683.ZQ (i + 1)) b =
        (cW i * ζ * (cW i)⁻¹) ⟨b, by omega⟩ := by
  have h := ch26683Q
  simp only [withXY, CFSG.KC.Pack.strictB_eq] at h
  obtain ⟨h1, h2⟩ := CFSG.KS.Co1Row26683Z.zqK_sound h
  refine ⟨fun b hb => (h1 b hb).trans (ap_prep hζ ⟨b, by omega⟩), fun i hi b hb => ?_⟩
  have e1 : CFSG.KS.Co1Row26683Z.wvI (TB.P (nat_lit 10)) (TB.P (nat_lit 11)) (TB.PI (nat_lit 10))
      (TB.PI (nat_lit 11)) (nthW C26683.WC i) b = ((cW i)⁻¹ ⟨b, by omega⟩ : Nat) :=
    CFSG.KS.Co1Row26683Z.wvI_eq prep_x prep_y prep_xi prep_yi _ ⟨b, by omega⟩
  rw [h2 i hi b hb, e1, ap_prep hζ]
  exact wv_eq prep_x prep_y prep_xi prep_yi _ _

theorem nc_node {k : Nat} (hk : k < 4) : nthN C26683.NC k < 4096 ∧ ∀ b < 3,
    lane (nrec C26683.RP (nthN C26683.NC k)) b = nIf(Nat.beq (nthN C26683.NCW k) (nat_lit 0), b,
      nthN (nthW C26683.ZQ (Nat.sub (nthN C26683.NCW k) (nat_lit 1))) b) :=
  ncOne_sound (base_parts.2.2 k hk)

theorem sN_12 (hζ : PRep 1365 11 C26683Z.PZ ζ) (hζD : ζ ∈ twoBD) : sN 12 = ζ := by
  obtain ⟨-, h⟩ := nc_node (k := 1) (by norm_num)
  refine eqD (sN_D (by norm_num)) hζD fun b hb => ?_
  rw [sN_base (by norm_num) hb]
  have e := h b hb
  rw [nc1, ncw1] at e
  rw [e]
  exact (zq_parts hζ).1 b hb

theorem sN_16 (hζ : PRep 1365 11 C26683Z.PZ ζ) (hζD : ζ ∈ twoBD) :
    sN 16 = cW 1 * ζ * (cW 1)⁻¹ := by
  obtain ⟨-, h⟩ := nc_node (k := 2) (by norm_num)
  refine eqD (sN_D (by norm_num))
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (wP_mem xBar_mem yBar_mem _) hζD)
      (Subgroup.inv_mem _ (wP_mem xBar_mem yBar_mem _))) fun b hb => ?_
  rw [sN_base (by norm_num) hb]
  have e := h b hb
  rw [nc2, ncw2] at e
  rw [e]
  exact (zq_parts hζ).2 1 (by norm_num) b hb

theorem sN_107 (hζ : PRep 1365 11 C26683Z.PZ ζ) (hζD : ζ ∈ twoBD) :
    sN 107 = cW 0 * ζ * (cW 0)⁻¹ := by
  obtain ⟨-, h⟩ := nc_node (k := 3) (by norm_num)
  refine eqD (sN_D (by norm_num))
    (Subgroup.mul_mem _ (Subgroup.mul_mem _ (wP_mem xBar_mem yBar_mem _) hζD)
      (Subgroup.inv_mem _ (wP_mem xBar_mem yBar_mem _))) fun b hb => ?_
  rw [sN_base (by norm_num) hb]
  have e := h b hb
  rw [nc3, ncw3] at e
  rw [e]
  exact (zq_parts hζ).2 0 (by norm_num) b hb

theorem co1_d_K (hζ : PRep 1365 11 C26683Z.PZ ζ) (hζD : ζ ∈ twoBD) :
    ∃ S : Subgroup (Equiv.Perm (Fin 1365)), S ≤ twoBD ∧ Nat.card S = 4096 ∧
      (∀ x ∈ S, x * ζ = ζ * x) ∧
      ∀ x ∈ S, x * x = 1 → x ≠ 1 → (∀ s ∈ S, x * s = s * x) →
        ∃ c ∈ twoBD, c * ζ * c⁻¹ = x := by
  have hζc : ∀ j < 4, gS j * ζ = ζ * gS j := by
    rw [← sN_12 hζ hζD]
    exact (sN_comm_iff (by norm_num)).2 (by rw [nc_eq]; simp)
  refine ⟨Sg, Sg_le, card_Sg, fun x hx => ?_, fun x hx _ hx1 hxc => ?_⟩
  · have hle : Sg ≤ Subgroup.centralizer {ζ} := by
      rw [Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact hζc j j.2
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hx)
  · obtain ⟨n, hn, rfl⟩ := mem_nodes hx
    have hmem := (sN_comm_iff hn).1 fun j hj => (hxc _ (gen_memS hj)).symm
    rw [nc_eq] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact absurd sN_zero hx1
    · exact ⟨1, Subgroup.one_mem _, by rw [sN_12 hζ hζD]; group⟩
    · exact ⟨cW 1, wP_mem xBar_mem yBar_mem _, (sN_16 hζ hζD).symm⟩
    · exact ⟨cW 0, wP_mem xBar_mem yBar_mem _, (sN_107 hζ hζD).symm⟩

theorem zeta_mem : triHom (liftC zM zM_mem) ∈ twoBD := by
  set K : Subgroup C₁ := twoBD.comap triHom with hK
  have hy : yM ∈ K.map ιC := ⟨d₂C twoBXY.2, yBar_mem, rfl⟩
  have hb : bM ∈ K.map ιC := by
    refine ⟨d₂C twoBXY.1 * d₂C twoBXY.2 * d₂C twoBXY.1, ?_, rfl⟩
    change triHom (d₂C twoBXY.1 * d₂C twoBXY.2 * d₂C twoBXY.1) ∈ twoBD
    rw [map_mul, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ xBar_mem yBar_mem) xBar_mem
  have hle : Subgroup.closure {yM, bM} ≤ K.map ιC := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hy
    · exact hb
  obtain ⟨c, hc, e⟩ := hle zM_closure
  have : c = liftC zM zM_mem := ιC_injective (e.trans (ιC_liftC _ _).symm)
  rw [← this]
  exact hc

end CertificateChecks.KernelSpor.Co1Row26683

end
